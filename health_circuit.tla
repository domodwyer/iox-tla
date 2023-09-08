This model validates the correctness of the IOx Router's lock-free (fast path) 
circuit breaker / health check primitive under multi-threaded execution.

A circuit breaker models the health state of an upstream, preventing requests to
(assumed) unhealthy upstreams. If enough requests to a healthy upstream return
an error, the circuit breaker transitions to "unhealthy" and further requests
are prevented. In order to detect recovery of an upstream, a limited number of
"probe" requests are allowed through per window of time (the "probe period") -
if enough of these probes succeed to pass the health criteria within the probe
period, the circuit transitions to the "healthy" state, and requests are allowed
to be dispatched again.

Periodically, under healthy conditions, the result counters are reset. This 
ensures a circuit can become unhealthy without having to observe a large number 
of errors to overcome a large number of previously successful requests (or vice 
versa).

This model validates that the circuit always eventually becomes healthy
(allowing requests) given a bounded number of upstream outages, and does not
deadlock or become "stuck" in an unhealthy state.

The per-thread atomic states, advancing independently an concurrently, are 
modelled as below:

     
                              Write Request
                                 Starts      ◀ ─ ─ ─ ─ ─ ─ ─ ─ ─
                                                                │
                                    │
                                    ▼                           │
                            ┌───────────────┐
         ┌────Yes───────────│  Is Healthy?  │                Abort
         │                  └───────────────┘
         │                          │                           │
         │                         No
         │                          │                           │
         │                          ▼
         │                  ┌───────────────┐                   │
         │                  │  Is Healthy?  │─ ─Yes─ ─ ─ ─ ─ ─ ─
         │                  └───────────────┘                   │
         │                          │
         │                         No                           │
         │                          │
         │                          ▼                           │
         │                  ┌───────────────┐
         │         ┌────────│  Can Probe?   │────────┐          │
         │         │        └───────────────┘        │
         │         │                │                │          │
         │         │                │                │
         │         ▼                ▼                ▼          │
         │ ┌ ─ ─ ─ ─ ─ ─ ─ ┐┌ ─ ─ ─ ─ ─ ─ ─ ┐┌ ─ ─ ─ ─ ─ ─ ─ ┐
         │   Start Probing      Probe in          Probing       │
         │ │    Window     ││Existing Window││   Complete    │ ─
         │  ─ ─ ─ ─ ─ ─ ─ ─  ─ ─ ─ ─ ─ ─ ─ ─  ─ ─ ─ ─ ─ ─ ─ ─
         │         │                │
         │         └────────────────┤
         │                          │
         │                          ▼
         │                  ┌───────────────┐
         └─────────────────▶│ Make Request  │
                            └───────────────┘
                                    │
                                    ▼
     
                              Record Result
     

For the purposes of this model, all requests to a healthy upstream succeed. The 
number of probe windows are bounded to limit the state space of the model, and 
only behaviours that do not reach the bound are validated as having a circuit 
that eventually becomes healthy.

--------------------------- MODULE health_circuit --------------------------

EXTENDS TLC, Integers

CONSTANTS 
    \* The set of threads concurrently interacting with the circuit breaker.
    Threads, 
    \* A model bound on the number of upstream outages.
    MaxOutages,
    \* A model bound on the number of probe resets that occur.
    MaxProbeResets,
    \* Number of probe requests to send
    NumProbes,
    \* Thread states
    T_ReadHealth,       \* Start of request - next read the circuit health
    T_ReadProbe_health, \* Unhealthy, read probe state - step 1: check health
    T_ReadProbe_probe,  \* Unhealthy, read probe state - step 2: probe candidate?
    T_MakeRequest       \* Submit the request to the upstream

VARIABLES 
    threads,
    outage_count, 
    upstream_healthy,
    counts,
    probes_started,
    probe_resets

vars == << 
    threads,
    outage_count, 
    upstream_healthy,
    counts,
    probes_started,
    probe_resets
>>

vars_upstream == << outage_count, upstream_healthy >>
vars_probes == << probes_started, probe_resets >>

SetThread(t, state) == threads' = [threads EXCEPT ![t] = state]
GetThread(t) == threads[t]

SetCounts(ok, err) == counts' = [ok |-> ok, err |-> err]
SetRequestOk == counts' = [counts EXCEPT !.ok = @ + 1]
SetRequestErr == counts' = [counts EXCEPT !.err = @ + 1]
RequestTotal == counts.ok + counts.err

\* Counter states that are derived from the request counts.
Counter_IsProbing == RequestTotal < NumProbes
Counter_IsHealthy == counts.ok > (counts.err + 1)

\* The CircuitBreaker::is_healthy() method composes the above counter states.
Counter_IsHealthy_Check == ~Counter_IsProbing /\ Counter_IsHealthy

----------------------------------------------------------------------------

\* The upstream goes offline.
UpstreamGoesOffline == 
    /\ upstream_healthy = TRUE
    /\ outage_count < MaxOutages
    /\ upstream_healthy' = FALSE
    /\ outage_count' = outage_count + 1
    /\ UNCHANGED << threads, counts, vars_probes >>

\* The upstream recovers.
UpstreamGoesOnline == 
    /\ ~upstream_healthy
    /\ upstream_healthy' = TRUE
    /\ UNCHANGED << threads, outage_count, counts, vars_probes >>

\* The start of a new probing window, during which time a limited number of
\* probes are allowed.
ProbeStart(t) == 
    /\ probe_resets < MaxProbeResets
    /\ probe_resets' = probe_resets + 1
    /\ probes_started' = 1
    /\ SetCounts(0, 0)
    /\ SetThread(t, T_MakeRequest)

\* Continue an existing probing window that has not yet sent all allowed probes.
ProbeContinue(t) == 
    /\ probes_started < NumProbes
    /\ probes_started' = probes_started + 1
    /\ SetThread(t, T_MakeRequest)

\* All the allowed probe requests have been sent for this window of time.
ProbeExhausted(t) == 
    /\ probes_started >= NumProbes
    /\ SetThread(t, T_ReadHealth) \* Abort write

\* Check if the upstream is healthy before using it.
\*
\* If the upstream is believed healthy, immediately jump to sending the request,
\* else evaluate the probing state.
ThreadReadHealth(t) ==
    /\ GetThread(t) = T_ReadHealth
    /\ SetThread(t, T_ReadProbe_health)
    /\ \/ Counter_IsHealthy_Check = TRUE  /\ SetThread(t, T_MakeRequest) \* Fast "healthy" path
       \/ Counter_IsHealthy_Check = FALSE /\ SetThread(t, T_ReadProbe_health)
    /\ UNCHANGED << vars_upstream, counts, vars_probes >>

\* The upstream was believed to be unhealthy when evaluating above (but both the
\* upstream and the circuit may no longer be unhealthy).
\*
\* If the circuit is now healthy, this request is aborted (potential future
\* optimisation to continue with the request).
\* 
\* If the circuit is unhealthy, read the probe state.
ThreadShouldProbe_health(t) == 
    /\ GetThread(t) = T_ReadProbe_health
    /\ SetThread(t, T_ReadProbe_probe)
    /\ \/ Counter_IsHealthy_Check = TRUE  /\ SetThread(t, T_ReadHealth) \* Abort
       \/ Counter_IsHealthy_Check = FALSE /\ SetThread(t, T_ReadProbe_probe)
    /\ UNCHANGED << vars_upstream, counts, vars_probes >>

\* Read the probe state.
\*
\* A request will either be allowed through, or aborted.
ThreadShouldProbe_probe(t) == 
    /\ GetThread(t) = T_ReadProbe_probe
    /\ \/ ProbeStart(t) /\ UNCHANGED vars_upstream
       \/ ProbeContinue(t) /\ UNCHANGED << vars_upstream, counts, probe_resets >>
       \/ ProbeExhausted(t) /\ UNCHANGED << vars_upstream, counts, vars_probes >>

\* The thread makes a request to the upstream and records the result.
ThreadMakeRequest(t) ==
    /\ GetThread(t) = T_MakeRequest
    /\ SetThread(t, T_ReadHealth)
    /\ \/ upstream_healthy = TRUE  /\ SetRequestOk
       \/ upstream_healthy = FALSE /\ SetRequestErr
    /\ UNCHANGED << vars_upstream, vars_probes >>

\* Periodically request result counters are reset to ensure the circuit breaker
\* doesn't have to observe large numbers of errors to become unhealthy, after
\* having previously observed large numbers of successful requests (or vice
\* versa).
ResetCounters == 
    /\ Counter_IsHealthy
    /\ ~Counter_IsProbing
    /\ SetCounts(NumProbes, 0)
    /\ UNCHANGED << vars_upstream, vars_probes, threads >>

Init == 
    /\ threads = [n \in Threads |-> T_ReadHealth]
    /\ upstream_healthy \in BOOLEAN
    /\ outage_count = 0
    /\ counts = [ok |-> 0, err |-> 0]
    /\ probes_started = 0
    /\ probe_resets = 0

Next == 
    \/ UpstreamGoesOffline
    \/ UpstreamGoesOnline
    \/ ResetCounters
    \/ \E t \in Threads:
        \/ ThreadReadHealth(t)
        \/ ThreadShouldProbe_health(t)
        \/ ThreadShouldProbe_probe(t)
        \/ ThreadMakeRequest(t)
    \/ UNCHANGED vars

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ \E t \in Threads: 
        /\ WF_vars(ThreadReadHealth(t))
        /\ WF_vars(ThreadShouldProbe_health(t))
        /\ WF_vars(ThreadMakeRequest(t))
        /\ SF_vars(ThreadShouldProbe_probe(t) /\ ProbeStart(t))

TypeOk == 
    /\ threads \in [Threads -> {
            T_MakeRequest, 
            T_ReadHealth, 
            T_ReadProbe_health, 
            T_ReadProbe_probe
       }]
    /\ outage_count \in 0..MaxOutages
    /\ upstream_healthy \in BOOLEAN
    /\ counts \in [ok: Int, err: Int]
    /\ probes_started \in 0..NumProbes
    /\ probe_resets \in 0..MaxProbeResets

----------------------------------------------------------------------------

ExclusiveProbeState == \A t \in Threads: 
    (ENABLED ProbeContinue(t)) /= (ENABLED ProbeExhausted(t))

(*************************** Temporal Properties ***************************)

\* Eventually the circuit breaker is always "healthy", within the bounds of the
\* model.
EventuallyAlwaysHealthy == <>[](
    \/ Counter_IsHealthy_Check       \* Terminates in a healthy state, or
    \/ probe_resets = MaxProbeResets \* Reaches model bounds in any state
)

=============================================================================
\* Author: Dom <dom@itsallbroken.com>
