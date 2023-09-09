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

This model validates liveness of the circuit, ensuring it always eventually 
becomes healthy (allowing requests) given a bounded number of upstream errors, 
and does not deadlock or become "stuck" in an unhealthy state.

The per-thread atomic states, advancing independently and concurrently, are  
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
     

The number of probe windows, counter resets, and number of requests (before a 
reset, if available) are bounded to limit the state space of the model. Only 
behaviours that do not reach the probe window bound are validated as having a 
circuit that eventually becomes healthy.

--------------------------- MODULE health_circuit --------------------------

EXTENDS TLC, Integers

CONSTANTS 
    \* The set of threads concurrently interacting with the circuit breaker.
    Threads, 
    \* A model bound on the number of upstream errors observed.
    MaxErrors,
    \* A model bound on the number of probe resets that occur.
    MaxProbeResets,
    \* A model bound on the number of request result counter resets that occur.
    MaxCounterResets,
    \* Number of probe requests to send per probe window.
    NumProbes,
    \* Thread states
    T_ReadHealth,       \* Start of request - next read the circuit health
    T_ReadProbe_health, \* Unhealthy, read probe state - step 1: check health
    T_ReadProbe_probe,  \* Unhealthy, read probe state - step 2: probe candidate?
    T_MakeRequest       \* Submit the request to the upstream

VARIABLES 
    threads,
    counts,
    probes_started,
    probe_resets,
    counter_resets

vars == << 
    threads, 
    counts,
    probes_started,
    probe_resets,
    counter_resets
>>

vars_probes == << probes_started, probe_resets >>
vars_counts == << counts, counter_resets >>

SetThread(t, state) == threads' = [threads EXCEPT ![t] = state]
GetThread(t) == threads[t]

SetCounts(ok, err) == counts' = [ok |-> ok, err |-> err]
SetRequestOk == counts' = [counts EXCEPT !.ok = @ + 1]
SetRequestErr == counts' = [counts EXCEPT !.err = @ + 1]
RequestTotal == counts.ok + counts.err
\* Bound the model to the minimum number of successful requests to drive healthy
MaxOk == MaxErrors + NumProbes

\* Counter states that are derived from the request counts.
Counter_IsProbing == RequestTotal < NumProbes
Counter_IsHealthy == counts.ok > (counts.err + 1)

\* The CircuitBreaker::is_healthy() method composes the above counter states.
Counter_IsHealthy_Check == ~Counter_IsProbing /\ Counter_IsHealthy

----------------------------------------------------------------------------

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
    /\ \/ Counter_IsHealthy_Check = TRUE  /\ SetThread(t, T_MakeRequest) \* Fast "healthy" path
       \/ Counter_IsHealthy_Check = FALSE /\ SetThread(t, T_ReadProbe_health)
    /\ UNCHANGED << vars_counts, vars_probes >>

\* The upstream was believed to be unhealthy when evaluating above (but both the
\* upstream and the circuit may no longer be unhealthy).
\*
\* If the circuit is now healthy, this request is aborted (potential future
\* optimisation to continue with the request).
\* 
\* If the circuit is unhealthy, read the probe state.
ThreadShouldProbe_health(t) == 
    /\ GetThread(t) = T_ReadProbe_health
    /\ \/ Counter_IsHealthy_Check = TRUE  /\ SetThread(t, T_ReadHealth) \* Abort
       \/ Counter_IsHealthy_Check = FALSE /\ SetThread(t, T_ReadProbe_probe)
    /\ UNCHANGED << vars_counts, vars_probes >>

\* Read the probe state.
\*
\* A request will either be allowed through, or aborted.
ThreadShouldProbe_probe(t) == 
    /\ GetThread(t) = T_ReadProbe_probe
    /\ \/ ProbeStart(t) /\ UNCHANGED << counter_resets >>
       \/ ProbeContinue(t) /\ UNCHANGED << vars_counts, probe_resets >>
       \/ ProbeExhausted(t) /\ UNCHANGED << vars_counts, vars_probes >>

\* The thread makes a request to the upstream and records the result.
ThreadMakeRequest(t) ==
    /\ GetThread(t) = T_MakeRequest
    /\ SetThread(t, T_ReadHealth)
    /\ \/ counts.ok < MaxOk /\ SetRequestOk
       \/ counts.err < MaxErrors /\ SetRequestErr
    /\ UNCHANGED << vars_probes, counter_resets >>

\* Periodically request result counters are reset to ensure the circuit breaker
\* doesn't have to observe large numbers of errors to become unhealthy, after
\* having previously observed large numbers of successful requests (or vice
\* versa).
ResetCounters == 
    /\ counter_resets < MaxCounterResets
    /\ counter_resets' = counter_resets + 1
    /\ Counter_IsHealthy
    /\ ~Counter_IsProbing
    /\ SetCounts(NumProbes, 0)
    /\ UNCHANGED << vars_probes, threads >>

Init == 
    /\ threads = [n \in Threads |-> T_ReadHealth]
    /\ counts = [ok |-> 0, err |-> 0]
    /\ probes_started = 0
    /\ probe_resets = 0
    /\ counter_resets = 0

Next == 
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
    /\ \A t \in Threads: 
        /\ WF_vars(Next)
        /\ SF_vars(ThreadShouldProbe_probe(t) /\ ProbeStart(t))

TypeOk == 
    /\ threads \in [Threads -> {
            T_MakeRequest, 
            T_ReadHealth, 
            T_ReadProbe_health, 
            T_ReadProbe_probe
       }]
    /\ counts \in [ok: 0..MaxOk, err: 0..MaxErrors]
    /\ probes_started \in 0..NumProbes
    /\ probe_resets \in 0..MaxProbeResets
    /\ counter_resets \in 0..MaxCounterResets

----------------------------------------------------------------------------

ExclusiveProbeState == \A t \in Threads: 
    (ENABLED ProbeContinue(t)) /= (ENABLED ProbeExhausted(t))

(*************************** Temporal Properties ***************************)

\* Eventually the circuit breaker is always "healthy", within the bounds of the
\* model.
EventuallyAlwaysHealthy == <>[](
    \/ Counter_IsHealthy_Check       \* The circuit becomes healthy
    \/ probe_resets = MaxProbeResets \* Or the model deadlocks at state bounds
)

=============================================================================
\* Author: Dom <dom@itsallbroken.com>
