This TLA+ model covers the IOx router's schema cache construction, including
gossiping updates between peers over an unreliable transport, and driving
anti-entropy / convergence / eventual consistency using a Merkle Search Tree to
synchronise inconsistent entries.

Schema cache operations are trivially monotonic - an append-only set (CRDT) is
used to perform conflict-free merges of schema updates between disjoint peers.

Eventual consistency is achieved by identifying and converging inconsistent
schemas across peers cheaply and efficiently using a Merkle Search Tree, with
inconsistent schemas fetched from peers and merged into the local node state.

---------------------------- MODULE schema_cache ----------------------------

EXTENDS TLC, Integers

CONSTANTS Namespaces, Tables, Columns, Peers, MaxEvents

VARIABLES 
    \* A state bound restricting the number of schemas applied to the system.
    event_count, 
    \* A function of Peers to schema sets modelling the peer's local cache
    \* state.
    p_state,
    \* Set of tuples "<< P, schema >>" where "P" is the peer which should apply
    \* the gossip message, and "schema" is the gossiped schema to apply.
    gossip_set

Gossip == INSTANCE Gossip

vars == << p_state, event_count, gossip_set >>

\* Helper operator for all possible schema combinations
Schemas == Namespaces \X Tables \X Columns

\* Helper to merge the set of schemas "s" into the cache state of "p".
CacheMerge(p, s) == p_state' = [p_state EXCEPT ![p] = @ \union s]

----------------------------------------------------------------------------

\* Upsert a schema to a peer and place the new addition in the gossip queue.
UpsertSchema(p) == 
    /\ event_count < MaxEvents \* Limit state space
    /\ event_count' = event_count + 1
    /\ \E s \in {v \in Schemas: v \notin p_state[p]}: \* No duplicate upserts 
        /\ CacheMerge(p, {s})
        /\ Gossip!Broadcast(p, s)

\* Peer "p" receives a previously gossiped schema.
GossipRx(p, msg) == CacheMerge(p, {msg})

\* Perform a sync round, pulling all missing schemas from p into q.
SyncPull(p, q) == LET diff == p_state[p] \ p_state[q] IN 
    /\ diff # {}
    /\ CacheMerge(q, diff)
    /\ UNCHANGED << event_count, gossip_set >>

Init == 
    /\ p_state = [p \in Peers |-> {}]
    /\ event_count = 0
    /\ Gossip!Init

Next == 
    \/ Gossip!Drop /\ UNCHANGED << p_state, event_count >>
    \/ Gossip!Rx(GossipRx) /\ UNCHANGED << event_count >>
    \/ \E p, q \in Peers: SyncPull(p, q)
    \/ \E p \in Peers: UpsertSchema(p) 
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_<<vars>>(Next)

TypeOk == 
    /\ p_state \in [Peers -> SUBSET Schemas]
    /\ event_count \in 0..MaxEvents
    /\ Gossip!TypeOk(Schemas)

----------------------------------------------------------------------------
(*************************** Temporal Properties ***************************)

\* Eventually all gossip messages are applied or dropped.
EventuallyAllGossipApplied == Gossip!EventuallyAllGossipApplied

\* Eventually all peers are consistent (eventual cache consistency).
EventuallyConsistent == <>[](\A p, q \in Peers: p_state[p] = p_state[q])

\* Cache state is monotonic.
MonotonicCaches == [][\A p \in Peers: p_state[p] \subseteq p_state[p]']_vars
=============================================================================
\* Author: Dom <dom@itsallbroken.com>
