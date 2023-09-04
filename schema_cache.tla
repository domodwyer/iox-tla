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
    gossip_queue

vars == << p_state, gossip_queue, event_count >>

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
        /\ \A q \in Peers \ {p}: gossip_queue' = gossip_queue \union {<<q, s>>}

\* Peer "p" receives a previously gossiped schema.
GossipRx(p) == \E msg \in {v \in gossip_queue: v[1] = p}:
    /\ CacheMerge(p, {msg[2]})
    /\ gossip_queue' = gossip_queue \ {msg}
    /\ UNCHANGED <<event_count>>

\* Perform a sync round, pulling all missing schemas from p into q.
SyncPull(p, q) == LET diff == p_state[p] \ p_state[q] IN 
    /\ diff # {}
    /\ CacheMerge(q, diff)
    /\ UNCHANGED <<event_count, gossip_queue>>

\* Drop a random gossip message in the gossip_queue.
GossipDrop == \E v \in gossip_queue: 
    /\ gossip_queue' = gossip_queue \ {v} 
    /\ UNCHANGED <<p_state, event_count>>

Init == 
    /\ p_state = [p \in Peers |-> {}]
    /\ gossip_queue = {}
    /\ event_count = 0

Next == 
    \/ GossipDrop
    \/ \E p, q \in Peers: SyncPull(p, q)
    \/ \E p \in Peers: 
        \/ UpsertSchema(p) 
        \/ GossipRx(p)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_<<vars>>(Next)

TypeOk == /\ DOMAIN p_state = Peers 
    /\ \A p \in Peers: p_state[p] \subseteq Schemas
    /\ gossip_queue \subseteq (Peers \X Schemas)
    /\ event_count \in 0..MaxEvents

----------------------------------------------------------------------------
(*************************** Temporal Properties ***************************)

\* Eventually all gossip messages are applied or dropped.
EventuallyAllGossipApplied == <>[](gossip_queue = {})

\* Eventually all peers are consistent (eventual cache consistency).
EventuallyConsistent == <>[](\A p, q \in Peers: p_state[p] = p_state[q])

\* Cache state is monotonic.
MonotonicCaches == [][\A p \in Peers: p_state[p] \subseteq p_state[p]']_vars
=============================================================================
\* Author: Dom <dom@itsallbroken.com>
