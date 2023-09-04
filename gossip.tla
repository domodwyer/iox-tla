Models a single Gossip topic, optionally over an unreliable transport.

------------------------------ MODULE Gossip ------------------------------

EXTENDS TLC, Integers

CONSTANTS Peers

VARIABLES 
    \* Set of tuples "<< P, msg >>" where "msg" is the gossiped message to apply
    \* to peer "P".
    gossip_set

vars == << gossip_set >>

----------------------------------------------------------------------------

\* Send "msg" to all gossip peers, originating "from" the given node which does
\* not receive the message.
Broadcast(from, msg) == 
    /\ \A q \in Peers \ {from}: gossip_set' = gossip_set \union {<<q, msg>>}

\* Receive a gossip message and delegate handling to the provided operator.
\*
\* The delegate operator receives the arguments "(peer, msg)" where "peer" is
\* the peer that has received "msg".
Rx(Op(_, _)) == \E v \in gossip_set:
    /\ Op(v[1], v[2])
    /\ gossip_set' = gossip_set \ {v}

\* Drop a random gossip message, simulating an unreliable transport.
Drop == \E v \in gossip_set: gossip_set' = gossip_set \ {v} 

----------------------------------------------------------------------------

\* Initialise the gossip module state.
Init == gossip_set = {}

\* Type check the gossip state, using "values" as the set of acceptable gossip
\* message payloads.
TypeOk(values) == gossip_set \subseteq (Peers \X values) 

----------------------------------------------------------------------------
(*************************** Temporal Properties ***************************)

\* Eventually all gossip messages are applied or dropped.
EventuallyAllGossipApplied == <>[](gossip_set = {})

=============================================================================
\* Author: Dom <dom@itsallbroken.com>
