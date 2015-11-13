----------------------- MODULE DistributedMultiPaxos -----------------------

EXTENDS MultiConsensus

VARIABLES
    ballot, vote, network

(***************************************************************************)
(* Each ballot has a leader                                                *)
(***************************************************************************)
Leader(b) == CHOOSE f \in [Ballots -> Acceptors] : TRUE

(***************************************************************************)
(* We do not model learners, so no need for 2b messages                    *)
(***************************************************************************)
Msgs == 
    {<<"propose", v>> : v \in V } \cup
    {<<"1a", b>> : b \in Ballots} \cup
    {<<"1b", vs>> : vs \in [Instances -> V \cup {None}]} \cup
    {<<"2a", v>> : v \in Ballots}
    

Init ==
    /\  ballot = [a \in Acceptors |-> -1]
    /\  vote = [a \in Acceptors |-> 
            [i \in Instances |-> 
                [b \in Ballots |-> None]]]
    /\  network = {}

TypeInv ==
    /\  ballot \in [Acceptors -> {-1} \cup Ballots]
    /\  vote \in [Acceptors -> 
            [Instances -> 
                [Ballots -> {None} \cup V]]]
    /\  network \subseteq Msgs

Propose(c) ==
    /\  network' = network \cup {<<"propose", c>>}
    /\  UNCHANGED <<ballot, vote>>

Phase1a(b) ==
    /\  network' = network \cup {<<"1a", b>>}
    /\  UNCHANGED <<ballot, vote>>

MaxVoteInInstance(a, i) ==
    LET maxBallot == Max({b \in Ballots : vote[a][i][b] # None} \cup {-1}, <=)
        v == IF maxBallot > -1 THEN vote[a][i][maxBallot] ELSE None
    IN <<maxBallot, v>>

(***************************************************************************)
(* This could be truncated to the highest started instance.                *)
(***************************************************************************)
MaxVotes(a) ==
    [i \in Instances |-> MaxVoteInInstance(a, i)]

Phase1b(a, b, v) ==
    /\  ballot[a] < b
    /\  <<"1a", b>> \in network
    /\  ballot' = [ballot EXCEPT ![a] = b]
    /\  network' = network \cup {<<"1b", MaxVotes(a)>>}
    /\  UNCHANGED vote

=============================================================================
\* Modification History
\* Last modified Fri Nov 13 18:44:45 EST 2015 by nano
\* Created Fri Nov 13 17:59:21 EST 2015 by nano
