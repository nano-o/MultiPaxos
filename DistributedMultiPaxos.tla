----------------------- MODULE DistributedMultiPaxos -----------------------

(***************************************************************************)
(* A specification of MultiPaxos that includes a model of the network.     *)
(* Compared to the abstract specification, processes now communicate       *)
(* through the network instead of directly reading each other's state.     *)
(* The main difference is that network messages reflect a past state of    *)
(* their sender, not its current state.  Note that since the state of the  *)
(* processes is monothonic (i.e.  values written in the vote array are     *)
(* never overwritten and ballots on increase), knowing the past state      *)
(* gives some information about the current state.                         *)
(***************************************************************************)

EXTENDS MultiConsensus

VARIABLES
    ballot, vote, network, propCmds

(***************************************************************************)
(* We do not model learners, so no need for 2b messages                    *)
(***************************************************************************)
Msgs == 
    {<<"1a", b>> : b \in Ballots} \cup
    {<<"1b", a, i, b, <<maxB, v>>>> : i \in Instances, a \in Acceptors, 
        b \in Ballots, maxB \in Ballots \cup {-1}, v \in V \cup {None}} \cup
    {<<"2a", i, b, v>> : i \in Instances, b \in Ballots, v \in V}
    
Init ==
    /\  ballot = [a \in Acceptors |-> -1]
    /\  vote = [a \in Acceptors |-> 
            [i \in Instances |-> 
                [b \in Ballots |-> None]]]
    /\  network = {}
    /\  propCmds = {}
(*    /\  1bInfo = [b \in Ballots |-> [i \in Instances |-> None]]*)

TypeInv ==
    /\  ballot \in [Acceptors -> {-1} \cup Ballots]
    /\  vote \in [Acceptors -> 
            [Instances -> 
                [Ballots -> {None} \cup V]]]
    /\  network \subseteq Msgs
    /\  propCmds \subseteq V
(*    /\  1bInfo = [Ballots -> [Instances -> V \cup {None}]]*)

Propose(c) ==
    /\  propCmds' = propCmds \cup {c}
    /\  UNCHANGED <<ballot, vote, network>>

Phase1a(b) ==
    /\  network' = network \cup {<<"1a", b>>}
    /\  UNCHANGED <<ballot, vote, propCmds>>

(***************************************************************************)
(* A pair consisting of the highest ballot in which the acceptro a has     *)
(* voted in instance i.  If a has not voted in instance i, then <<-1,      *)
(* None>>.                                                                 *)
(***************************************************************************)
MaxAcceptorVote(a, i) ==
    LET maxBallot == Max({b \in Ballots : vote[a][i][b] # None} \cup {-1}, <=)
        v == IF maxBallot > -1 THEN vote[a][i][maxBallot] ELSE None
    IN <<maxBallot, v>>

(***************************************************************************)
(* Acceptor a receives responds from a 1a message by sending, for each     *)
(* instance i, its max vote in this instance.                              *)
(***************************************************************************)
Phase1b(a, b, v) ==
    /\  ballot[a] < b
    /\  <<"1a", b>> \in network
    /\  ballot' = [ballot EXCEPT ![a] = b]
    /\  network' = network \cup 
            {<<"1b", a, i, b, MaxAcceptorVote(a,i)>> : i \in Instances}
    /\  UNCHANGED <<vote, propCmds>>

1bMsgs(b, i, Q) ==
    {m \in network : m[1] = "1b"  /\ m[2] \in Q /\ m[3] = i /\ m[4] = b}

(***************************************************************************)
(* The vote cast in the highest ballot less than b in instance i.  This    *)
(* vote is unique because all ballots are conservative.  Note that this    *)
(* can be None.                                                            *)
(***************************************************************************)
MaxVote(b, i, Q) ==
    LET maxBal == Max({m[5][1] : m \in 1bMsgs(b, i, Q)}, <=)
    IN  CHOOSE v \in V \cup {None} : \E m \in 1bMsgs(b, i, Q) : 
            /\ m[5][1] = maxBal /\ m[5][2] = v

(***************************************************************************)
(* The leader of ballot b sends 2a messages when it is able to determine a *)
(* safe value (i.e.  when it receives 1b messages from a quorum), and only *)
(* if it has not done so before.                                           *)
(***************************************************************************)    
Phase2a(b, i) ==
    /\ \neg (\E m \in network : m[1] = "2a" /\ m[2] = i /\ m[3] = b)
    /\ \E Q \in Quorums :
        /\  \A a \in Q : \E m \in 1bMsgs(b, i, Q) : m[2] = a
        /\  LET  maxV == MaxVote(b, i , Q)
                 safe == IF maxV # None THEN {maxV} ELSE propCmds
            IN  \E v \in safe : network' = network \cup {<<"2a", i, b, v>>}
    /\  UNCHANGED <<propCmds, ballot, vote>>

Vote(a, b, i) ==
    /\  ballot[a] = b
    /\  \E m \in network : 
            /\  m[1] = "2a" /\ m[2] = i /\ m[3] = b
            /\  vote' = [vote EXCEPT ![a] = [@ EXCEPT ![i] = 
                    [@ EXCEPT ![b] = m[4]]]]
    /\  UNCHANGED <<propCmds, ballot, network>>
    
Next == 
    \/  \E c \in V : Propose(c)
    \/  \E b \in Ballots : Phase1a(b)
    \/  \E a \in Acceptors, b \in Ballots, v \in V : Phase1b(a, b, v)
    \/  \E b \in Ballots, i \in Instances : Phase2a(b, i)
    \/  \E a \in Acceptors, b \in Ballots, i \in Instances : Vote(a, b, i)
    
Spec == Init /\ [][Next]_<<propCmds, ballot, vote, network>>

MultiPaxos == INSTANCE MultiPaxos

THEOREM Spec => MultiPaxos!Spec

=============================================================================
\* Modification History
\* Last modified Wed Nov 18 18:41:57 EST 2015 by nano
\* Created Fri Nov 13 17:59:21 EST 2015 by nano
