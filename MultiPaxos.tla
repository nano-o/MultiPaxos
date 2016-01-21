----------------------------- MODULE MultiPaxos -----------------------------
    

(***************************************************************************)
(* An abstract specification of the MultiPaxos algorithm.  We do not model *)
(* the network nor leaders explicitely.  Instead, we keep the history of   *)
(* all votes cast and use this history to describe how new votes are cast. *)
(* Note that, in some way, receiving a message corresponds to reading a    *)
(* past state of the sender.  We produce the effect of having the leader   *)
(* by requiring that not two different values can be voted for in the same *)
(* ballot.                                                                 *)
(*                                                                         *)
(* This specification is inspired from the abstract specification of       *)
(* Generalized Paxos presented in the Generalized Paxos paper by Lamport.  *)
(***************************************************************************)

EXTENDS MultiConsensus

(***************************************************************************)
(* The variable ballot maps an acceptor to its current ballot.             *)
(*                                                                         *)
(* Given an acceptor a, an instance i, and a ballot b, vote[a][i][b]       *)
(* records the vote that a casted in ballot b of instance i.               *)
(***************************************************************************)
VARIABLES
    ballot, vote, propCmds

Init ==
    /\  ballot = [a \in Acceptors |-> -1]
    /\  vote = [a \in Acceptors |-> 
            [i \in Instances |-> 
                [b \in Ballots |-> None]]]
    /\  propCmds = {}

TypeInv ==
    /\  ballot \in [Acceptors -> {-1} \cup Ballots]
    /\  vote \in [Acceptors -> 
            [Instances -> 
                [Ballots -> {None} \cup V]]]
    /\  propCmds \in SUBSET V

    
(***************************************************************************)
(* Now starts the specification of the algorithm                           *)
(***************************************************************************)

(***************************************************************************)
(* A ballot is conservative when all acceptors which vote in the ballot    *)
(* vote for the same value.  In MultiPaxos, the leader of a ballot ensures *)
(* that the ballot is conservative.                                        *)
(***************************************************************************)
Conservative(i,b) ==
    \A a1,a2 \in Acceptors :
        LET v1 == vote[a1][i][b]
            v2 == vote[a2][i][b]
        IN  (v1 # None /\ v2 # None) => v1 = v2

ConservativeVoteArray ==
    \A i \in Instances : \A b \in Ballots :
        Conservative(i,b)
            
(***************************************************************************)
(* The maximal ballot smaller than max in which a has voted in instance i. *)
(***************************************************************************)
MaxVotedBallot(i, a, max) ==
    Max({b \in Ballots : b <= max /\ vote[a][i][b] # None} \cup {-1}, <=)

MaxVotedBallots(i, Q, max) == {MaxVotedBallot(i, a, max) : a \in Q}

(***************************************************************************)
(* The vote casted in the maximal ballot smaller than max by an acceptor   *)
(* of the quorum Q.                                                        *)
(***************************************************************************)
HighestVote(i, max, Q) == 
    IF \E a \in Q : MaxVotedBallot(i, a, max) # -1 
    THEN 
        LET MaxVoter == CHOOSE a \in Q : 
                MaxVotedBallot(i, a, max) = Max(MaxVotedBallots(i, Q, max), <=)
        IN vote[MaxVoter][i][MaxVotedBallot(i, MaxVoter, max)]
    ELSE
        None

(***************************************************************************)
(* Values that are safe to vote for in ballot b according to a quorum Q    *)
(* whose acceptors have all reached ballot b.                              *)
(*                                                                         *)
(* If there is an acceptor in Q that has voted in a ballot less than b,    *)
(* then the only safe value is the value voted for by an acceptor in Q in  *)
(* the highest ballot less than b.                                         *)
(*                                                                         *)
(* Else, all values are safe.                                              *)
(*                                                                         *)
(* In an implementation, the leader of a ballot b can compute              *)
(* ProvedSafeAt(i, Q, b) when it receives 1b messages from the quorum Q.   *)
(***************************************************************************)
ProvedSafeAt(i, Q, b) ==
    IF HighestVote(i, b-1, Q) # None
    THEN {HighestVote(i, b-1, Q)}
    ELSE V

(***************************************************************************)
(* The propose action:                                                     *)
(***************************************************************************)
Propose(v) ==
    /\  propCmds' = propCmds \cup {v}
    /\  UNCHANGED <<ballot, vote>>
    

(***************************************************************************)
(* The JoinBallot action: an acceptor can join a higher ballot at any      *)
(* time.  In an implementation, the JoinBallot action is triggered by a 1a *)
(* message from the leader of the new ballot.                              *)
(***************************************************************************)
JoinBallot(a, b) ==
    /\  ballot[a] < b
    /\  ballot' = [ballot EXCEPT ![a] = b]
    /\  UNCHANGED <<vote, propCmds>>

(***************************************************************************)
(* The Vote action: an acceptor casts a vote in instance i.  This action   *)
(* is enabled when the acceptor has joined a ballot, has not voted in its  *)
(* current ballot, and can determine, by reading the last vote cast by     *)
(* each acceptor in a quorum, which value is safe to vote for.  If         *)
(* multiple values are safe to vote for, we ensure that only one can be    *)
(* voted for by requiring that the ballot remain conservative.             *)
(*                                                                         *)
(* In an implementation, the computation of safe values is done by the     *)
(* leader of the ballot when it receives 1b messages from a quorum of      *)
(* acceptors.  The leader then picks a unique value among the safe values  *)
(* and suggests it to the acceptors.                                       *)
(***************************************************************************)
Vote(a,i) ==
    /\  ballot[a] # -1
    /\  vote[a][i][ballot[a]] = None
    /\  \E Q \in Quorums :
            /\  \A q \in Q : ballot[q] \geq ballot[a]
            /\  \E v \in ProvedSafeAt(i, Q, ballot[a]) \cap propCmds : 
                    vote' = [vote EXCEPT ![a] = 
                        [@ EXCEPT ![i] = [@ EXCEPT ![ballot[a]] = v]]]
    /\  UNCHANGED <<ballot, propCmds>>
    /\  Conservative(i, ballot[a])'
    
Next == 
    \/  \E v \in V : Propose(v)
    \/  \E a \in Acceptors : \E b \in Ballots : JoinBallot(a, b)
    \/  \E a \in Acceptors : \E i \in Instances : Vote(a, i)

Spec == Init /\ [][Next]_<<ballot,vote,propCmds>>

(***************************************************************************)
(* Some properties and invariants that help understanding the algo and     *)
(* would probably be needed in a proof.                                    *)
(***************************************************************************)

(***************************************************************************)
(* The maximal ballot in which an acceptor a voted is always less than or  *)
(* equal to its current ballot.                                            *)
(***************************************************************************)
WellFormed == \A a \in Acceptors : \A i \in Instances : \A b \in Ballots :
    b > ballot[a] => vote[a][i][b] = None
    
THEOREM Spec => []WellFormed

ChosenAt(i,b,v) ==
    \E Q \in Quorums : \A a \in Q : vote[a][i][b] = v

Chosen(i,v) ==
    \E b \in Ballots : ChosenAt(i,b,v)

Choosable(v, i, b) ==
    \E Q \in Quorums : \A a \in Q : ballot[a] > b => vote[a][i][b] = v
    
SafeAt(v, i, b) ==
    \A b2 \in Ballots : \A v2 \in V : 
        (b2 < b /\ Choosable(v2, i, b2))
        => v = v2

SafeInstanceVoteArray(i) == \A b \in Ballots : \A a \in Acceptors :
    LET v == vote[a][i][b]
    IN  v # None => SafeAt(v, i, b)

SafeVoteArray == \A i \in Instances : SafeInstanceVoteArray(i)

THEOREM Spec => []SafeVoteArray

(***************************************************************************)
(* If the vote array is well formed and the vote array is safe, then for   *)
(* each instance only a unique value can be chosen.                        *)
(***************************************************************************)
THEOREM TypeInv /\ WellFormed /\ SafeVoteArray => \A i \in Instances :
    \A v1,v2 \in V : Chosen(i, v1) /\ Chosen(i, v2) => v1 = v2

(***************************************************************************)
(* In a well-formed, safe, and conservative vote array, all values that    *)
(* are proved safe are safe.                                               *)
(***************************************************************************)
THEOREM TypeInv /\ WellFormed /\ SafeVoteArray /\ ConservativeVoteArray 
    =>  \A v \in V : \A i \in Instances : 
            \A Q \in Quorums : \A b \in Ballots :
                /\  \A a \in Q : ballot[a] \geq b
                /\  v \in ProvedSafeAt(i, Q, b) 
                => SafeAt(v, i, b) 
Correctness ==  
    \A i \in Instances : \A v1,v2 \in V :
        Chosen(i, v1) /\ Chosen(i, v2) => v1 = v2
        
THEOREM Spec => []Correctness

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 01:21:39 EST 2016 by nano
\* Created Mon Nov 02 09:08:37 EST 2015 by nano
