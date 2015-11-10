--------------------------- MODULE MultiConsensus ---------------------------
(***************************************************************************)
(* A set of constants and definitions for use in the specification of      *)
(* MultiPaxos-like algorithms.                                             *)
(***************************************************************************)

EXTENDS Integers, FiniteSets
    
CONSTANTS Acceptors, Quorums, V, None

ASSUME None \notin V

ASSUME \A Q \in Quorums : Q \subseteq Acceptors

ASSUME \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

ASSUME -1 \notin Ballots

Instances == Nat

MajQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) > Cardinality(Acceptors) \div 2}

Max(xs, LessEq(_,_)) ==  CHOOSE x \in xs : \A y \in xs : LessEq(y,x)

=============================================================================
\* Modification History
\* Last modified Tue Nov 03 10:15:12 EST 2015 by nano
\* Created Mon Nov 02 19:28:17 EST 2015 by nano
