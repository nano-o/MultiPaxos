----------------------------- MODULE DiskPaxos -----------------------------

(***************************************************************************)
(* A formalization of the SWMR-Shared-Memory Disk Paxos, as described in   *)
(* Lamport and Gafni's paper.                                              *)
(*                                                                         *)
(* This is an interesting view on Paxos.  Can we base the correctness      *)
(* proof on the same notions as for classic Paxos? I.e.  what about ballot *)
(* arrays? What about the Choosable predicate and its monotonicity?        *)
(*                                                                         *)
(* A value is choosable at ballot b if the owner p of b can complete its   *)
(* ballot with v.  This is equivalent to the disjunction of the following: *)
(* rs[p].mbal < b and rs[p].mbal is the highest ballot; rs[p].mbal = b and *)
(* rs[p].mbal is the highest ballot and rs[p].inp = v; rs[p].mbal =        *)
(* rs[p].bal = b and rs[p].inp = v.                                        *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT P, Ballots, NotABallot, V, NotAnInput
\* V contains the values to decide upon.

ASSUME NotABallot \notin Ballots
ASSUME NotAnInput \notin V

CONSTANT Bals(_) \* maps a process to its set of ballots.

ASSUME \A p \in P : Bals(p) \subseteq Ballots

Dblock == [mbal : Ballots \cup {NotABallot}, bal : Ballots \cup {NotABallot}, 
    inp : V \union {NotAnInput}]

Min(xs) == CHOOSE x \in xs : \A y \in xs : y >= x

(*
--algorithm DiskPaxos {
    variables
        \* Below the f[p].inp component does not matter, but it reduces the state-space to set it.
        rs \in {f \in [P -> Dblock] : \A p \in P : 
            f[p].mbal = NotABallot /\ f[p].bal = NotABallot /\ f[p].inp = NotAnInput};
        \* Here we could take anything in Bal(p) for the f[p].mbal component; again, we set it to reduce the state-space.
        dblock \in {f \in [P -> Dblock] : \A p \in P : 
            f[p].mbal = Min(Bals(p)) /\ f[p].inp # NotAnInput /\ f[p].bal = NotABallot};
        decisions = {};
    define {
        MaxBal(bals) == IF bals = {NotABallot} 
            THEN NotABallot
            ELSE CHOOSE b \in bals \ {NotABallot} : \A c \in bals  \ {NotABallot} : c <= b
        Inp(blocksRead) ==
            LET nonInitBlks ==  {db \in blocksRead : db.mbal # NotABallot}
                \* Note that using mbal in nonInitBlks is crucial.
                bals == {db.bal : db \in nonInitBlks}
            IN 
                IF nonInitBlks = {} THEN NotAnInput 
                ELSE CHOOSE inp \in V : \E db \in nonInitBlks : 
                    db.inp = inp /\ db.bal = MaxBal(bals) 
    }
    process (proc \in P)
        variables
            \* Does not work... so we have to use global variables.
            \* dblock \in {db \in Dblock : db.mbal \in Bals(self) /\ db.inp # NotAnInput};
            toRead; phase = 1;
            blocksRead = {};
        {   l1: rs[self] := dblock[self];
                toRead := P;
            l2: while (toRead # {})
                    with (p \in toRead, dbp = rs[p]) {
                        if (dbp.mbal # NotABallot /\ dbp.mbal > dblock[self].mbal) {
                            if (\E b \in Bals(self) : b > dblock[self].mbal) {
                                dblock[self].mbal := CHOOSE b \in Bals(self) : 
                                    b > dblock[self].mbal; 
                                goto "l1"
                            } else goto "Done"
                        }
                        else {
                            blocksRead := blocksRead \union {rs[p]};
                            toRead := toRead \ {p}
                        }
                    };
            l3: if (phase = 1) {
                    dblock[self].bal := dblock[self].mbal || dblock[self].inp := 
                        IF Inp(blocksRead) = NotAnInput THEN dblock[self].inp 
                        ELSE Inp(blocksRead);
                    phase := 2;
                    goto "l1" 
                } else 
                    decisions := decisions \union {dblock[self].inp}
        }
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES rs, dblock, decisions, pc

(* define statement *)
MaxBal(bals) == IF bals = {NotABallot}
    THEN NotABallot
    ELSE CHOOSE b \in bals \ {NotABallot} : \A c \in bals  \ {NotABallot} : c <= b
Inp(blocksRead) ==
    LET nonInitBlks ==  {db \in blocksRead : db.mbal # NotABallot}

        bals == {db.bal : db \in nonInitBlks}
    IN
        IF nonInitBlks = {} THEN NotAnInput
        ELSE CHOOSE inp \in V : \E db \in nonInitBlks :
            db.inp = inp /\ db.bal = MaxBal(bals)

VARIABLES toRead, phase, blocksRead

vars == << rs, dblock, decisions, pc, toRead, phase, blocksRead >>

ProcSet == (P)

Init == (* Global variables *)
        /\ rs \in    {f \in [P -> Dblock] : \A p \in P :
                  f[p].mbal = NotABallot /\ f[p].bal = NotABallot /\ f[p].inp = NotAnInput}
        /\ dblock \in        {f \in [P -> Dblock] : \A p \in P :
                      f[p].mbal = Min(Bals(p)) /\ f[p].inp # NotAnInput /\ f[p].bal = NotABallot}
        /\ decisions = {}
        (* Process proc *)
        /\ toRead = [self \in P |-> defaultInitValue]
        /\ phase = [self \in P |-> 1]
        /\ blocksRead = [self \in P |-> {}]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ rs' = [rs EXCEPT ![self] = dblock[self]]
            /\ toRead' = [toRead EXCEPT ![self] = P]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << dblock, decisions, phase, blocksRead >>

l2(self) == /\ pc[self] = "l2"
            /\ IF toRead[self] # {}
                  THEN /\ \E p \in toRead[self]:
                            LET dbp == rs[p] IN
                              IF dbp.mbal # NotABallot /\ dbp.mbal > dblock[self].mbal
                                 THEN /\ IF \E b \in Bals(self) : b > dblock[self].mbal
                                            THEN /\ dblock' = [dblock EXCEPT ![self].mbal =                  CHOOSE b \in Bals(self) :
                                                                                            b > dblock[self].mbal]
                                                 /\ pc' = [pc EXCEPT ![self] = "l1"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                 /\ UNCHANGED dblock
                                      /\ UNCHANGED << toRead, blocksRead >>
                                 ELSE /\ blocksRead' = [blocksRead EXCEPT ![self] = blocksRead[self] \union {rs[p]}]
                                      /\ toRead' = [toRead EXCEPT ![self] = toRead[self] \ {p}]
                                      /\ pc' = [pc EXCEPT ![self] = "l2"]
                                      /\ UNCHANGED dblock
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l3"]
                       /\ UNCHANGED << dblock, toRead, blocksRead >>
            /\ UNCHANGED << rs, decisions, phase >>

l3(self) == /\ pc[self] = "l3"
            /\ IF phase[self] = 1
                  THEN /\ dblock' = [dblock EXCEPT ![self].bal = dblock[self].mbal,
                                                   ![self].inp = IF Inp(blocksRead[self]) = NotAnInput THEN dblock[self].inp
                                                                 ELSE Inp(blocksRead[self])]
                       /\ phase' = [phase EXCEPT ![self] = 2]
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                       /\ UNCHANGED decisions
                  ELSE /\ decisions' = (decisions \union {dblock[self].inp})
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << dblock, phase >>
            /\ UNCHANGED << rs, toRead, blocksRead >>

proc(self) == l1(self) \/ l2(self) \/ l3(self)

Next == (\E self \in P: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Inv1 == \A p \in P : dblock[p].bal # NotABallot => dblock[p].bal <= dblock[p].mbal

Inv2 == \A p \in P : rs[p].mbal = rs[p].bal /\ rs[p].mbal # NotABallot => phase[p] = 2 

Agreement == \A v,w \in decisions : v = w
 
Owner(b) == CHOOSE p \in P : b \in Bals(p)

Choosable(v, b) == LET p == Owner(b) IN
    CASE 
        rs[p].mbal = NotABallot \/ rs[p].mbal < b \/ (rs[p].mbal = b /\ phase[p] = 1) 
            -> \A q \in P : rs[q].mbal = NotABallot \/ rs[q].mbal < dblock[q].mbal
    []  rs[p].mbal = b /\ rs[p].mbal = rs[p].bal 
            -> rs[p].inp = v /\ (\A q \in toRead[p] : dblock[q].mbal > b => q \notin toRead[p])
    []  TRUE -> FALSE
    
Inv3 == \A v \in V : \A p \in P : 
    (phase[p] = 2 /\ dblock[p].inp = v) => (\A b2 \in Ballots : 
        b2 < dblock[p].bal => (\A w \in V : Choosable(w,b2) => v = w))
    
=============================================================================
\* Modification History
\* Last modified Mon Jan 09 20:25:34 PST 2017 by nano
\* Created Mon Jan 09 08:47:33 PST 2017 by nano
