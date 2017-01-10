---------------------------- MODULE MCDiskPaxos ----------------------------

EXTENDS Naturals

CONSTANT 
    N, \* The number of processes
    B \* The number of ballots
    
P == 1..N
Ballots == 0..(B-1)
Bals(p) == {b \in Ballots : b % N = p-1}

CONSTANT NotABallot, V, NotAnInput, defaultInitValue
VARIABLES rs, dblock, decisions, pc
VARIABLES toRead, phase, blocksRead, aborted

INSTANCE DiskPaxos

=============================================================================
\* Modification History
\* Last modified Mon Jan 09 20:45:20 PST 2017 by nano
\* Created Mon Jan 09 18:08:36 PST 2017 by nano
