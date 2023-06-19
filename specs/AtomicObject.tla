------------------------------ MODULE AtomicObject ------------------------------
(* Canonical Wait-Free Atomic Object - Distributed Algorithms by Nancy Lynch - p.408 *)
EXTENDS Integers, FiniteSets
CONSTANTS V
VARIABLES val, invBuf, respBuf, stopped

vars == <<val, invBuf, respBuf, stopped>>

\* number of processes
I == 3

TypeOK ==
    /\ val \in V
    /\ invBuf \in SUBSET ((1..I) \X V)
    /\ respBuf \in SUBSET ((1..I) \X V)
    /\ stopped \in SUBSET (1..I)

Init ==
    /\ val = CHOOSE v \in V : TRUE
    /\ invBuf = {}
    /\ respBuf = {}
    /\ stopped = {}

-------------------------------------------------------------------------------

Dummy(i) == 
    /\ i \in stopped
    /\ UNCHANGED vars

Stop(i) ==
    /\ stopped' = stopped \union {i}
    /\ UNCHANGED <<val, invBuf, respBuf>>

Resp(i, b) == 
    /\ respBuf # {}
    /\ <<i,b>> \in respBuf
    /\ respBuf' = respBuf \ {<<i,b>>}
    /\ UNCHANGED <<val, invBuf, stopped>>

Inv(i, a) == 
    /\ invBuf' = invBuf \union  {<<i,a>>}
    /\ UNCHANGED <<val, respBuf, stopped>>

Perform(i, v) == 
    /\ invBuf # {}
    /\ <<i,v>> \in invBuf
    /\ invBuf' = invBuf \ {<<i,v>>}
    /\ val' = v
    /\ respBuf' = respBuf \union {<<i,v>>}
    /\ UNCHANGED <<stopped>>

-------------------------------------------------------------------------------

Next == 
    \E i \in 1..I:
        \/ Dummy(i)
        \/ Stop(i)
        \/ LET v == CHOOSE v \in V : TRUE
            IN  Inv(i,v) \/ Resp(i,v) \/ Perform(i,v)

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Mon Jun 19 08:38:00 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
