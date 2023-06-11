------------------------------ MODULE Bakery ------------------------------
(* Bakery algorithm - Distributed Algorithms by Nancy Lynch - p.297

    try-i
    choosing(i) := 1
    number(i) := 1 + max j#i number(j)
    choosing(i) := 0
    for j # i:
    waitfor choosing(j) = 0
    waitfor number(j) = 0 or (number(i),i) < (number(j),j)

    crit-i

    exit-i
    number(i) := 0

    rem-i

The model will eventually error when it violates the max "number" TypeOK
invariant, and this behavior is expected because this algorithm uses
unbounded size registers.

*)
EXTENDS Integers
CONSTANTS I
VARIABLES choosing, number, iState

vars == <<choosing, number, iState>>

states == {"try", "crit", "exit", "rem"}

TypeOK ==
    /\ choosing \in [I -> {0,1}]
    /\ number \in [I -> (0..3)] 
    /\ iState \in [I -> states]

Init ==
    /\ choosing = [i \in I |-> 0]
    /\ number = [i \in I |-> 0]
    /\ iState = [i \in I |-> "rem"]

-------------------------------------------------------------------------------

Rem(i) ==
    /\ iState[i] = "rem"
    /\ iState' = [iState EXCEPT ![i] = "try"]
    /\ UNCHANGED <<choosing, number>>

-------------------------------------------------------------------------------

SetChoose(i) == 
    /\ iState[i] = "try"
    /\ choosing[i] = 0
    /\ choosing' = [choosing EXCEPT ![i] = 1]
    /\ UNCHANGED <<number, iState>>

Max(J) ==
    CHOOSE n \in {number[j] : j \in J} : ( \A j \in J : n >= number[j] )

GetNumber(i) == 
    /\ iState[i] = "try"
    /\ choosing[i] = 1
    /\ number[i] = 0
    /\ number' = [number EXCEPT ![i] = Max(I \ {i}) + 1]
    /\ UNCHANGED <<choosing, iState>>

UnSetChoose(i) == 
    /\ iState[i] = "try"
    /\ choosing[i] = 1
    /\ number[i] # 0
    /\ choosing' = [choosing EXCEPT ![i] = 0]
    /\ UNCHANGED <<number, iState>>

EnterCrit(i) ==
    /\ iState[i] = "try"
    /\ number[i] # 0
    /\ choosing[i] = 0
    /\ \A j \in I \ {i}:
        /\ choosing[j] = 0
        /\ number[j] = 0 
            \/ (IF number[i] = number[j] 
                THEN i < j
                ELSE number[i] < number[j])
    /\ iState' = [iState EXCEPT ![i] = "crit"]
    /\ UNCHANGED <<choosing, number>>


Try(i) ==
    \/ SetChoose(i)
    \/ GetNumber(i)
    \/ UnSetChoose(i)
    \/ EnterCrit(i)

-------------------------------------------------------------------------------

Crit(i) ==
    /\ iState[i] = "crit"
    /\ iState' = [iState EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<choosing, number>>

-------------------------------------------------------------------------------

Exit(i) ==
    /\ iState[i] = "exit"
    /\ number' = [number EXCEPT ![i] = 0]
    /\ iState' = [iState EXCEPT ![i] = "rem"]
    /\ UNCHANGED <<choosing>>

-------------------------------------------------------------------------------

Next ==
    \E i \in I:
        \/ Rem(i)
        \/ Try(i)
        \/ Crit(i)
        \/ Exit(i)

Spec == Init /\ [][Next]_<<vars>>

-------------------------------------------------------------------------------

ME == 
    ~ \E i, j \in I:
        /\ i # j
        /\ iState[i] = "crit"
        /\ iState[j] = "crit"

=============================================================================
\* Modification History
\* Last modified Sat Jun 10 18:16:04 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
