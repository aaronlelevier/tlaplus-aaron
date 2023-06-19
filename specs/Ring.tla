------------------------------ MODULE Ring ------------------------------
(*
Ring of nodes where each index unique from 1..N where N is the ring size
*)

EXTENDS Integers, FiniteSets

CONSTANT RM

N == Cardinality(RM)

VARIABLE rmState, values, indexes

vars == <<rmState, values, indexes>>

TypeOK ==
    /\ rmState \in [RM -> [
        index: 0..N,
        value: 0..N,
        status: {"unknown", "leader"}]]

Init ==
    /\ values = 1..N
    /\ indexes = 1..N 
    /\ rmState = [r \in RM |-> [
        index |-> 0,
        value |-> 0,
        status |-> "unknown"]]

-------------------------------------------------------------------------------

PostInit(r) ==
    /\ rmState[r].value = 0
    /\ LET 
        v == CHOOSE v \in values : TRUE
        i == CHOOSE i \in indexes : TRUE
        IN
        /\ values' = values \ {v}
        /\ indexes' = indexes \ {i}
        /\ rmState' = [rmState EXCEPT ![r].value = v,
                                   ![r].index = i]

-------------------------------------------------------------------------------
    
\* Clockwise Neighbor
CN(r) ==
    LET idx == IF rmState[r].index = N THEN 1 ELSE rmState[r].index + 1
    IN CHOOSE s \in RM : rmState[s].index = idx

Step(r) ==
    /\ \A s \in RM: \* PostInit has occurred for all RM
        rmState[s].value # 0
    /\ LET s == CN(r)
        IN 
            CASE rmState[s].value > rmState[r].value ->
                /\ UNCHANGED vars
            [] rmState[s].value < rmState[r].value ->
                /\ rmState' = [rmState EXCEPT ![s].value = rmState[r].value]
                /\ UNCHANGED <<values, indexes>>
            [] OTHER -> \* rmState[s].value = rmState[r].value
                /\ rmState' = [rmState EXCEPT ![s].status = "leader"]
                /\ UNCHANGED <<values, indexes>>

Done ==
    /\ \E r \in RM : 
        rmState[r].status = "leader"
    /\ UNCHANGED vars

Next ==
    \/ \E r \in RM: 
        \/ PostInit(r)
        \/ Step(r)
    \/ Done

Spec == Init /\ [][Next]_<<vars>>


=============================================================================
\* Modification History
\* Last modified Mon Jun 19 09:37:51 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
