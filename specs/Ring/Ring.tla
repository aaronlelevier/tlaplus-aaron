------------------------------ MODULE Ring ------------------------------
(*
Ring of nodes where each index unique from 1..N where N is the ring size
*)

EXTENDS Integers

CONSTANT N

Node == 0 .. N-1
Status == {"unknown", "leader"}

VARIABLE 
    value,
    index,
    status

vars == <<value, index, status>>

TypeOK ==
    /\ value \in [Node -> Nat]
    /\ index \in [Node -> Nat]
    /\ status \in [Node -> Status]

Init ==
    /\ value = [i \in Node |-> 1..N]
    /\ index = [i \in Node |-> 1..N]
    /\ status = [i \in Node |-> "unknown"]

    
\* Clockwise Neighbor
CN(i) ==
    IF i.index = N
    THEN index[1]
    ELSE index[N+1]

Step ==
    /\ \A i \in Node:
        status[i] # "leader"
    /\ \E i,j \in Node:
        IF index[i] < index[j]
        THEN
            IF value[i] > value[j]
            THEN 
                value' = [value EXCEPT ![j] = value[i]]

Done ==
    \E i \in Node : status[i] = "leader"

Next == Step \/ Done

Spec == Init /\ [][Next]_<<vars>>


=============================================================================
\* Modification History
\* Last modified Sun Apr 30 08:07:14 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
