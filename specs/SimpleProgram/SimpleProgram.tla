------------------------------ MODULE SimpleProgram ------------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"

Add1 == \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"

Next == Pick \/ Add1


=============================================================================
\* Modification History
\* Last modified Sat May 13 16:22:59 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
