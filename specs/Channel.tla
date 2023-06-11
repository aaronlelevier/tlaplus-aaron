------------------------------ MODULE Channel ------------------------------
\* Channel I/O automata - Distributed Algorithms by Nancy Lynch - p.204

EXTENDS Integers, Sequences

CONSTANTS M

VARIABLES queue

vars == <<queue>>

\* bounded queue size is required or the queue size will grow indefinitely
maxQueueSize == 3

TypeOK ==
    /\ queue \in Seq(M)

Init ==
    /\ queue = << >>

Send(m) ==
    IF Len(queue) < maxQueueSize
    THEN queue' = Append(queue, m)
    ELSE UNCHANGED queue

Receive(m) ==
    /\ queue # << >>
    /\ IF Head(queue) = m 
        THEN queue' = Tail(queue)
        ELSE UNCHANGED queue

Next ==
    \E m \in M:
        \/ Send(m) 
        \/ Receive(m)

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Sat Jun 10 16:14:16 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
