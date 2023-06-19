------------------------------ MODULE ReliableReorderingChannel ------------------------------
(* ReliableReorderingChannel algorithm - Distributed Algorithms by Nancy Lynch - p.460 *)
EXTENDS Integers, Sequences
CONSTANTS M
VARIABLES channel

vars == <<channel>>


TypeOK ==
    /\ channel \in Seq(M)

Init ==
    /\ channel = << >>

-------------------------------------------------------------------------------

\* Return the set of indexes where "x" occurs in "seq"
RECURSIVE Indexes(_,_,_) 
Indexes(x, i, seq) ==
    \* empty sequence
    IF Len(seq) = 0
    THEN {}
    ELSE \* have processed all indexes
        IF i > Len(seq)
        THEN {}
        ELSE \* normal index
            IF seq[i] = x
            THEN {i} \union Indexes(x, i+1, seq)
            ELSE Indexes(x, i+1, seq)

\* remove the i'ith element of "seq"
\* ref: AB.tla
RemoveIdx(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]


Remove(x, seq) == 
    LET idxs == Indexes(x, 1, seq)
        idx == CHOOSE v \in idxs : TRUE
    IN RemoveIdx(idx, seq)

-------------------------------------------------------------------------------

\* reliable send adds each message "m" to "channel"
Send(m) ==
    /\ channel' = Append(channel, m)

\* reordering property picks a nondeterministic message "m" to recieve from
\* the "channel", but it's not FIFO, so it doesn't have to be the first element
Receive(m) ==
    /\ \E i \in 1..Len(channel):
        channel[i] = m
    /\ LET i == CHOOSE i \in 1..Len(channel) : TRUE
        IN channel' = Remove(channel[i], channel)

Next ==
    \E m \in M:
        \/ Send(m)
        \/ Receive(m)

Spec == Init /\ [][Next]_<<vars>>

FairSpec == Spec /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Wed Jun 14 08:56:47 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
