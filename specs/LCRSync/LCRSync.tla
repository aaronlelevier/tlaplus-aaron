------------------------------ MODULE LCRSync ------------------------------
(*
This is a directional ring of n processes or P where uid's are synchronously
passed around the ring 1x per round, each Pi performs the action:
- if Pi.receive(v) > Pi.u, save v (to send next round)
- if Pi.receive(v) < Pi.u, discard v
- if Pi.receive(v) = Pi.u, output "leader"

Pi, 1 <= i <= n state:
- i:
    desc: Pi index detePining its location in the ring
    domain: 1 <= i <= n
    initial: Pi.i
- u:
    desc: unique identifier
    domain: 1 <= i <= n
    initial: random and unique
- status:
    desc: leader identifier
    domain: {"unknown", "leader"}
    initial: "unknown"
- send:
    desc: stores uid's to be sent
    domain: 1 <= i <= n \union null
    initial: Pi.i
*)

EXTENDS Integers, Sequences, SequencesExt

CONSTANT P \* {a, b, c}

VARIABLE pState

\* computed
pSeq == SetToSeq(pState)
N == Len(pSeq)
null == CHOOSE n : n \notin N

\* Clockwise Neighbor
CN(i) ==
    IF i = N
    THEN pSeq[1]
    ELSE pSeq[N+1]

\* node with max v
Max(p) ==
    LET x ==
        CHOOSE i \in p : \A j \in p : pState[i].u > pState[j].u
    IN pState[x].u


TypeOK ==
    /\ pState \in [P -> [u: 1..10,
                         status: {"unknown", "leader"}]]


Init ==
    /\ pState = [r \in P |->
                    [u |-> 1..10, \* todo: rand unique val with domain 1..N
                     status |-> "unknown"]]


Send ==
    /\ \A p \in P : 
        pState[p].status # "leader"
    /\ \E i \in N : 
        j == CN(i)
        IF pSeq[i].u > pSeq[j].u
        THEN 
            pSeq[j].u = pSeq[i].u 

            pState' = [pState EXCEPT ![pSeq[j]] = "committed"]
        


Done ==
    \E p \in P : pState[p].status = "leader"

\* "Round"
Next == Send \/ Done

Spec == Init /\ [][Next]_<<pState>>


=============================================================================
\* Modification History
\* Last modified Sun Apr 30 08:07:14 PDT 2023 by aaronlelevier
\* Created Wed Feb 22 14:58:46 PST 2023 by aaronlelevier
