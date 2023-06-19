------------------------------ MODULE DieHard ------------------------------

EXTENDS Integers

VARIABLES big, small

TypeOK == 
    /\ big \in 0..5
    /\ small \in 0..3
    /\ big /= 4

Init == 
    /\ big = 0
    /\ small = 0
    

FillBig ==
    /\ big' = 5
    /\ small' = small

FillSmall ==
    /\ big' = big
    /\ small' = 3


EmptyBig ==
    /\ big' = 0
    /\ small' = small

EmptySmall ==
    /\ big' = big
    /\ small' = 0


SmallToBig == 
    IF big + small <= 5
    THEN 
        /\ big' = big + small
        /\ small' = 0
    ELSE
        /\ big' = 5
        /\ small' = big + small - 5 
    

BigToSmall == 
    IF big + small <= 3
    THEN
        /\ small' = big + small
        /\ big' = 0
    ELSE
        /\ small' = 3
        /\ big' = big + small - 3
        
Done ==
    /\ big = 4

Next ==
    \/ FillBig
    \/ FillSmall
    \/ EmptyBig
    \/ EmptySmall
    \/ BigToSmall
    \/ SmallToBig
    
    
Spec == Init /\ [][Next]_<<big, small>>

=============================================================================
\* Modification History
\* Last modified Tue May 23 08:28:05 PDT 2023 by aaronlelevier
\* Created Tue May 23 07:51:24 PDT 2023 by aaronlelevier
