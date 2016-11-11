------------------------------- MODULE 2jugs -------------------------------

EXTENDS Integers

VARIABLES big, small
TypeOK == /\ big \in 0..5
          /\ small \in 0..3
          
FourGallons == big /= 4 \/ small /= 1

Min(m, n) == IF m < n THEN m ELSE n

Init == /\ big = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big
             
FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big
EmptyBig == /\ big' = 0
            /\ small' = small

BigtoSmall == /\ small' = Min(big + small, 3)
              /\ big' = big - (small' - small)

SmalltoBig == /\ big' = Min(small + big, 5)
              /\ small' = small - (big' - big)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ BigtoSmall
        \/ SmalltoBig
        





=============================================================================
\* Modification History
\* Last modified Fri Oct 28 15:18:21 BST 2016 by fergus
\* Created Fri Oct 28 10:24:28 BST 2016 by fergus
