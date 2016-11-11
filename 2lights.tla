------------------------------ MODULE 2lights ------------------------------

EXTENDS Integers

VARIABLES lightA, lightB, lightC

TypeOK == /\ lightA \in 0..100
          /\ lightB \in 0..100
          /\ lightC \in 0..100
          
Check == \/ lightA /= 50
         \/ lightB /= 50
         \/ lightC /= 50
         
Init == /\ lightA = 0
        /\ lightB = 0
        /\ lightC = 0

trigA == /\ lightA' = 100
         /\ lightB' = 50
         /\ lightC' = lightC
         
trigB == /\ lightB' = 100
         /\ IF lightC = 100 
            THEN lightA' = 50 /\ lightC' = lightC 
            ELSE lightC' = 50 /\ lightA' = lightA

trigC == /\ lightC' = 100
         /\ lightB' = 50
         /\ lightA' = lightA

Next == \/ trigA
        \/ trigB
        \/ trigC
        \/ trigA /\ trigC
        \/ trigA /\ trigB /\ trigC

=============================================================================
\* Modification History
\* Last modified Fri Oct 28 14:55:26 BST 2016 by fergus
\* Created Fri Oct 28 13:49:03 BST 2016 by fergus
