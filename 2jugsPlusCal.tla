---------------------------- MODULE 2jugsPlusCal ----------------------------
EXTENDS Integers

Min(m, n) == IF m < n THEN m ELSE n

(*
--algorithm DieHard { 
    variables big = 0, small = 0 ; {
    while(TRUE) {
        either small := 3;
        or     big := 5;
        or     small := 0;
        or     big := 0;
        or with (poured = Min(big + small, 5) - big) {
            big := big + poured;
            small := small - poured;
        }
        or with (poured = Min(big + small, 3) - small) {
            big := big - poured;
            small := small + poured;
        }
    }
} }
*)
\* BEGIN TRANSLATION
VARIABLES big, small

vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Next == \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ LET poured == Min(big + small, 5) - big IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min(big + small, 3) - small IN
                /\ big' = big - poured
                /\ small' = small + poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Oct 31 17:18:38 GMT 2016 by fergus
\* Created Mon Oct 31 16:54:35 GMT 2016 by fergus
