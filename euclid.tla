------------------------------- MODULE euclid -------------------------------
EXTENDS Integers, GCD

CONSTANTS M, N

ASSUME /\ M \in Nat \ {0}
       /\ N \in Nat \ {0}
       
    
(******
--algorithm Euclid {
     variables x \in 1 .. N, y \in 1 .. N, x0 = x, y0 = y; {
        while(x # y) {
            if (x < y) y := y - x;
            else       x := x - y;
        }
     }
     
}

*******)


\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1 .. N
        /\ y \in 1 .. N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
partialCorrectness == (pc = "Done") => (x = y) /\ (x = GCD(M, N))

=============================================================================
\* Modification History
\* Last modified Tue Nov 01 13:55:23 GMT 2016 by fergus
\* Created Tue Nov 01 11:31:27 GMT 2016 by fergus
