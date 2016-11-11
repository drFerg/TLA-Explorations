---------------------------- MODULE coffeebeans ----------------------------
EXTENDS Integers
CONSTANTS W, B

ASSUME /\ W \in Nat \ {0}
       /\ B \in Nat \ {0}

(*
--algorithm coffeebeans {
    variables b \in 1..B, w \in 1..W; {
    
    while (b + w > 1) {
        either { (* 2 B beans, replace with W *)
            await b >= 2;
            b := b - 2;
            w := w + 1;
        }
        or { (* 2 W beans, replace with W *)
            await w >= 1;
            w := w - 1;
        }
        or { (* 1 W + 1B , replace with B *)
           await w >= 1 /\ b >= 1;
           w :=  w - 1;
        }
    }
    }
}
*)

\* BEGIN TRANSLATION
VARIABLES b, w, pc

vars == << b, w, pc >>

Init == (* Global variables *)
        /\ b \in 1..B
        /\ w \in 1..W
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF b + w > 1
               THEN /\ \/ /\ b >= 2
                          /\ b' = b - 2
                          /\ w' = w + 1
                       \/ /\ w >= 1
                          /\ w' = w - 1
                          /\ b' = b
                       \/ /\ w >= 1 /\ b >= 1
                          /\ w' = w - 1
                          /\ b' = b
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << b, w >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
inv == b >= 0


=============================================================================
\* Modification History
\* Last modified Tue Nov 08 11:18:43 GMT 2016 by fergus
\* Created Tue Nov 08 10:19:43 GMT 2016 by fergus
