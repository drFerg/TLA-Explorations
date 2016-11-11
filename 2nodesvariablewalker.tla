------------------------ MODULE 2nodesvariablewalker ------------------------
EXTENDS Integers
CONSTANT Position
CONSTANT CLEAR, MOTION_EVENT, NETWORK_EVENT

(*
--algorithm nodes {
    variables a = 0, b = 0, c = 0, alight = 0, blight = 0, clight = 0, p = 0;
    (* Lights are arranged A B C *)
    process(NodeA = 0) {
        t0: while(TRUE) {
                await a /= CLEAR; (* Wait until A gets a msg *)
                if (a = MOTION_EVENT) {
                    alight := 100;
\*                    clight := 50;
                    b := NETWORK_EVENT
                    }
                else alight := 50;
                a := CLEAR;
            }               
    }
    
    process(NodeB = 1) {
        t1: while(TRUE) {
                await b /= CLEAR;
                if (b = MOTION_EVENT) {
                    blight := 100;
                    a := NETWORK_EVENT
                    }
                else blight := 50;
                b := CLEAR;
            }
    }
    
    process(NodeC = 2) {
        t2: while(TRUE) {
                await c /= CLEAR;
                if (c = MOTION_EVENT) {
                    clight := 100;
\*                        alight := 50;
                    b := NETWORK_EVENT;
                    }
                else clight := 50;
                c := CLEAR;
            }
    }
    
    process (Person1 = 3) {
        t3: while(TRUE) {
            p := (p + 1) % 3;
            if (p = 0) {
                a := MOTION_EVENT;
             } else if (p = 1) {
                b := MOTION_EVENT;
             } else {
                c := MOTION_EVENT;
             }
         }
     }
}
*)
\* BEGIN TRANSLATION
VARIABLES a, b, c, alight, blight, clight, p

vars == << a, b, c, alight, blight, clight, p >>

ProcSet == {0} \cup {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ a = 0
        /\ b = 0
        /\ c = 0
        /\ alight = 0
        /\ blight = 0
        /\ clight = 0
        /\ p = 0

NodeA == /\ a /= CLEAR
         /\ IF a = MOTION_EVENT
               THEN /\ alight' = 100
                    /\ b' = NETWORK_EVENT
               ELSE /\ alight' = 50
                    /\ b' = b
         /\ a' = CLEAR
         /\ UNCHANGED << c, blight, clight, p >>

NodeB == /\ b /= CLEAR
         /\ IF b = MOTION_EVENT
               THEN /\ blight' = 100
                    /\ a' = NETWORK_EVENT
               ELSE /\ blight' = 50
                    /\ a' = a
         /\ b' = CLEAR
         /\ UNCHANGED << c, alight, clight, p >>

NodeC == /\ c /= CLEAR
         /\ IF c = MOTION_EVENT
               THEN /\ clight' = 100
                    /\ b' = NETWORK_EVENT
               ELSE /\ clight' = 50
                    /\ b' = b
         /\ c' = CLEAR
         /\ UNCHANGED << a, alight, blight, p >>

Person1 == /\ p' = (p + 1) % 3
           /\ IF p' = 0
                 THEN /\ a' = MOTION_EVENT
                      /\ UNCHANGED << b, c >>
                 ELSE /\ IF p' = 1
                            THEN /\ b' = MOTION_EVENT
                                 /\ c' = c
                            ELSE /\ c' = MOTION_EVENT
                                 /\ b' = b
                      /\ a' = a
           /\ UNCHANGED << alight, blight, clight >>

Next == NodeA \/ NodeB \/ NodeC \/ Person1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Nov 08 14:42:08 GMT 2016 by fergus
\* Created Thu Nov 03 14:57:33 GMT 2016 by fergus
