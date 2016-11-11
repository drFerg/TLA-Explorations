------------------------------- MODULE 2nodes -------------------------------

CONSTANT CLEAR, MOTION_EVENT, NETWORK_EVENT

CONSTANT FULL_LIGHT, HALF_LIGHT, OFF


(*
--algorithm nodes {
    variables a = CLEAR, b = CLEAR, c = CLEAR, alight = OFF, blight = OFF, clight = OFF, p = 0;
    
    (* Lights are arranged A B C *)
    process(NodeA = 0) {
        t0: while(TRUE) {
                await a /= CLEAR; (* Wait until A gets a msg *)
                if (a = MOTION_EVENT) {
                    alight := FULL_LIGHT;
\*                    clight := 50;
                    b := NETWORK_EVENT
                    }
                else alight := HALF_LIGHT;
                a := CLEAR;
            }               
    }
    
    process(NodeB = 1) {
        t1: while(TRUE) {
                await b /= CLEAR;
                if (b = MOTION_EVENT) {
                    blight := FULL_LIGHT;
                    a := NETWORK_EVENT
                    }
                else blight := HALF_LIGHT;
                b := CLEAR;
            }
    }
    
    process(NodeC = 2) {
        t2: while(TRUE) {
                await c /= CLEAR;
                if (c = MOTION_EVENT) {
                    clight := FULL_LIGHT;
\*                        alight := 50;
                    b := NETWORK_EVENT;
                    }
                else clight := HALF_LIGHT;
                c := CLEAR;
            }
    }
    
    process (Person1 = 3) {
        t3: while(TRUE) {
            await a = CLEAR /\ b = CLEAR /\ c = CLEAR;
            if (p = 0) {
                p := 1;
                a := MOTION_EVENT;
             } else if (p = 1) {
                p := 2;
                b := MOTION_EVENT;
             } else {
                p := 0;
                c := MOTION_EVENT;
             }
         }
     }
     
\*     process (Person1 = 3) {
\*        t3: while(TRUE) {
\*            await a = CLEAR /\ b = CLEAR /\ c = CLEAR;
\*            p := (p + 1) % 3;
\*            if (p = 0) {
\*                a := MOTION_EVENT;
\*             } else if (p = 1) {
\*                b := MOTION_EVENT;
\*             } else {
\*                c := MOTION_EVENT;
\*             }
\*         }
\*     }
\*     process (Time = 4) {
\*        t4: while(TRUE) {
            
}
*)
\* BEGIN TRANSLATION
VARIABLES a, b, c, alight, blight, clight, p

vars == << a, b, c, alight, blight, clight, p >>

ProcSet == {0} \cup {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ a = CLEAR
        /\ b = CLEAR
        /\ c = CLEAR
        /\ alight = OFF
        /\ blight = OFF
        /\ clight = OFF
        /\ p = 0

NodeA == /\ a /= CLEAR
         /\ IF a = MOTION_EVENT
               THEN /\ alight' = FULL_LIGHT
                    /\ b' = NETWORK_EVENT
               ELSE /\ alight' = HALF_LIGHT
                    /\ b' = b
         /\ a' = CLEAR
         /\ UNCHANGED << c, blight, clight, p >>

NodeB == /\ b /= CLEAR
         /\ IF b = MOTION_EVENT
               THEN /\ blight' = FULL_LIGHT
                    /\ a' = NETWORK_EVENT
               ELSE /\ blight' = HALF_LIGHT
                    /\ a' = a
         /\ b' = CLEAR
         /\ UNCHANGED << c, alight, clight, p >>

NodeC == /\ c /= CLEAR
         /\ IF c = MOTION_EVENT
               THEN /\ clight' = FULL_LIGHT
                    /\ b' = NETWORK_EVENT
               ELSE /\ clight' = HALF_LIGHT
                    /\ b' = b
         /\ c' = CLEAR
         /\ UNCHANGED << a, alight, blight, p >>

Person1 == /\ a = CLEAR /\ b = CLEAR /\ c = CLEAR
           /\ IF p = 0
                 THEN /\ p' = 1
                      /\ a' = MOTION_EVENT
                      /\ UNCHANGED << b, c >>
                 ELSE /\ IF p = 1
                            THEN /\ p' = 2
                                 /\ b' = MOTION_EVENT
                                 /\ c' = c
                            ELSE /\ p' = 0
                                 /\ c' = MOTION_EVENT
                                 /\ b' = b
                      /\ a' = a
           /\ UNCHANGED << alight, blight, clight >>

Next == NodeA \/ NodeB \/ NodeC \/ Person1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Nov 11 12:16:10 GMT 2016 by fergus
\* Created Thu Nov 03 13:51:12 GMT 2016 by fergus
