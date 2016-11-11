----------------------------- MODULE 2morejugs -----------------------------
EXTENDS Integers
Min(m, n) == IF m < n THEN m ELSE n

CONSTANTS Goal, Jugs, Capacity

ASSUME /\ Goal \in Nat
       /\ Capacity \in [Jugs -> Nat \ {0}]

(*
--algorithm 2morejugs {
    variables injug = [j \in Jugs |-> 0]; (* Init all jugs to 0 *)
    {
        while(TRUE) {
            either with (j \in Jugs) { injug[j] := Capacity[j]}
            or with (j \in Jugs) { injug[j] := 0}
            or with (j \in Jugs, k \in Jugs \ {j}) {
                with (poured = Min(injug[j] + injug[k], Capacity[k]) - injug[k]) {
                    injug [j ] := injug [j ] - poured || (* Allows it to change a var twice in one step *)
                    injug[k] := injug[k] + poured;
                    }
        }
    }}}
*)
\* BEGIN TRANSLATION
VARIABLE injug

vars == << injug >>

Init == (* Global variables *)
        /\ injug = [j \in Jugs |-> 0]

Next == \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = Capacity[j]]
        \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = 0]
        \/ /\ \E j \in Jugs:
                \E k \in Jugs \ {j}:
                  LET poured == Min(injug[j] + injug[k], Capacity[k]) - injug[k] IN
                    injug' = [injug EXCEPT ![j ] = injug [j ] - poured,
                                           ![k] = injug[k] + poured]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Wed Nov 02 19:47:34 GMT 2016 by fergus
\* Created Wed Nov 02 19:33:15 GMT 2016 by fergus
