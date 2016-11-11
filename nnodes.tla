------------------------------- MODULE nnodes -------------------------------
EXTENDS Integers, Sequences

CONSTANT FULL_LIGHT, HALF_LIGHT, OFF

CONSTANT NODES


(*
--algorithm nnodes {
    variables NO_EVENT = 0, MOTION_EVENT = 1, NETWORK_EVENT = 2, 
    EVENTS = {MOTION_EVENT, NETWORK_EVENT}, p = 0, 
    events = [n \in 0..NODES |-> 0], 
    light = [n \in 0..NODES |-> 0], 
    allClear = [n \in 0..NODES |-> 0] ;
    
    macro send(node, event) {
        events[node] := event;
    }
    
    macro actuate(device, id, action) {
        device[id] := action;
    }
    
    macro wait_on_event(id) {
        await events[id] /= NO_EVENT;
    }
    
    (* Lights are arranged 0 - 1 - 2 - n *)
    process (Nodes \in 0..NODES) {
        procThread: while(TRUE) {
                wait_on_event(self); (* Wait until you get a msg *)
                if (events[self] = MOTION_EVENT) {
                    actuate(light, self, FULL_LIGHT);
                    send(self+1, NETWORK_EVENT);
                }
                else if (events[self] = NETWORK_EVENT) {
                    actuate(light, self, HALF_LIGHT);
                };
                clear: events[self] := NO_EVENT;
            }               
    }
  
    process (Person1 = NODES + 1) {
        t3: while(TRUE) {
            await events = allClear;
            p := (p + 1) % NODES;
            send(p, MOTION_EVENT);
         }
     }
               
}
*)
\* BEGIN TRANSLATION
VARIABLES NO_EVENT, MOTION_EVENT, NETWORK_EVENT, EVENTS, p, events, light, 
          allClear, pc

vars == << NO_EVENT, MOTION_EVENT, NETWORK_EVENT, EVENTS, p, events, light, 
           allClear, pc >>

ProcSet == (0..NODES) \cup {NODES + 1}

Init == (* Global variables *)
        /\ NO_EVENT = 0
        /\ MOTION_EVENT = 1
        /\ NETWORK_EVENT = 2
        /\ EVENTS = {MOTION_EVENT, NETWORK_EVENT}
        /\ p = 0
        /\ events = [n \in 0..NODES |-> 0]
        /\ light = [n \in 0..NODES |-> 0]
        /\ allClear = [n \in 0..NODES |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 0..NODES -> "procThread"
                                        [] self = NODES + 1 -> "t3"]

procThread(self) == /\ pc[self] = "procThread"
                    /\ events[self] /= NO_EVENT
                    /\ IF events[self] = MOTION_EVENT
                          THEN /\ light' = [light EXCEPT ![self] = FULL_LIGHT]
                               /\ events' = [events EXCEPT ![(self+1)] = NETWORK_EVENT]
                          ELSE /\ IF events[self] = NETWORK_EVENT
                                     THEN /\ light' = [light EXCEPT ![self] = HALF_LIGHT]
                                     ELSE /\ TRUE
                                          /\ light' = light
                               /\ UNCHANGED events
                    /\ pc' = [pc EXCEPT ![self] = "clear"]
                    /\ UNCHANGED << NO_EVENT, MOTION_EVENT, NETWORK_EVENT, 
                                    EVENTS, p, allClear >>

clear(self) == /\ pc[self] = "clear"
               /\ events' = [events EXCEPT ![self] = NO_EVENT]
               /\ pc' = [pc EXCEPT ![self] = "procThread"]
               /\ UNCHANGED << NO_EVENT, MOTION_EVENT, NETWORK_EVENT, EVENTS, 
                               p, light, allClear >>

Nodes(self) == procThread(self) \/ clear(self)

t3 == /\ pc[NODES + 1] = "t3"
      /\ events = allClear
      /\ p' = (p + 1) % NODES
      /\ events' = [events EXCEPT ![p'] = MOTION_EVENT]
      /\ pc' = [pc EXCEPT ![NODES + 1] = "t3"]
      /\ UNCHANGED << NO_EVENT, MOTION_EVENT, NETWORK_EVENT, EVENTS, light, 
                      allClear >>

Person1 == t3

Next == Person1
           \/ (\E self \in 0..NODES: Nodes(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Fri Nov 11 13:34:50 GMT 2016 by fergus
\* Created Fri Nov 11 12:16:31 GMT 2016 by fergus
