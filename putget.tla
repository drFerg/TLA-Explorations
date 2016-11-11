------------------------------- MODULE putget -------------------------------
EXTENDS Sequences

Put(s) == Append(s, "item")
Get(s) == Tail(s)



        
=============================================================================
\* Modification History
\* Last modified Thu Nov 03 13:34:43 GMT 2016 by fergus
\* Created Thu Nov 03 13:24:01 GMT 2016 by fergus
