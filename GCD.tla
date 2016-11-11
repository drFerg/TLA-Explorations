-------------------------------- MODULE GCD --------------------------------
EXTENDS Integers

Divides(p, n) == \E q \in Int : n = q * p
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax( DivisorsOf(m) \cap DivisorsOf(n))
=============================================================================
\* Modification History
\* Last modified Tue Nov 01 13:44:47 GMT 2016 by fergus
\* Created Tue Nov 01 11:39:53 GMT 2016 by fergus
