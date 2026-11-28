# Counting integers with no small component in their prime support

Fix an integer s≥2. Unlike a connectivity condition, this local condition permits arbitrarily many separate components, but every component of the graph induced on the distinct prime divisors must contain at least s vertices. Multiplicities of the primes are arbitrary.

* With maximum graph degree O(L^d) at binary length L, the sharp universal logarithmic counting exponent is max(1/s,d/(1+d)).
* Joining primes by *ordinary numerical distance* ≤H(L) attains exactly that exponent for every d≥0 whenever H(L)→∞ and log H(L)/log L→d. For s=2 this means each prime factor needs at least one other nearby prime factor. Empty bins between clusters cause no obstruction.
* For a fixed numerical distance H, the upper logarithmic exponent is exactly 1/s times the upper logarithmic exponent of the set of primes starting a length-s bounded-gap cluster. Thus the size of the very narrow case is not inferred from the growing-width result. In particular, H=s=2 relates precisely to, but does not resolve, a twin-prime counting question.

PROOF.md gives the quantifiers and proofs; UPSTREAM.md locates the quantitative input of Maynard and the preceding connected-support theorem. The two scripts verify fixed finite combinatorial and enumerative identities only. This is a counting result; it has no recovery algorithm, cryptographic object, or computational-security claim.
