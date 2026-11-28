# How many integers have connected prime support?

For each input length L, draw any simple graph on the rational primes of maximum degree O(L^d). Count n≤X having at least two distinct prime factors whose set induces a connected subgraph of the graph for n's own bit length. The largest possible logarithmic counting exponent is exactly
    max(1/2, d/(1+d)).
This holds for every fixed real d≥0, including arbitrary multiplicities; no computability condition on the family of graphs is needed. A matching gives the extremal power for d≤1. A window in the index ordering of primes gives it for d>1. These are extremal examples, not lower bounds for every graph.

For the concrete arithmetic graph joining primes whose *values* differ by at most L^c, the count is X^(c/(1+c)+o(1)) for every positive integer c. The lower bound uses PNT for c=1 and a prime scaffold for c≥2. At c=0 only support {2,3} occurs. See PROOF.md for the upper error, the short-interval dependence for real c, and the distinction between the two types of windows.

This package is purely enumerative. It provides neither a factorization nor a recognition algorithm. The fixed scripts check a finite graph encoding and exact small counts by two independent finite enumerations; they are not evidence for a limiting exponent. Run `python3 verify_forests.py` and `python3 verify_counts.py`.
