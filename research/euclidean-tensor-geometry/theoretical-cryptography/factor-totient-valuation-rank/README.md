# Recovering prime-graph components from the rank of valuation classes

Given an odd integer N and the exact numeric value of phi(N), group its prime-power factors by the ratio v_p(phi(N))/v_p(N). Each whole group product is computable **without factoring N or phi(N)**. On a prime graph p -> q when p divides q-1, form a matrix: rows are these ratio classes, columns are graph components, entries sum the N-exponents of primes in that row and component.

**Result:** when the number of distinct primes and their largest/smallest ratio have fixed bounds, the complete prime factorization follows in deterministic polynomial bit time if this matrix has rank at least the number of components minus one. Unknown positive prime multiplicities are unbounded. The graph, matrix, classes of individual primes and factorization are not input; the rank is a promise on the true hidden data.

At full rank the proof constructs integer root intervals of polynomial width by rational arithmetic. At rank deficiency one, the exact class equations give a smooth curve near each candidate of relevant size; the exact Euler equation has strictly negative second derivative there. Finiteness is proved locally at every feasible point, not from a global assertion about the number of curves. Examples on five two-leaf trees require no exclusive class and include a genuinely rank-deficient matrix with no individually identifiable coordinate. A deficiency-two example shows what can fail for the continuous equations, not hardness of the integer problem.

```
python3 -B verify_profiles.py
python3 -B verify_curvature.py
```

Only Python's standard library and finite labelled inputs are used by the checkers. They are not implementations of the general factoring method. The statement assumes one exact totient value; it does not compute that value from N, estimate a density, or address any cryptosystem.
