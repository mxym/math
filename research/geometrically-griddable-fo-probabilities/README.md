# Exactly which first-order probabilities occur in geometric grid classes?

**Yongxian Zhang · research draft · 19 November 2026.** Let an infinite hereditary class of permutations fit in a fixed geometric grid. Choose a permutation uniformly from the class at each size, **without remembering its gridding**. If the class has exponential growth rate $r>1$, then the limits of probabilities of first-order sentences in the two orders are exactly
$$\mathbb Q(r)\cap[0,1].$$
Thus for integer growth the spectrum consists of all rational numbers in the unit interval; for nonrational growth it is the corresponding algebraic field interval. Each target has its own finite sentence. The limiting probability of a specified sentence can also be computed from a supplied geometric presentation and finite relative basis.

[Convergence](CONVERGENCE.md) uses the unambiguous primitive automaton from the [companion shape theorem](../geometrically-griddable-permutation-limit-shapes/SHAPES.md), here called SHAPES. [The field upper bound and a direct density proof](DENSITY.md) use rational enumeration and definable canonical prefixes. [Exact attainability](EXACT.md) reconstructs the full edge path in first-order logic, builds equally likely outcomes without counting an unbounded number of steps modulo anything, and realizes every target using a fixed number of coin trials and an independent finite die.

The polynomial case is different: its exact finite spectrum is due to Falgas-Ravry, Markström, Räty and Skerman. Their small exponential-class result is density, not exact attainment; Markström and Räty had already proved convergence for small classes. A fixed geometric grid can have arbitrarily large growth. No result for all proper classes, all small classes outside this hypothesis, or other logics is asserted here. [Sources and comparison](SOURCES.md) distinguish these results and the underlying word, trace and simulation techniques.

The proofs and the [initial](REVIEW.md) and [exact-attainment](EXACT-REVIEW.md) checks are AI-assisted and internally reviewed, not externally peer reviewed. No priority guarantee. From this directory the finite sanity checks (not proofs of an infinite statement) use Python's standard library:
```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
