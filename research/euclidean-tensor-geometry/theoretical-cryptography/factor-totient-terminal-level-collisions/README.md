# Factoring from one totient using multiplicity classes of terminal primes

For an odd integer N and its exact numeric totient, draw p -> q between its distinct prime divisors when p divides q-1. In the bounded-ratio, bounded-support setting, its terminal vertices are precisely the primes visible in the reduced denominator of phi(N)/N. This note uses their exact multiplicities in N: the product of the terminal primes in each multiplicity class can be recovered without factoring.

Assume the terminal primes in each graph component all have the same multiplicity. A multiplicity class may be used by one or two components, and at most two classes may be used by two. When two classes are shared, at least one of the four components sharing them must have an edge. Then the **entire factorization of N**, including arbitrary unknown positive multiplicities, is determined in deterministic polynomial bit time **given N and the single numeric value phi(N)**. The assignment of classes, the graph, primes, exponents and their order are not given. No assumption is made that N alone supplies its totient.

A class used by one component determines its root by a monotone polynomial. Two shared classes leave four roots; the main proof resolves all possible placements of the nontrivial trees among the two pairs. An edge only in a component already peeled is not enough for this four-root proof. There is a finite prime example showing why the remaining all-isolated case is excluded from the complex-fiber argument.

```
python3 -B verify_layers.py
python3 -B verify_boundary.py
```

Both checkers use Python's standard library, known fixtures and exact arithmetic. They are not factoring implementations or timing experiments. Read PROOF.md for the proof and UPSTREAM.md for sources, including the earlier three-component result, classical graph and gcd ingredients, and the fixed-variable algebraic decision theorem. No density or infinitude is claimed.
