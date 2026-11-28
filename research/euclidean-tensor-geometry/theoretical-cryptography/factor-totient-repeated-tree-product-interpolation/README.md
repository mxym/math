# Reconstructing repeated prime trees by product interpolation

Given an odd integer N and its exact numerical totient T, draw p -> q on its prime support if p divides q-1. Under fixed bounds on the number and size ratio of the primes, suppose its components are copies of a common rooted tree, with the same edge multipliers q=m p+1 and node multiplicities at corresponding positions. Only the root values differ. The tree, multipliers, roots, multiplicities and the correspondence are not supplied.

The profile blocks of (N,T) give positive **products** of values of a single monic polynomial whose roots are the component roots. An additional exact value is recovered at 1. A finite sign test on rational sample points can force this polynomial to be unique and give complete deterministic polynomial-bit-time factorization. Pairwise disjoint intervals give one simple sufficient test, but a 35-prime, five-tree example passes the full sign test without passing that interval criterion. Both that example and the smaller examples have valuation incidence rank one.

The theorem is conditional on a specified structure and on passing the stated sign certificate, not a claim about all repeated trees or factorization from N alone. Purely finite fixtures do not establish an infinite family or positive density.
```
python3 -B verify_prime_data.py
python3 -B verify_signs.py
```
The two exact standard-library checkers examine the arithmetic identities and the sign bound separately; neither is a general factoring program.
