# Removing unknown multiplicities from a clustered one-totient problem

Input: an integer N and its **exact numeric** Euler totient T. Output of the main theorem: the pair (rad N, phi(rad N)), **not** a factorization of rad N. No totient oracle is queried. Distinct prime divisors of N have a fixed bounded ratio; the sources of totient cross-divisibilities may be in an unknown interval of width P^(4/k-epsilon), where P is the least *distinct* prime and k is a fixed upper bound on their number. All positive multiplicities are unknown and may be unbounded. The no-source and single-source cases do not require comparability. This is a promise reduction, not ordinary factoring from N alone.

The proof uses the published *univariate* small-root theorem as an explicit black box. Its width bound is sufficient, not claimed optimal. In applications, compose with a separate squarefree theorem; the reduction preserves the distinct primes and their locations exactly. In particular an already-proved conditional two-cluster result may be composed as described at the end of PROOF.md; it is not required to prove anything else in this package.

Run with Python 3, standard library only:
```
python3 verify_support.py
python3 verify_paths.py
```
The first checker exhausts a finite set of prime supports and multiplicities; the second independently checks residual sets, terminal affine paths and exact integer inequalities on finite known-prime fixtures. Neither replaces the analytic argument or implements a lattice solver. No external datasets. See UPSTREAM.md for priority/scope and RESULTS.txt for replay.
