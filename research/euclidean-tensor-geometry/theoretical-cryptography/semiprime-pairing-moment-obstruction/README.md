# Low-degree moment collisions for pairings of the same primes

For every r there are edge-disjoint perfect matchings of one set of distinct primes whose squarefree semiprime block lists share the same product and the same first r power sums. There are O(r^2) blocks, and the block values can be arbitrarily close in relative size. The exact prime list may be provided to the observer; it still does not identify the hidden pairing.

This is a grouped-divisor nonidentifiability theorem, not a lower bound for integer factorization. The prime factorization of the common product is unique. See PROOF.md for the complete statement and UPSTREAM.md for the distinction from classical equal-product Prouhet–Tarry–Escott work.

Both checkers use only fixed data and exact arithmetic:

```sh
sha256sum -c SHA256SUMS
python3 -B verify_symbolic.py
python3 -B verify_prime_fixture.py
```
