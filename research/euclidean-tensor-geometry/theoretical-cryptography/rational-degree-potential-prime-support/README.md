# A rational degree potential on connected prime supports

Fix a rational ratio `lambda > 1`. A public, polynomially bounded catalogue gives pairs of monic integer polynomials with degree ratios in `lambda^Z` and roots in a common polynomial-radius disk. Consider products of primes whose distinct support is connected by exact equalities of values of catalogue pairs.

For this promised class, only the product is input. An additive localization theorem with an explicitly bounded list of rational exponents gives deterministic polynomial bit complexity, with no bound fixed in advance on the number of distinct factors or their multiplicities. Connectivity and the full prime product are checked. The result concerns this particular mathematical class, not unrestricted factorization, any cryptosystem, or recovery at actual targets.

Relative to the adjacent repository notes, the change is specifically the conjunction of nonlinear separated relations and no fixed support size: the aggregate is a rational degree sum on a logarithmic coordinate, not an affine scale or a hidden sparse-span certificate. The fixed cyclic group of degree quotients is still a global public restriction.

`PROOF.md` gives the complete abstraction; `UPSTREAM.md` separates the classical ingredients and nearby results. Both checkers are fixed finite arithmetic verifications, not implementations of the recognizer or factorization procedure.

```sh
sha256sum -c SHA256SUMS
python3 -B verify_fixture.py
python3 -B verify_lattice.py
```
