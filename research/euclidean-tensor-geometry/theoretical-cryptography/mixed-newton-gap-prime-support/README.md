# Newton-gap correspondences on connected prime supports

A public length-dependent list gives exact, possibly mixed bivariate relations. Each has two pure leading monomials, a certified weighted gap below them, and a degree ratio in one fixed rational cyclic group. If the graph of these relations on the distinct prime factors of an integer is connected, the complete prime product is recognizable in deterministic polynomial bit time from the integer alone, without a supplied edge or a fixed bound on support size or multiplicities.

This is a mathematical promise class, not a general factorization claim. It extends the preceding separated monic catalogue: a weighted coefficient certificate gives the uniform error estimate even when the polynomial has mixed terms or exponentially large coefficients. The fixed irreducible example shows a genuine difference of correspondence models, not a claim about a density of prime points.

`PROOF.md` is a self-contained statement and proof, with `UPSTREAM.md` for prior work. Checkers verify only fixed arithmetic identities and toy fixtures; they are not a factorization implementation.

```sh
sha256sum -c SHA256SUMS
python3 -B verify_gap.py
python3 -B verify_fixture.py
```
