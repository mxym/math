# Prior art and exact scope

## Randomized factoring from exponent information

François Morain, Guénaël Renault, and Benjamin Smith,
**“Deterministic factoring with oracles,”** arXiv:1802.08444v2 (2021),
especially §2.3 and Appendix A, Algorithms 7–9:
[https://arxiv.org/abs/1802.08444](https://arxiv.org/abs/1802.08444).

They record the standard efficient randomized reduction from exact
\(\lambda(N)\) (and related oracles) to factorization, using an even
annihilating exponent and nontrivial square roots of \(1\).

The present note's additional reduction is elementary but explicit:
complete prime-support advice alone synthesizes a factored multiple
\(E\) of \(\lambda(N)\), even though neither the value nor the
prime-power exponents of \(\lambda(N)\) are supplied. The proof also
records the exact CRT law and a uniform \(1/2\) unit-trial failure
bound after repeated-prime stripping.

## Repository context

* Commit 4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc gives a deterministic
  unconditional bound from the same support promise.
* Commit 3c4258ea82dd571c4ddfedb077103af82685cfb7 improves the general
  deterministic bound to \(L_N[2/3,1+o(1)]\).
* Commit 42c47a10dc003b30ac1725826503b096662c904e gives deterministic
  polynomial time under GRH.

This package is instead unconditional and randomized.

## Limits

* Every actual prime divisor of \(\lambda(N)\) must be included in the
  advice list. False positives are harmless, omissions are not.
* The advice entries themselves must be genuine primes and are
  validated.
* The result is Las Vegas expected polynomial time, not deterministic
  polynomial time.
* It makes no claim about recovering the support from \(N\).
* No claim of absolute historical priority is made.
