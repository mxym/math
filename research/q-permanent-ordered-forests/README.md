# The q-permanent of an arbitrarily ordered forest

[Proof](proof.md) · [Internal review and verification](REVIEW.md)

For a Hermitian positive semidefinite matrix, the off-diagonal entries specify a graph; their positions specify an ordering. If that graph is a forest, the diagonal is positive, and at least one edge is present, its $q$-permanent is strictly increasing for $-1\le q<\infty$. Edges may cross in the given ordering. For each **positive definite, non-diagonal** such matrix the interval extends a little to the left of $-1$. The extension cannot be chosen uniformly, even in dimension four.

**What is different here?** [Da Fonseca's 2005 Theorem 4.3](https://doi.org/10.1080/03081080500092372) already stated the tree result on $[-1,1]$. The original proof identities do not hold for all orderings; the [author's corrected condition](https://arxiv.org/html/1804.02231#S3) excludes interleaved disjoint edges. The present proof keeps the original labels and treats the crossing terms through a probability of avoiding events. Its inversion-count identity is a special case of [Marques de Sá's 2019 paper](https://doi.org/10.1016/j.laa.2018.09.027), not a new permutation statistic.

**Scope.** This does not resolve monotonicity for unrestricted real symmetric matrices on $[-1,1]$ or alter the known counterexamples for broader matrix classes. The argument and checks are AI-assisted. The review was a separate internal AI-assisted pass, not external peer review or formal verification. No worldwide priority claim is made.

**Reproduce the finite checks** from this directory:

```sh
python -B -O verify.py
python -B -O audit_independent.py
```

The first script uses only the Python standard library. The second uses SymPy. The tests include interleaved pairs and singular complex matrices; the general theorem rests on the written proof.
