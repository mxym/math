# Sharp Bernoulli expand–accumulate distance tails over fixed commutative rings

The Bernoulli expand–accumulate ensemble of Boyle, Couteau, Gilboa,
Ishai, Kohl, Resch and Scholl has an exact reduction to the residue
fields of any fixed finite commutative ring. This reduction gives a
constant-rate distance theorem without a rate restriction involving
the size of the entire ring. However, the **same numerical failure
bound as the binary theorem does not extend**. The fixed ring
\(\mathbb Z/4\mathbb Z\) is already a counterexample.

In detail, let the ring have order \(Q\) and smallest residue-field
order \(q_*\), and write \(\zeta=Q/(Q-1)\). At entry density
\(C\ln N/N\), limiting rate \(\rho\), and target relative distance
\(0<\delta<1-1/q_*\), suppose \(\rho<1-H_{q_*}(\delta)\), where \(H_q\)
is the normalized \(q\)-ary entropy. Put
\[
 A=C\zeta\left(
       \sqrt{(1-1/q_*)(1-\delta)}-\sqrt{\delta/q_*}
              \right)^2.
\]
Then the distance failure probability tends to one if \(A<1\);
it tends to zero subpolynomially if \(A=1\); and if \(A>1\) its
exact logarithmic exponent is \(1-A\). The strict GV margin is
needed for the success statements, not for the one-row lower bound.

For \(\rho=1/100\), \(\delta=1/4\), and \(C=64\), the published
binary Theorem 3.10(5) bounds its failure by \(O(N^{-6})\). The
same parameters over \(\mathbb Z/4\mathbb Z\) give a failure exponent
of \(-4.716249439\ldots\) instead. This resolves the precise
same-probability extension formulated in
[AICR c/0086](https://aicr.info/c/0086/) in the negative, while proving
the qualitative positive rate statement over fixed commutative rings.
This is a theorem about sampled abstract generator matrices. It does
not assert failure or security of any cryptographic system.

Rindal (2026/2315) already proved the strict successful side of the
density/GV threshold over each fixed **field**, with the same
sparse constant. The present statements concern residue reduction,
the matching probability lower bound, the critical line, and the
fixed-ring discrepancy. See [PROOF.md](PROOF.md) and
[SOURCES.md](SOURCES.md) for the precise attributions and boundaries.

For exact checks on small rings and independent combinatorial and
spectral regressions, run `sh replay.sh | diff -u RESULTS.txt -`; the expected output is
[RESULTS.txt](RESULTS.txt).
