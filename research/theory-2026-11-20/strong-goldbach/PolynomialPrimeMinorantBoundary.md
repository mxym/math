# A necessary zero-slope bound for pointwise prime minorants from the polynomial halves

Use \(H_k\) and its unshifted mean \(k\) as in the
[critical polynomial parity-halves theorem](midpoint_halves/Proof.md).
For fixed real coefficients write \(M=\sum_{k=2}^K c_k H_k\).
Suppose \(M(n)\le V(n)\) for all sufficiently large squarefree \(n\);
it is enough to require this for each compact positive prime-factor profile
asymptotically, with error \(o(\log n)\) along that profile.
Then **the ordinary calibrated mean is nonpositive**:
\[
                           \sum_{k=2}^K k c_k\le 0.
\]
This rules out a positive-mean, globally valid pure-prime minorant
through arbitrary finite degree; it does not rule out a localized
inequality for the actual joint factor profiles of \(n\) and \(P-n\).

Let \(R(z)=\sum_{k\ge3,\ k\text{ odd}}c_k z^k\). On three distinct primes
of exponents \(x_i=\log_n p_i\), the normalized matching-parity sum is
\(R(1)-\sum_iR(1-2x_i)\); this is complementary-divisor pairing or
the coefficient formula in the cited theorem.
Take \(x_1=e,\ x_2=x_3=(1-e)/2\), for any fixed \(0<e<1/4\).
These are actual limiting factor exponents of squarefree triprimes:
for \(Y\to\infty\) choose one prime in \([Y^e,2Y^e]\) and two distinct
ones in \([Y^{(1-e)/2},2Y^{(1-e)/2}]\), by ordinary PNT. If a central
target is required, take \(P=2n\), even, so \(n\in I\);
no reflected test condition is being imposed. By continuity,
\[
                   R(1)-R(1-2e)-2R(e)\le0 .
\]
Its left side equals \(2e R'(1)+O_R(e^2)\), since \(R'(0)=0\).
Let \(e\downarrow0\) **after** the profile limit. Hence \(R'(1)\le0\).
The even-degree part vanishes identically on odd ranks, and must be
nonpositive on every even rank because the odd-degree part vanishes there.
Integrating its values on the positive simplices (or applying §1 of the
parity-halves theorem) gives \(\sum_{k\ {\rm even}}k c_k\le0\).
Adding \(R'(1)=\sum_{k\ {\rm odd}} k c_k\) proves the result.

For example \(M=H_3-\tfrac9{10}H_5\) does minorize \(V\):
on triprimes \(H_5/H_3=\tfrac{10}{3}\sum_i x_i^2\ge10/9\), on rank 5
only the negative component remains, and on primes \(M=V/10\).
Its ordinary mean is \(-3/2\).

**Consequence for actual correlations.** No such \(M\), even with mean
zero, has a uniformly positive reflected correlation on the scale
\(X\mathfrak S(P)\) against any fixed \(H_j\) with \(j\ge2\).
Indeed, write \(m_M=\sum k c_k\le0\). The one-variable asymptotic of
the parity-halves theorem gives masses with intensities \(j\) and \(m_M\)
on fixed macroscopic intervals. One can obtain the interval version
from the same simplex sum or by first summing the central estimates over
dyadic intervals to obtain cumulative masses. Total variations are bounded
by finite nonnegative combinations of \(H_k\) of finite intensity.
Even inputs have zero limiting intensity, since on them the prime 2 has
exponent tending to zero and the absolute weight near a zero exponent
tends to zero by the unshifted small-prime estimate. Thus in summing over
even \(P\in[Y,2Y]\) the double sum may be restricted to odd \(n,r\) at cost
\(o(Y^2)\); their sum is automatically even. Let
\(\mathcal D=\{(u,v):1\le u+v\le2,\ (u+v)/3\le u\le2(u+v)/3\}\).
Product Riemann sums give
\[
 \sum_{\substack{Y\le P\le2Y\\P\ {\rm even}}} \langle H_j,M\rangle
     = j m_M\,\operatorname{area}(\mathcal D)\,Y^2+o(Y^2).
\]
Approximate the polygon with rectangles, then let their mesh shrink.
The positive total-variation majorants justify the boundary estimate.
A uniformly positive lower bound on the proposed scale would instead
give a positive multiple of \(Y^2\), since \(\mathfrak S(P)\gg1\).
The signed transfer to \(\langle O_j,\sum c_k O_k\rangle\) changes the
sum by \(o(Y^2)\): the even-target mean of \(\mathfrak S(P)\) is bounded,
as follows by expanding its squarefree divisor product. In particular
the displayed example has negative actual correlations on an unbounded
sequence of targets, on both sides of the transfer.

**Scope and comparison.** The [mixed positive correlation](midpoint_halves_reserve/Proof.md)
keeps several positive ranks and does not conflict with this obstruction.
See [Arneth's October 2026 cubic minorant](https://zenodo.org/records/23477014)
for a different detector built from generalized von Mangoldt functions
on a polynomially rough restricted set. Neither that restricted method
nor a target-dependent comparison of actual joint profiles is ruled out
by the derivative obstruction for this particular finite family.
