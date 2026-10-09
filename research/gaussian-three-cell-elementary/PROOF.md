# Three equal Gaussian cells: elementary sharp first-moment proof

**Status:** Unconditional mathematical proof, not a claim of completed Lean verification. The general \(k\ge4\) theorem is outside this result. The matching Lean source in PR #8 is checked separately by fixed-version GitHub CI.

## Statement

Let \(X\sim N(0,I_d)\). For any measurable fractional partition \(0\le f_i\le1\) (\(i=0,1,2\)), \(\sum f_i=1\) almost surely, \(\mathbb E f_i=1/3\), put \(m_i=\mathbb E[Xf_i(X)]\) and \(E=\sum_i\|m_i\|^2\). Then
\[
\boxed{E\le \tfrac12(\mathbb E\max(Z_0,Z_1,Z_2))^2}
\]
for independent standard normals \(Z_i\). In dimension \(d\ge2\), equality holds exactly for cylindrical regular three-sector fans (up to rotations, null sets and relabeling); for \(d=1\), it is strict.

## Direct covariance proof (no Gaussian multi-bubble input)

For every three real numbers \(a,b,c\),
\[
2\bigl(\max(a,b,c)+\max(-a,-b,-c)\bigr)
=|a-b|+|a-c|+|b-c|.
\]
For an integrable centrally symmetric real triple \(Y\), taking expectations yields
\[
4\,\mathbb E\max_iY_i=\sum_{i<j}\mathbb E|Y_i-Y_j|. \tag{1}
\]
For Gaussian score vectors \(Y_i=\langle v_i,X\rangle\) in arbitrary finite dimension, each difference is \(N(0,\|v_i-v_j\|^2)\). Writing \(\mu=\mathbb E|Z|>0\) for a standard normal \(Z\), equation (1) becomes
\[
4\,\mathbb E\max_i\langle v_i,X\rangle
=\mu\sum_{i<j}\|v_i-v_j\|. \tag{2}
\]
Suppose scores are centered and trace-normalized: \(\sum_i v_i=0\) and \(\sum_i\|v_i\|^2=1\). An exact Euclidean identity gives
\[
\sum_{i<j}\|v_i-v_j\|^2=3\sum_i\|v_i\|^2-\bigl\|\sum_i v_i\bigr\|^2=3.
\]
Therefore three-term Cauchy implies \(\sum_{i<j}\|v_i-v_j\|\le3\). Equation (2) gives
\[
\mathbb E\max_i\langle v_i,X\rangle\le 3\mu/4, \tag{3}
\]
and equality forces all three edge lengths to equal one, determining the centered trace-one regular Gram matrix \(Q_*\).

For an arbitrary centered positive-semidefinite trace-one \(3\times3\) covariance \(Q\), select any centered Gaussian score realization \(v\) with Gram matrix \(Q\). The optimized balanced score value \(C(Q)\), which is the infimum over prices, does not exceed its value at price zero. Thus \(C(Q)\le3\mu/4\). At \(Q_*\), the actual zero-price winner cells are equally likely by symmetry, so price zero minimizes the balanced score objective. They have three edges of length one. Hence \(C(Q_*)=3\mu/4\). Writing the regular score vector as \((Z_i-\bar Z)/\sqrt2\) identifies
\[
C(Q_*)=\frac{\mathbb E\max_iZ_i}{\sqrt2}.
\]
Therefore \(C(Q)\le C(Q_*)\), with equality only for the regular Gram matrix. Singular covariance endpoints are included; no differentiability of prices or geometric perimeter theorem is needed.

## Actual fractional-partition reduction and equality

For actual first moments \(m_i\), Gaussian centering gives \(\sum_i m_i=0\). Actual pointwise price duality yields \(E\le C(MM^T)\), where \(M\) has rows \(m_i\). When \(E>0\), the proven square-root homogeneity of \(C\) shows
\[
E\le\sqrt E\ C(MM^T/E)\le\sqrt E\ C(Q_*),
\]
so \(E\le C(Q_*)^2\); if \(E=0\), the inequality is trivial.

If equality holds, \(MM^T/E=Q_*\), which has rank two, excluding ambient dimension one. Equality in primal–dual comparison forces the fractional labels to coincide almost everywhere with the winning cells of these moment scores; the regular Gram form and symmetric prices force the regular three-sector fan. Conversely the previously constructed regular winning partition attains the constant.

## Lean interfaces and trust status

The existing foundation proves the actual Gaussian score-price primal-dual, covariance coupling, norm/trace normalization, regular winner attainment, Gram rigidity and fractional-dual equality almost everywhere. PR #8 adds the exact three-maximum identity and the actual Gaussian absolute projected moment formula, then assembles finite three-edge Cauchy and the unconditional main inequality. The exact-byte pinned CI and each declaration's printed axioms—not this prose note—determine whether each new Lean assertion is verified. At the time of this note, do not infer completion of the all-\(k\) Gaussian theorem, the sharp multi-bubble perimeter inequality, or all equality declarations.
