# A state-weighted minimal informationally complete measurement

**Theorem.** For every nonzero positive semidefinite operator
\(R\) on \(\mathbb C^d\), there is an explicit rank-one,
extremal, \(d^2\)-outcome POVM \(\{M_{ab}\}_{a,b=0}^{d-1}\)
such that
\[
             \operatorname{Tr}(R M_{ab})
                    =\frac{\operatorname{Tr}R}{d^2}
                    \qquad(0\le a,b<d).                    \tag{1}
\]
In particular, this is a minimal informationally complete
measurement (MIC): the effects are a real basis of the
Hermitian matrices. No symmetry of \(R\), full-rank
assumption, or SIC existence hypothesis is needed.

## 1. Construction

The case \(d=1\) is the single effect \(I\); assume \(d\ge2\).
Work in an eigenbasis of \(R/\operatorname{Tr}R\) and let
\(r=(r_0,\ldots,r_{d-1})^\top\) be its eigenvalues as a
column, each nonnegative and with sum 1. All subscripts
on coordinates below are read modulo \(d\). Put
\[
 0<\epsilon\le\frac1{2d^4},\quad
 \theta=\frac{\pi}{2d},\quad
 t=e^{\mathrm i\theta},\quad
 \zeta=e^{2\pi\mathrm i/d},\quad
 P_{ai}=\frac1d+\epsilon(\delta_{ai}-r_a).
\]
Each \(P_{ai}\) lies in
\([1/d-\epsilon,\,1/d+\epsilon]\), a strictly positive interval.
Define
\[
 u_a(i)=t^{\delta_{ai}}\sqrt{P_{ai}},\qquad
 Z|i\rangle=\zeta^i|i\rangle,\qquad
 M_{ab}=\frac1d Z^b u_a u_a^\ast Z^{-b}.                    \tag{2}
\]
For an arbitrary eigenbasis, conjugate these effects back
to the original coordinate system.

The columns of \(P\) sum to 1 and \(P r=d^{-1}\mathbf 1\).
Averaging over \(b\) dephases \(u_a u_a^\ast\) in the chosen
basis, so \(\sum_{a,b}M_{ab}=I\). The effects all have rank
one. Since the weight \(R\) is diagonal, its expectation
on each effect is \(\operatorname{Tr}(R)(Pr)_a/d\), giving
(1). This is state-weighted balance, not necessarily equal
traces of the effects.

## 2. Informational completeness

Use the complex matrix algebra for the linear-independence
calculation. Taking the discrete Fourier transform in \(b\)
separates the matrices into their cyclic bands, indexed by
\(s=0,\ldots,d-1\). Indeed the \((i,i+s)\) entry carries the
factor \(\zeta^{-bs}\); after summing \(\zeta^{bs}M_{ab}\)
over \(b\), it is \(u_a(i)\overline{u_a(i+s)}\), and all
other cyclic bands vanish. Thus the span of the effects is
the full complex matrix space if, for each \(s\), the \(d\)
vectors indexed by \(a\) in that band form a basis.

For \(s=0\) the band matrix is \(P\), which is invertible.
If \(P x=0\), the column-sum identity gives
\(\mathbf 1^\top x=0\), and on this subspace \(P x=\epsilon x\).
Equivalently the matrix determinant lemma gives
\(\det P=\epsilon^{d-1}\): write
\(P=\epsilon I+(d^{-1}\mathbf 1-\epsilon r)\mathbf 1^\top\).

For \(s\ne0\) the band matrix \(C_s\), rows \(a\) and columns
\(i\), is
\[
 (C_s)_{ai}=\sqrt{P_{ai}P_{a,i+s}}\;
             t^{\delta_{ai}-\delta_{a,i+s}} .
\]
Let \(C_s^{(0)}\) denote the same formula with \(P_{ai}=1/d\).
Write \(J\) for the all-ones matrix and \(S_s\) for the cyclic
permutation with entry 1 where \(a=i+s\). Since \(s\ne0\),
these positions are disjoint from the diagonal. We have
\[
 C_s^{(0)}=\frac1d
       \big[J+(t-1)I+(t^{-1}-1)S_s\big].
\]
This circulant is unitarily diagonalized by the Fourier
basis. Its constant-mode eigenvalue is
\((d-2+2\cos\theta)/d\). Any other eigenvalue is
\((t-1)(1-t^{-1}\xi)/d\) for a \(d\)th root of unity \(\xi\),
possibly \(\xi=1\) if \(s\) is not coprime to \(d\).
The circular angular distance from \(t\) to any such
root is at least \(\theta\), because \(\theta\) lies a
quarter of the way from 1 to the next root. On \([0,\pi]\)
a chord of angular length \(\varphi\) has length
\(2\sin(\varphi/2)\ge2\varphi/\pi\). In particular both
nonconstant factors have absolute value at least \(1/d\).
The constant-mode absolute value is at least
\(\sqrt2/d\), since \(d\ge2\) and \(\cos\theta\ge1/\sqrt2\).
It follows that
\[
                         \sigma_{\min}(C_s^{(0)})\ge d^{-3}.
\]
The geometric mean of any two positive entries of \(P\)
also lies in \([1/d-\epsilon,1/d+\epsilon]\). Hence
entrywise \(|C_s-C_s^{(0)}|\le\epsilon\) and
\(\|C_s-C_s^{(0)}\|_{\rm op}\le\|C_s-C_s^{(0)}\|_{\rm F}
\le d\epsilon\le\tfrac12d^{-3}\). Every \(C_s\) is therefore
invertible, with minimum singular value at least
\(\tfrac12d^{-3}\). The real span of the Hermitian effects
is the entire Hermitian space: complex independence of the
\(d^2\) effects implies real independence, and the real
dimension is exactly \(d^2\).

For completeness, rank-one independence implies extremality
in the convex set of POVMs with these outcome labels. If
\(M_{ab}=pN_{ab}+(1-p)Q_{ab}\) with \(0<p<1\) and \(N,Q\)
POVMs, positivity forces each \(N_{ab},Q_{ab}\) to be
supported on the rank-one range of \(M_{ab}\). Thus
\(N_{ab}-M_{ab}\) is a real multiple of \(M_{ab}\).
The sum over \(a,b\) vanishes, so linear independence
forces every multiple to vanish. The same holds for \(Q\).
This finishes the theorem.

## 3. Exact attainment in fixed-state quantum randomness

Theorem 4.6 of Gutierrez Anco, Nemoz and Brown
(arXiv:2410.16447v2; see also their Theorem B.4) already
determines the **supremal values** and gives the equality
criteria among extremal rank-one POVMs. It does not prove
that the equality measurements exist in all dimensions:
the given proof uses a limiting sequence, and Example 4.7
supplies exact attainment for a qubit.

In that paper's precise device-dependent optimization,
apply (1) at a given input density operator \(\rho\) with
\[
  R=\rho^{\alpha/(2\alpha-1)}\quad(\alpha>1)
\]
for the up-arrow sandwiched Rényi criterion, and with
\[
  R=\rho^{1/\alpha}\quad(1/2\le\alpha<1
                                      \ \text{or}\ \alpha>1)
\]
for its down-arrow criterion. The choices are nonzero
positive semidefinite even for singular \(\rho\). Equation
(1) is exactly their respective equality condition
(46) or (48), so the previously computed suprema are
**maxima** in every dimension and at every state. The
numerical formulas \(2\log_2d-H_{\alpha/(2\alpha-1)}(\rho)\)
and \(2\log_2d-H_{1/\alpha}(\rho)\) remain theirs. The new
assertion is the existence of the explicit optimizers.

For clarity, the up-arrow attainment uses only bounds in
Appendix A, not the generally nonuniform entropy-index
substitution after the inequality in their Eq. (71).
Set \(\gamma=\alpha/(2\alpha-1)\),
\(\beta=2-1/\alpha=1/\gamma\), and
\(p_x=\operatorname{Tr}(\rho^\gamma M_x)/
          \operatorname{Tr}\rho^\gamma\).
Their lower bound (73) and the comparison inequality in
(71), followed by their down-arrow formula (68) at
order \(\beta\), give
\[
 H_\alpha(p)-H_\gamma(\rho)
 \ \le H_\alpha^\uparrow(X|E)
 \ \le H_\beta^\downarrow(X|E)
       =H_\beta(p)-H_\gamma(\rho).
\]
The two classical entropies of the uniform \(d^2\)-point
law are equal to \(2\log_2d\), so both bounds coincide
for (2). Even for nonuniform \(p\) the upper bound is
at most \(2\log_2d-H_\gamma(\rho)\), since an extremal
rank-one POVM has at most \(d^2\) nonzero effects.

For the conditional min-entropy one can also prove the
equality directly on canonical purifying side information.
Take \(R=\sqrt\rho\), let \(x=(a,b)\), and write
\(M_x=m_xm_x^\ast\). Put \(c=\operatorname{Tr}\sqrt\rho/d^2\).
The subnormalized state on the purifying register given
outcome \(x\) is
\(\sigma_x=\sqrt\rho\,\overline{m_x}m_x^{\top}\sqrt\rho\)
in the chosen eigenbasis. The compressed transposed
effects \(P_\rho M_x^\top P_\rho\), where \(P_\rho\) is
the support projector of \(\rho\), define a POVM on the
support. It guesses with probability
\[
 \sum_x \operatorname{Tr}(\sigma_x P_\rho M_x^\top P_\rho)
        =\sum_x[\operatorname{Tr}(\sqrt\rho\,M_x)]^2
        =d^2c^2 .
\]
Conversely \(c\sqrt\rho\succeq\sigma_x\) for each \(x\).
Conjugating by \(\rho^{-1/4}\) on its support reduces
this to the fact that the unique nonzero eigenvalue of
\(\rho^{1/4}M_x^\top\rho^{1/4}\) is \(c\). Summing the
inequality against any guessing POVM shows its success
probability is at most \(c\,\operatorname{Tr}\sqrt\rho=d^2c^2\).
Thus \(H_{\min}(X|E)=2\log_2d-H_{1/2}(\rho)\).
The extension to the cited paper's device-side-information
optimization uses its Lemma 4.5/B.3 for extremal rank-one
effects and the previously derived upper bound. This is not
a statement about arbitrary, uncharacterized laboratory
implementations.

For pure \(\rho\), this gives exactly \(2\log_2d\), with
uniform outcomes, without the SIC hypothesis in Curran's
arXiv:2605.18291v1 §3. For an isotropically noisy
\(\rho\) it in particular gives that paper's equality in
(13) with the same assumptions and no SIC requirement.
A calibrated MIC also identifies the state from its exact
outcome distribution in the source-device-independent
interpretation of that work; noisy statistics and robustness
are not treated here.

The POVM generally depends on the requested entropy
criterion. If an MIC satisfies the uniformity condition
for two normalized weights \(\rho^s/\operatorname{Tr}\rho^s\)
and \(\rho^t/\operatorname{Tr}\rho^t\) with distinct positive
exponents, informational completeness forces the weights
equal. By diagonalizing \(\rho\), this holds exactly when
all of its nonzero eigenvalues are equal. For such a flat
spectrum one choice in (2) works for every positive power.
In particular a pure state admits a common optimizer.

## 4. Weighted condition in one-sided randomness certification

In Sarkar et al., arXiv:2110.15176, the certification
procedure preceding Eq. (14) already applies to any known
pure bipartite state of local dimension \(d\) with all
\(d\) Schmidt coefficients nonzero and to any rank-one
extremal measurement chosen on the untrusted side.
That proof derives \(2\log_2d\) randomness if the reduced
density operator \(\rho_B\) and the measurement effects
\(\{\mathcal I_b\}\) obey
\(\operatorname{Tr}(\rho_B\mathcal I_b)=1/d^2\) for all
\(b\). The source provides this condition in all dimensions
for the maximally entangled state and in some partial-
entanglement ranges in low dimensions. Its outlook asks
for measurements even at arbitrarily weak entanglement.

Applying (1) with \(R=\rho_B\) supplies precisely that
missing measurement in every dimension and for every
strictly positive Schmidt spectrum. This is a corollary
using the paper's observed-correlation and trusted-side
assumptions, not a new steering test, a DI protocol,
a finite-precision security guarantee, or an assertion
for rank-deficient Schmidt spectra at the larger nominal
dimension.

## 5. Explicit unbiased approach to the pure-state maximum

With \(r_i=1/d\) in (2), the row sums of \(P\) are all 1.
Hence the effects have equal trace \(1/d\), which is the
definition of an unbiased measurement in Curran's paper.
For the pure basis state \(|i\rangle\), the largest of the
outcome probabilities \(P_{ai}/d\) is
\([1+(d-1)\epsilon]/d^2\). Its intrinsic min-entropy with
that measurement is
\[
              2\log_2 d-\log_2[1+(d-1)\epsilon].
\]
It tends to \(2\log_2d\) as \(\epsilon\downarrow0\)
through explicit unbiased MICs, in every dimension.
The value is not attained by an unbiased MIC on a pure
state for \(d>1\): the maximally mixed state already gives
uniform outcomes on the same MIC, and equal statistics
would contradict informational completeness. The
\(\epsilon=0\) limiting effects lose diagonal independence.
This is an all-dimensional family with the same
approximation property as the reported low-dimensional
examples, not a claim of their particular scissors
geometry or SIC endpoint.
