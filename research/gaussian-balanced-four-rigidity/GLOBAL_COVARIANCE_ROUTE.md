# A covariance route to the complete four-cell conjecture

8 October 2026. This is an ongoing proof route. **The global comparison
below is not proved.** The Hessian identity and the conditional implication
are derived here; the accompanying floating computations do not establish
the sign of the Hessian on its entire domain.

## The value function and the missing inequality

Write $P=I-\mathbf1\mathbf1^T/4$. For a symmetric matrix $Q\succeq0$ with
$Q\mathbf1=0$, let $Y\sim N(0,Q)$ and define

\[
 C(Q)=\inf_{\lambda\in\mathbb R^4}
 \left\{\frac14\sum_i\lambda_i+
       \mathbb E\max_i(Y_i-\lambda_i)\right\}.                 \tag{R1}
\]

Equivalently, maximize $\mathbb E Y_I$ over couplings for which $I$ is
uniform on four labels. Allowing couplings handles repeated scores and
degenerate covariances. In the full-rank case the maximizing label is the
unique winning affine score almost surely. The price existence and
assignment argument in Section 2 of the paper gives this equivalence;
at degenerate scores it also follows by a limiting argument, or by the
same relaxed assignment problem with tied labels split to their quotas.

We have $C(sQ)=\sqrt{s}C(Q)$ for $s\ge0$, and $C$ is continuous up to the
boundary of the positive semidefinite cone. Indeed use the same standard
Gaussian vector in $Q^{1/2}G$ and $\widetilde Q^{1/2}G$. For every price,
the difference of the two expected maxima is at most
$\mathbb E\|(Q^{1/2}-\widetilde Q^{1/2})G\|$. The same bound applies to
the infima. Also $C(0)=0$ by (R1).

Put $Q_*=P/3$, so $\operatorname{tr}Q_*=1$. The regular tetrahedral
calculation in the paper gives

\[
 C(Q_*)=c_*:=\sqrt{F_{\rm tet}},\qquad
 F_{\rm tet}=12(\arctan\sqrt2)^2/\pi^3.                       \tag{R2}
\]

**Conditional implication.** If $C$ is concave on

\[
 \mathcal Q=\{Q\succeq0:Q\mathbf1=0,\ \operatorname{tr}Q=1\},  \tag{R3}
\]

then the complete regular-tetrahedron global conjecture follows, including
uniqueness up to rotations and relabeling.

*Proof.* Simultaneously permuting the rows and columns preserves $C$.
The average of the 24 permutation conjugates of any $Q\in\mathcal Q$
is $P/3$: a permutation-invariant matrix has constant diagonal and
constant off-diagonal entries; its zero row sums and unit trace specify
these entries. Concavity would therefore give $C(Q)\le c_*$.

For an arbitrary equal-mass measurable partition, form the matrix $M$ of
its first moments, with rows $m_i$, and let $F=\sum_i|m_i|^2$.
Its label is an admissible coupling for $Y=MG$, so
$F\le C(MM^T)$. Since $\operatorname{tr}(MM^T)=F$, homogeneity yields
$F\le c_*\sqrt F$, and hence $F\le F_{\rm tet}$, with $F=0$ handled
separately. The regular partition attains this bound.

It remains to justify uniqueness rather than infer it from symmetry.
The strict local score maximum proved in Section 8 of the paper implies
that $C$ restricted to $\mathcal Q$ has a strict local maximum at $Q_*$.
To see the normalization, realize a nearby Gram matrix by a centered
score list $V$ of squared norm one. The list $\sqrt{F_{\rm tet}}V$ is
near the regular stationary list and has squared norm $F_{\rm tet}$.
The strict local inequality for $H=2C-\|V\|^2$ then implies
$C(Q)<c_*$ unless $Q=Q_*$; rotations give the same Gram matrix.
If any other $Q$ attained $c_*$, concavity and the upper bound would make
the entire segment from it to $Q_*$ attain $c_*$. This contradicts the
strict local maximum. Equality in the partition bound consequently
requires $MM^T=F_{\rm tet}P/3$. Equality in the linear assignment also
requires the regular winning-score cells, proving the classification.
$\square$

Full covariance concavity is stronger than necessary. It is enough that
$C$ be concave along every segment from $Q_*$ to another matrix in
$\mathcal Q$. The derivative at $Q_*$ in every trace-zero direction is
zero by permutation symmetry and smoothness. Concavity along the segment
then puts its endpoint value below its value at $Q_*$. The same strict
local argument proves uniqueness. Thus the restricted radial Hessian
test described below would already suffice.

## The exact Hessian that must have the right sign

Suppose $Q$ is positive definite on $\mathbf1^\perp$. Choose a centered
$4\times3$ score matrix $M$ with $MM^T=Q$, and write its rows as $v_i^T$.
Let $\lambda$ be its balanced prices, in the gauge $\sum_i\lambda_i=0$.
The four scores are affinely independent. Every pair has a positive
Gaussian facet measure, and their facet graph is complete. Use the
notation $A_{ij},w_{ij},L$ from (5) of the paper, now for the scores $v_i$;
the scores need not be their own cell moments. Let $\mathbb E_{ij}$ mean
expectation with respect to normalized Gaussian surface measure on that
facet. Set $d_{ij}=v_i-v_j$.

Every symmetric covariance direction satisfying $D\mathbf1=0$ has a
unique representation $D=MAM^T$ with $A$ symmetric. The additional
trace-zero condition is $\operatorname{tr}(M^TM A)=0$.

Define the vector $r\in\mathbf1^\perp$ by

\[
 r_i=\sum_{j\ne i}w_{ij}\mathbb E_{ij}[d_{ij}^TAX].           \tag{R4}
\]

Let $L^+$ be the inverse of $L$ on $\mathbf1^\perp$ and zero on constants.
Then

\[
\begin{split}
4D^2 C(Q)[D,D]
 &=\min_{u\in\mathbb R^4}\sum_{i<j}w_{ij}
   \mathbb E_{ij}[(d_{ij}^TAX-u_i+u_j)^2]
       -\sum_{i<j}w_{ij}|Ad_{ij}|^2                         \tag{R5}\\
 &=\sum_{i<j}w_{ij}\left\{
      \mathbb E_{ij}[(d_{ij}^TAX)^2]-|Ad_{ij}|^2\right\}
      -r^TL^+r.
\end{split}
\]

*Proof.* Along the covariance path $Q+tD$, use the scores
$M(t)=M(I+tA)^{1/2}$. At zero their first and second derivatives are
$MA/2$ and $-MA^2/4$. The balancing prices are smooth by the implicit
function theorem, since their Hessian is $L$, invertible in the price
gauge. Differentiating each cell mass gives
$L(2\lambda'(0))=r$: across a facet the winning-score gap changes by
$d_{ij}^TAX/2-\lambda'_i+\lambda'_j$.

The surface part of the second variation of the expected maximum is
the sum of the squared gap changes weighted by $w_{ij}$. The other
term is $-\sum_i b_i^TA^2v_i/4$, where $b_i$ are the actual cell moments.
Gaussian flux gives $b=LM$ for every score list, so this term is
$-\sum_{i<j}w_{ij}|Ad_{ij}|^2/4$. The linear price term has no remaining
contribution, because the cell masses are the prescribed masses.
Substituting $u=2\lambda'(0)$ proves the first expression. This $u$
minimizes its quadratic form because $Lu=r$. Completing that quadratic
on $\mathbf1^\perp$ gives the second expression.

These differentiations are local at a full-rank score list. Facets have
codimension one, triple junctions have codimension two, and the fourfold
junction has codimension three. The boundary-strip second variation
therefore has the same justification as Section 3 of the paper.
Equivalently, integrate the smooth Gaussian density over the fixed
polyhedral fan after its locally nonsingular change of coordinates;
Gaussian tails dominate all derivatives needed here. $\square$

Consequently full concavity on (R3) is equivalent to the following
**unproved** inequality at every balanced full-rank score list:

\[
 \min_u\sum_{i<j}w_{ij}
 \mathbb E_{ij}[(d_{ij}^TAX-u_i+u_j)^2]
 \ \le\ \sum_{i<j}w_{ij}|Ad_{ij}|^2                         \tag{R6}
\]

for all symmetric $A$ with $\operatorname{tr}(M^TM A)=0$.
Continuity extends a concavity proof on the interior to the boundary.
For the weaker radial route it is enough to prove (R6) for

\[
 A=\tfrac13(M^TM)^{-1}-I\quad
 \text{when }\operatorname{tr}(M^TM)=1.                      \tag{R7}
\]

Indeed $MAM^T=P/3-Q$. At each interior point of a segment to $Q_*$,
the segment direction is a scalar multiple of this direction. No
positivity conclusion for (R6), even just for (R7), is claimed here.

## Facet moments without finite differences

Here are explicit formulas used by the discovery code. On a facet put
$n=d_{ij}/|d_{ij}|$ and $t=(\lambda_i-\lambda_j)/|d_{ij}|$.
The other two score inequalities, restricted to the plane $n\cdot X=t$,
are $UZ\le h$, where $Z$ is its centered tangential standard Gaussian
and the two rows of $U$ are tangential unit normals. Write
$\rho=U_1\cdot U_2$, $s=\sqrt{1-\rho^2}$, and
$P_f=\Phi_2(h_1,h_2;\rho)$. Affine independence ensures $|\rho|<1$.
For $g=\nabla_h P_f$ and $J=\nabla_h^2P_f$,

\[
\begin{gathered}
 g_i=\varphi(h_i)\Phi((h_j-\rho h_i)/s),\qquad
 J_{12}=\varphi_2(h_1,h_2;\rho),\\
 J_{ii}=-h_i g_i-\rho\varphi_2(h_1,h_2;\rho),\qquad
 \mu=-U^Tg,\\
 S=P_f(I-nn^T)+U^TJU,\\
 \int X\,\mathbf1_{UZ\le h}\,d\gamma_{n^\perp}
       =tnP_f+\mu,\\
 \int XX^T\,\mathbf1_{UZ\le h}\,d\gamma_{n^\perp}
       =t^2nn^TP_f+t(n\mu^T+\mu n^T)+S.                     \tag{R8}
\end{gathered}
\]

The last two integrals use $X=tn+Z$. For a direct derivation, shift the
mean of the tangential Gaussian by $a$. Its probability is
$P_f(h-Ua)$; its first and second derivatives at zero are respectively
the raw first moment and the raw second moment minus $P_f I$.
The displayed derivatives of the bivariate CDF follow by conditioning
one coordinate. Multiply these raw moments by $\varphi(t)/|d_{ij}|$
to obtain their contributions to (R4) and (R5).

## What the experiments and the literature establish

`discovery/covariance_probe.py` uses deterministic floating Plackett
quadrature, solves the three price equations, and evaluates (R5) using
(R8). It does not implement interval arithmetic or certify its root,
CDF values, or eigenvalues. Its separate finite-difference comparison is
a diagnostic for signs and factors, not an independent mathematical
proof. A small positive eigenvalue near a degenerating covariance can be
roundoff and is not a counterexample without further certification.

The fixed batches accompanying this note contain 200 covariance cases
with log-eigenvalues sampled from $[-8,1]$ and 300 from $[-10,1]$,
then rescaled to trace one in score space. They found no positive
trace-preserving Hessian eigenvalue exceeding $10^{-5}$. This is finite
floating evidence only; the cutoff has no role in any theorem.

One neighboring result must not be silently imported. Sun, Hu and Lan,
arXiv:2008.04827v2, Section 6.1, report a numerical nonconcavity example
for the unpriced expected maximum of four unit-variance Gaussians. Their
function does not enforce four equal label probabilities. Its
nonconcavity does not refute (R6), and their regular-simplex maximum
theorem does not prove (R6). A targeted literature search, including
multinomial-probit and Gaussian-surplus terminology, did not locate a
theorem or counterexample for (R6); this is not an exhaustive historical
claim. Source: <https://arxiv.org/abs/2008.04827v2>.

The next complete endpoint is a proof of (R6) for (R7), a different
global comparison, or a rigorously certified counterexample to the
original partition conjecture. Publishing this route does not mark that
endpoint complete and does not warrant an immutable breakthrough release.
