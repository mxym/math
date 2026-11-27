# Gaussian maximum entropy with a one-constraint formula and exactness of a soft objective

## 1. Model

Let \(X\) be centered Gaussian noise in \(\mathbb R^n\), with specified
positive marginal standard deviations \(\sigma_i\), and let \(AX=0\)
be required almost surely. Write \(\mathsf D=\operatorname{diag}(\sigma)\),
\(\operatorname{Cov}(X)=\mathsf D R\mathsf D\), and \(B=\mathsf D A^{\mathsf T}\).
Then \(R\) is a correlation matrix (symmetric positive semidefinite,
diagonal \(\mathbf1\)), and \(AX=0\) holds exactly when \(RB=0\):
the invariant covariance is \(B^{\mathsf T}RB\), a Gram matrix, so it
vanishes exactly when \(R^{1/2}B=0\). We study the correlation-space
formulation below. Rescaling by \(\mathsf D\) gives the output
covariance. On any fixed feasible support subspace the rescaling
changes differential entropy by a constant independent of \(R\), by
the fixed subspace Jacobian of the invertible linear transformation.

If \(W\) is the maximal feasible support and \(K\) an orthonormal
basis matrix for \(W\), we use differential entropy relative to
Lebesgue measure on \(W\). For a centered Gaussian supported fully
on \(W\) the entropy is
\(\frac12\log\det(K^{\mathsf T}RK)+\frac{\dim W}{2}\log(2\pi e)\).
Gaussians of smaller support are singular relative to this measure.
The same optimum applies if all joint distributions with the
specified Gaussian marginals and the invariant are permitted:
each such distribution has a feasible covariance, and the Gaussian
of that covariance maximizes entropy on its support. This follows
by nonnegativity of relative entropy to that Gaussian, since its
quadratic log density has the same expectation under the two laws.
Degenerate supports are compared using the maximal feasible subspace,
not different reference measures at different candidates.

## 2. One arbitrary weighted invariant

The graph reduction below is already available in Lafferty–Roy
v2 Theorem 2, Eqs. (7)–(8). The resulting fixed-diagonal max-det
problem at one constraint is equivalent to the optimization in
Bernard–Bondarenko–Vanduffel §3.1, Eq. (3.3), Proposition 3.7 and
Remark 3.10; they compute the optimum numerically. The contribution
here is its explicit scalar solution, including all feasible and
infeasible cases.

**Theorem 1.** For \(B=b\) a single column, order the nonzero
coefficients so that \(|b_1|=\max_i |b_i|\). If \(b=0\), the
maximum-entropy solution is \(I\). Otherwise:
* If \(|b_1|>\sum_{i\ne1}|b_i|\), no feasible covariance exists.
* If equality holds, the active coordinates of any feasible
  covariance are collinear. With signs as below their Gram matrix
  is \(vv^{\mathsf T}\), where \(v_i\in\{-1,1\}\); the optimum
  on the maximal support is \(vv^{\mathsf T}\oplus I\).
* If the inequality is strict in the other direction, the maximal
  support is \(b^\perp\). Remove the zero coefficients as an
  independent identity block and put \(c=(b_2,\ldots,b_m)^{\mathsf T}/b_1\)
  on the remaining \(m\) active coordinates. Set \(w_i=c_i^2\)
  for indices \(i=1,\ldots,m-1\), and
\[
 a_i(u)=\sqrt{1-w_i+w_i u^2},\qquad
 F(u)=\sum_{i=1}^{m-1}\frac{w_i(1+u)}{1+a_i(u)} .
\]
  If \(F(0)\ge1\), choose the unique \(u\in[0,1)\) satisfying
\[
 (1-u)+\sum_i(1-a_i(u))=2,\qquad x=\frac{1-u}{2}.
 \tag{1}
\]
  If \(F(0)<1\), choose the unique \(u>0\) with \(F(u)=1\), and
  \(x=(1+u)/2\). A root \(u=1\) is allowed in this second branch.
  In both cases put \(s=(1-u^2)/4\) and \(D_0=\operatorname{diag}(d_i)\),
  \(d_i=2/(1+a_i(u))\). The optimum, appending the independent
  identity block, is
\[
 C=D_0-s(D_0c)(D_0c)^{\mathsf T},\qquad
 R_\star=\begin{bmatrix}-c^{\mathsf T}\\ I\end{bmatrix}
             C\begin{bmatrix}-c&I\end{bmatrix}.
 \tag{2}
\]
  Its determinant on the active orthonormal hyperplane equals
  \((1+\|c\|^2)x\prod_i d_i\).

**Proof.** The Gram form \(R_{ij}=\langle v_i,v_j\rangle\) has unit
vectors \(v_i\), with \(\sum b_i v_i=0\). The triangle inequality
gives the necessary balance condition. In the saturation case
the vectors \(b_i v_i\) for \(i\ne1\) with nonzero weights must all
point along the same ray, opposite to \(b_1v_1\).
Equivalently fix their common unit direction, take signs
\(\operatorname{sgn}(b_i)\) for \(i\ne1\), and
\(-\operatorname{sgn}(b_1)\) at the first coordinate. The maximum
active support is their one-dimensional span. In a unit coordinate
along this direction the variance is \(m\), since \(\|v\|^2=m\).
The inactive diagonal entries are one. Hadamard's determinant
inequality yields the optimum by making those adapted coordinates
independent. It is attained and unique since all displayed
variances are positive in the adapted subspace.

For strict balance, the graph factorization in (2) is forced by
\(Rb=0\). It is the \(k=1\) case of Lafferty–Roy v2 Eq. (8):
the lower principal block \(C\) is subject to \(C\succeq0\),
\(\operatorname{diag}C=\mathbf1\), and \(c^{\mathsf T}Cc=1\).
On the active hyperplane the determinant is
\(\det(C)(1+\|c\|^2)\), by the Gram determinant of the
fixed graph basis. Any coordinates with \(b_i=0\) can be made
independent from the active ones and from each other without
reducing the constrained support determinant: on the fixed
orthogonal decomposition the block determinant inequality gives
\(\det M\le\det M_A\det M_{\rm inactive}\le\det M_A\).
The first inequality follows from the Schur complement, with
equality in the positive definite case only if the off-block
matrix vanishes; the second is Hadamard's inequality.

Each \(w_i\) belongs to \((0,1]\). In (1) the left side strictly
decreases from \(1+F(0)\ge2\) to zero as \(u\) moves from zero
to one. In the other branch \(F(0)<1\) forces all \(w_i<1\).
Each summand of \(F\) increases strictly for \(u\ge0\):
the sign of its derivative is the sign of
\(a_i(u)+1-w_i-w_i u>0\), because
\(a_i(u)\ge\sqrt{w_i}u\). Its limit at infinity is
\(\sqrt{w_i}\), so \(F(u)\to\sum_i |c_i|>1\) by strict balance.
Thus the stated roots exist, are unique, and can be bracketed
and bisected using only real arithmetic and square roots.

Put \(y_i=(1-a_i(u))/2\). Then \(y_i(1-y_i)=s w_i\) and
\(d_i=(1-y_i)^{-1}\). In the first branch (1) says
\(x+\sum_i y_i=1\). In the second branch use
\[
 y_i=\frac{(1-u)w_i(1+u)}{2(1+a_i(u))}
\]
to get the same identity, including \(u=1\). In both branches
\(x(1-x)=s\) and \(x>0\). Put \(t=c^{\mathsf T}D_0c\);
then \(s t=\sum_i y_i=1-x\). If \(s\ne0\), this gives
\(tx=1\); if \(s=0\) the solution is \(u=1\), so \(x=1\)
and \(t=F(1)=1\), again \(tx=1\).

The rank-one update form of \(C\) shows it is positive definite:
the eigenvalues after congruence by \(D_0^{-1/2}\) are one on
the perpendicular complement of \(D_0^{1/2}c\), and
\(1-st=x\) along it. Its diagonal is one since
\(d_i-sd_i^2 w_i=d_i(1-y_i)=1\).
Also \(c^{\mathsf T}Cc=t(1-st)=1\). Its inverse is
\[
 C^{-1}=D_0^{-1}+\frac{s}{x}cc^{\mathsf T}.
\]
This is a linear combination of the gradients of the affine
constraints on \(C\). The concavity inequality for \(\log\det\)
therefore proves it is an optimum, and strict concavity gives
uniqueness. The determinant formula follows from that same
rank-one update. This supplies full rank on the prescribed
hyperplane and proves sufficiency of balance, including the
explicit saturation case above. The case \(b=0\) follows by
Hadamard's inequality.

The result extends without coupled optimization to disjoint
weighted constraint supports. The maximal support decomposes
orthogonally into their maximal feasible supports and the unused
coordinates; the same block determinant inequality shows the
blocks are independent at maximum entropy. It also covers a
laminar family of sets with a common coordinate weight vector:
each constraint row is the coordinate weights times the
indicator of one set, and any two sets are nested or disjoint.
Subtract the indicators of its maximal proper children from
each row. This is a triangular row operation and yields exactly
the disjoint residual atoms, with any empty zero row discarded.
Thus the original constraints are equivalent to the disjoint
ones. This does not include arbitrary crossing sets or
incompatible per-row weights.

## 3. Exactness of the finite-weight objective

Let \(B\) now have any number of columns, \(U=\operatorname{col}B\),
\(W=U^\perp\), \(P=KK^{\mathsf T}\) its projector, and \(p_i=P_{ii}\)
its coordinate leverages. Assume there exists a correlation
matrix \(R\) with \(\ker R=U\), so every \(p_i>0\). Let \(R_0\)
be the unique solution maximizing
\[
 g(R)=\log\det(K^{\mathsf T}RK)
\]
under the exact constraint \(RB=0\). The determinant is
maximized at a positive value by compactness and the assumption;
uniqueness follows from strict log-det concavity since exact
matrices are determined by the compression. Treat \(g=-\infty\)
for singular compressions, and use natural logs in this section.

For \(\tau>0\), Lafferty–Roy v2 Eq. (6) is precisely the
minimum on the full elliptope of
\[
 F_\tau(R)=v(R)-\tau g(R), \qquad v(R)=\operatorname{tr}(B^{\mathsf T}RB).
 \tag{3}
\]
Here the basis in \(g\) is chosen for \(W\), as in the objective's
derivation; this is not a statement about an unrelated compression.
The minimum exists, since the elliptope is compact and the
objective extended by \(+\infty\) is lower semicontinuous.

**Theorem 2.** The following are equivalent:
* Some \(\tau>0\) has a minimizer with \(RB=0\).
* For every \(\tau>0\), the unique minimizer is exact.
* \(P\operatorname{diag}(p)=\operatorname{diag}(p)P\).

In the exact case the minimizer is
\[
 R_0=P\,\operatorname{diag}(1/p_i)\,P.
 \tag{4}
\]
Otherwise every positive \(\tau\) is inexact. For a single
nonzero \(b\) and full feasible support \(b^\perp\), the condition
is exactly equality of all nonzero magnitudes \(|b_i|\).

**Proof.** Set \(C_0=K^{\mathsf T}R_0K\) and
\(G=K C_0^{-1}K^{\mathsf T}=R_0^+\), using the Moore–Penrose
inverse on the support. Any exact minimizer of (3) is \(R_0\).
Write \(R_0=VV^{\mathsf T}\) with \(V=K C_0^{1/2}\). Each row
\(v_i\) of \(V\) is a unit vector. For any row vectors \(h_i\)
orthogonal to \(v_i\), set
\[
 V(t)_i=(v_i+t h_i)/\|v_i+t h_i\|,\qquad R(t)=V(t)V(t)^{\mathsf T}.
 \tag{5}
\]
This is an elliptope curve for real \(t\) near zero. Its invariant
term is \(O(t^2)\), since \(V^{\mathsf T}B=0\).
Its log-det derivative at zero is
\(2\sum_i h_i\cdot(GV)_i\). If (3) is exact at \(R_0\), this
derivative must vanish for every tangent, so \(GV=\Lambda V\)
for a diagonal \(\Lambda\). As \(V\) spans \(W\), \(\Lambda\)
preserves \(W\); by symmetry it commutes with \(P\), and
its restriction to \(W\) equals \(G|_W>0\).
Every \(P e_i\ne0\) is an eigenvector of \(\Lambda\) with
eigenvalue \(\Lambda_{ii}\), so the diagonal entries are positive.
It follows that \(R_0=P\Lambda^{-1}P\). Unit diagonal then
requires \(\Lambda_{ii}=p_i\). This proves necessity.

Conversely, let \(S=\operatorname{diag}(p)\) commute with \(P\).
Then the matrix in (4) is a correlation matrix of kernel \(U\).
Its compressed gradient is \(G=PSP\). For any correlation
matrix \(R\), using the common diagonal and \(R_0(I-P)=0\),
\[
 g(R)-g(R_0)\le\langle G,R-R_0\rangle
 =-\operatorname{tr}(S(I-P)R)\le0 .
\]
The last trace is nonnegative before the sign because both
factors are positive semidefinite. If \(RB\ne0\), (3) is strictly
larger than at \(R_0\) by \(v(R)>0\); if \(RB=0\) use the
strict concavity on the exact face. This proves sufficiency and
uniqueness. Finally \([P,S]_{ij}=P_{ij}(p_j-p_i)\), giving the
equivalent rule of constant leverage on each connected component
of the graph of the off-diagonal nonzeros of \(P\).
For \(P=I-bb^{\mathsf T}/\|b\|^2\), that graph has a complete
component on the nonzero entries of \(b\), and \(p_i=1-b_i^2/\|b\|^2\).

If no feasible covariance fills \(W\), there is no exact
matrix of finite objective in (3), and no statement about its
small-\(\tau\) rate below is made. This includes some saturated
feasible cases of Theorem 1. A support of two saturated active
entries does fill \(b^\perp\), and Theorem 2 applies there.

The equal-weight active example in the source is therefore exact
for every \(\tau>0\), not just small \(\tau\). For \(n\ge4\),
the all-ones example has other feasible matrices of rank \(n-1\):
to the maximum-entropy matrix add a small multiple of the
symmetric zero-diagonal pattern with off-diagonal entries
\(M_{12}=M_{34}=1,\ M_{13}=M_{24}=-1\) and other entries zero.
It has zero row sums and a small perturbation preserves positivity
on the orthogonal hyperplane. Thus maximum entropy, not maximum
rank alone, is the uniqueness statement.

## 4. Residual at small positive penalty weight

Keep the full-support assumption of §3, take \(U\ne0\), and
let \(L\) be an orthonormal basis matrix of \(U\).
Use \((K,L)\) coordinates for any correlation matrix:
\[
 C=K^{\mathsf T}RK,\qquad Y=K^{\mathsf T}RL,\qquad Z=L^{\mathsf T}RL,\qquad
 J=L^{\mathsf T}BB^{\mathsf T}L>0 .
\]
Then \(v(R)=\operatorname{tr}(JZ)\).
There is a diagonal \(\Lambda\) supporting the exact
max-det problem, satisfying \(K^{\mathsf T}\Lambda K=C_0^{-1}\).
Indeed the derivative at \(C_0>0\) vanishes on the kernel of
the linear map \(X\mapsto\operatorname{diag}(KXK^{\mathsf T})\),
since that describes all feasible directions locally. The
orthogonal complement of the kernel is the range of the adjoint,
which is exactly the displayed set of compressed diagonals.

Define the linear space
\[
 \mathcal E=\{E:\ \exists X=X^{\mathsf T},\
 \operatorname{diag}(KXK^{\mathsf T}+KEL^{\mathsf T}+LE^{\mathsf T}K^{\mathsf T})=0\},
\]
and on it define
\[
 \|E\|_*^2=\operatorname{tr}(J E^{\mathsf T}C_0^{-1}E),
 \qquad \ell(E)=-2\operatorname{tr}((K^{\mathsf T}\Lambda L)^{\mathsf T}E).
\]
The norm is positive definite. On \(\mathcal E\), the functional
is independent of the choice of diagonal multiplier:
it equals \(\operatorname{tr}(C_0^{-1}X)\) for every compatible \(X\),
by the defining diagonal constraint. Let \(E_*\) be the unique
minimizer of \(\|E\|_*^2-\ell(E)\) on this linear space. It is
found by a finite linear system. Equivalently \(E_*\) is half
the norm-inner-product representative of \(\ell\), so
\(\ell(E_*)=2\|E_*\|_*^2\).

**Theorem 3.** For any minimizers \(R_\tau\) of (3),
\[
 \lim_{\tau\downarrow0}\frac{v(R_\tau)}{\tau^2}=\|E_*\|_*^2,\qquad
 \lim_{\tau\downarrow0}\frac{g(R_\tau)-g(R_0)}{\tau}=2\|E_*\|_*^2.
 \tag{6}
\]
The constant is positive exactly when the projector does
not satisfy Theorem 2's commutation condition.

**Proof.** The gradient bound for log determinant and the
diagonal constraint give
\[
 \Delta g\le\langle G,R-R_0\rangle
 =\ell(Y)-\operatorname{tr}((L^{\mathsf T}\Lambda L)Z).
 \tag{7}
\]
Here the right side uses the same linear formula for \(\ell\)
on all cross blocks, even those outside \(\mathcal E\).
Positive semidefiniteness and trace \(n\) imply
\(\|Y\|_{\mathrm F}\le\sqrt{n\,\operatorname{tr}Z}\):
factor \(R\) as a Gram matrix and apply the product norm
bound to its two row blocks. Also \(\|Z\|_{\mathrm F}\le\operatorname{tr}Z\)
and \(v\ge\lambda_{\min}(J)\operatorname{tr}Z\). Thus
\(\Delta g\le a\sqrt v+bv\) for fixed finite \(a,b\ge0\).
Optimality gives \(v(R_\tau)\le\tau\Delta g\); for small
\(\tau\), this forces \(v(R_\tau)=O(\tau^2)\) (including
the possible zero case). Compactness gives \(R_\tau\to R_0\):
any limit has zero residual and \(g\) no smaller than \(g(R_0)\)
by upper semicontinuity. In particular its compression is
positive definite. Uniqueness on the exact face gives the limit.

For any \(E\in\mathcal E\), choose a compatible \(X\) and in
(5) take the matrix of row tangents
\[
 H=K\frac{X}{2}C_0^{-1/2}+L E^{\mathsf T} C_0^{-1/2}.
\]
Its rows are orthogonal to those of \(V\) because the
correlation derivative has diagonal zero. That derivative
has \(W\)-block \(X\), cross block \(E\), and \(U\)-block zero.
The row normalization in (5) does not change its first derivative.
Since \(L^{\mathsf T}V(0)=0\), the \(U\)-block of \(R(t)\)
is \(t^2 E^{\mathsf T}C_0^{-1}E+O(t^3)\).
Putting \(t=\tau\) gives a feasible comparison with
\[
 [F_\tau(R(\tau))-F_\tau(R_0)]/\tau^2
 \longrightarrow \|E\|_*^2-\ell(E).
 \tag{8}
\]

For the lower bound, take a subsequence along which
\(Y_\tau/\tau\to E\) and \(Z_\tau/\tau^2\to Z'\), possible by
the residual and cross bounds. The diagonal equation,
projected onto the complement of the range of
\(X\mapsto\operatorname{diag}(KXK^{\mathsf T})\), divided by
\(\tau\), shows \(E\in\mathcal E\): the \(Z\)-term vanishes
at this scale. The Schur complement gives
\(Z'\succeq E^{\mathsf T}C_0^{-1}E\), since \(C_\tau\to C_0\).
Using (7) the lower limit of the scaled objective in (8),
for the actual minimizers, is at least
\(\operatorname{tr}(JZ')-\ell(E)\ge\|E\|_*^2-\ell(E)\).
The upper limit is at most the minimum over \(E\), by
(8). Thus equality forces \(E=E_*\) and
\(Z'=E_*^{\mathsf T}C_0^{-1}E_*\), as \(J>0\).
This is true of every convergent subsequence. It proves the
residual limit; subtracting the scaled objective from it
gives the log-det limit.

If (4) applies, take \(\Lambda=\operatorname{diag}(p)\);
its cross block is zero, so \(E_*=0\).
Conversely if \(E_*=0\), then \(\ell\) vanishes on
\(\mathcal E\). Every row-orthogonal tangent in (5) has
some \(E\in\mathcal E\), and its derivative is \(\ell(E)\).
The necessity proof of Theorem 2 therefore gives
the commutation condition. This proves positivity in all
inexact cases.

An exact convex penalty is also available under these assumptions:
minimize \(\kappa\|RB\|_{\rm F}-g(R)\) on the elliptope.
Let
\(D=\sqrt{4\|K^{\mathsf T}\Lambda L\|_{\rm F}^2+
                 \|L^{\mathsf T}\Lambda L\|_{\rm F}^2}\).
Inequality (7) bounds \(\Delta g\) by
\(D\sqrt{\|Y\|_{\rm F}^2+\|Z\|_{\rm F}^2}=D\|RL\|_{\rm F}\).
As \(L^{\mathsf T}B\) has full row rank,
\(\|RL\|_{\rm F}\le\|RB\|_{\rm F}/\sigma_{\min}^{+}(B)\),
where the denominator denotes the smallest positive singular
value. Thus \(\kappa>D/\sigma_{\min}^{+}(B)\) forces exactness.
On the exact face the unique optimum is \(R_0\). This is the
standard norm-penalty principle applied here with an explicit
multiplier bound.

## 5. Checks and Gaussian privacy calibration

For a small analytic check take \(b=(\sqrt2,1,1)\).
By averaging over swapping the last two coordinates, convexity
allows a penalty minimizer of the form
\(R_{12}=R_{13}=a,\,R_{23}=c\), with diagonal one.
Write \(z=\sqrt{1+c}\), and \(w=\sqrt2 a\).
Positivity is \(|w|\le z\) and \(0\le z\le\sqrt2\).
At fixed \(z\), the objective increases in \(w\), so
\(w=-z\) is optimal: the invariant variance is
\(2(1+z^2+2w)\), and the compressed determinant is
\((2-z^2)(1+z^2-2w)/2\).
The resulting scalar objective is
\[
 2(z-1)^2-\tau\log[(2-z^2)(1+z)^2/2].
\]
The log derivative at \(z=1\) is \(-1\); the unique local,
hence global, minimum for sufficiently small \(\tau\) has
\(z=1-\tau/4+O(\tau^2)\) by strict convexity and the implicit
function theorem. Thus \(v/\tau^2\to1/8\). The exact one-constraint
maximum-entropy matrix at this weight vector is the \(u=1\)
case in Theorem 1, with \(C=I\).

The following standard privacy calibration is separate from
the entropy objective. Assume a fixed noise law \(N(0,\Sigma)\)
on a support \(W_X=\operatorname{ran}\Sigma\), and choose
the neighbor relation only inside the declared invariant data
universe. For a query difference \(d\) between neighbors, their
output affine supports are disjoint if \(d\notin W_X\).
If \(d\in W_X\), define \(s_d^2=d^{\mathsf T}\Sigma^+d\).
In orthonormal support coordinates the log likelihood ratio
under the first law has mean \(s_d^2/2\) and variance \(s_d^2\);
under the second law its mean is \(-s_d^2/2\), same variance.
The positive likelihood ratio test on the common support
therefore gives the exact additive discrepancy at
\(\varepsilon\ge0\):
\[
 \delta_d(\varepsilon)
 =\Phi(s_d/2-\varepsilon/s_d)
     -e^\varepsilon\Phi(-s_d/2-\varepsilon/s_d),
 \quad s_d>0,
 \qquad\delta_0(\varepsilon)=0 .
\]
Specifically, the supremum of \(P(S)-e^\varepsilon Q(S)\)
is obtained on the set where the density of \(P\) exceeds
\(e^\varepsilon\) times that of \(Q\). Swapping \(P,Q\) gives
the same value. This is Balle–Wang's analytic Gaussian formula,
now expressed in the support coordinates; it is monotone in
\(s_d>0\), by differentiating and noting the two density terms
differ by the factor \(e^\varepsilon\). Use the supremum over
the actual neighbor differences for the guarantee. Opposite
cosets require \(\delta\ge1\), while the full feasible support
\(\ker A\) covers all invariant-respecting differences.
At a fixed covariance shape with common scale \(\sigma\),
the corresponding one-tail sufficient threshold is
\(\varepsilon\sigma/\sqrt a-\sqrt a/(2\sigma)\) for the
unscaled squared sensitivity \(a\). This agrees with the
source appendix derivation. It does not assert finite pure
DP for a nontrivial Gaussian or optimality of the entropy
shape for privacy calibration.
