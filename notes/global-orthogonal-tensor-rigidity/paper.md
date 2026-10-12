# Quantitative compatibility of nonlinear matrix Jacobians

mxym repository account, prepared with AI assistance. 7 October 2026.

## Abstract and status

We prove a local coercivity theorem for symmetric linear matrix fields whose nonlinear functional calculus is approximately a Jacobian. The zero set, after sum-of-squares normalization, is the orthogonal orbit of the coordinate cubic tensor. The derivative of the compatibility and normalization defects has exactly the tangent space of that orbit as its kernel. Consequently distance to the orbit is bounded **linearly** by the defects, in any fixed dimension. Gaussian Poincaré then turns an approximately linear inverse-hazard Jacobian into an explicit-order Wasserstein estimate for an exponential product.

As a **conditional application of the precise transport remainder stated in OpenAI family 101**, this proves a square-root Wasserstein stability estimate for its entropy inequality. We supply the complete implication from that remainder, including whitening and passage to nonsmooth densities. We do **not** independently certify the full upstream entropy theorem. Our unconditional results are the compatibility theorem, its Gaussian transport consequence, and the truncated-exponential obstruction to every uniform power greater than one half. Constants depend on dimension; their existence is proved, but numerical values and dimension-free bounds are not claimed. No priority, external peer review, or journal-tier claim is made.

## 1. Definitions and the main compatibility theorem

Fix an integer $m\ge1$. Let

$$
\mathcal V_m=(\operatorname{Sym}_m)^m,
\qquad |X|^2=\sum_{r=1}^m|X_r|_F^2,
\qquad A_X(x)=\sum_r x_rX_r,
\qquad B_X=\sum_rX_r^2.
$$

For an orthonormal basis $u_1,\ldots,u_m$, define

$$
(T_u)_r=\sum_i(u_i)_r u_i u_i^T,
\qquad \mathcal M_m=\{T_u:(u_i)\text{ an orthonormal basis}\}.
\tag{1}
$$

The associated cubic tensor is $\sum_i u_i^{\otimes3}$. Reversing a basis vector includes a negative coefficient; no extra sign parameter is needed. The action of $U\in O(m)$ is

$$
(U\cdot X)_r=U\left(\sum_s U_{rs}X_s\right)U^T.
\tag{2}
$$

It preserves the norm and sends $A_X(U^Tx)$ to $A_{U\cdot X}(x)$ by conjugation. In particular $\mathcal M_m$ is the orbit of $X_r^0=e_re_r^T$.

Let $\Omega=\{x\in\mathbb R^m:|x|<1\}$. For a tensor distribution $Z=(Z_{irs})$, use the Hilbert negative Sobolev norm dual to the componentwise norm

$$
\|v\|_{H_0^1}^2=\sum_{i,r,s}\int_\Omega(|v_{irs}|^2+|\nabla v_{irs}|^2)\,dx.
$$

All distributions and derivatives below are in the ordinary Euclidean variables. For a smooth real function $g$, define

$$
\Phi_g(X)_{irs}=\partial_r(g(A_X))_{is}-\partial_s(g(A_X))_{ir},
\qquad
\mathcal E_g(X)=|B_X-I|_F+\|\Phi_g(X)\|_{H^{-1}(\Omega)}.
\tag{3}
$$

Scalar functions of a real symmetric matrix use spectral functional calculus. The norm in (3) includes all indices, including the redundant antisymmetric pairs.

**Theorem 1 (quantitative nonlinear compatibility).** Suppose $g\in C^\infty(\mathbb R)$ and $g'(0)g''(0)\ne0$. There are $c_{m,g},C_{m,g}>0$ such that

$$
\mathcal E_g(X)\le c_{m,g}
\quad\Longrightarrow\quad
\operatorname{dist}(X,\mathcal M_m)\le C_{m,g}\mathcal E_g(X).
\tag{4}
$$

The result is unconditional. It is not a numerical simultaneous-diagonalization assertion, and needs no entropy inequality or convexity assumption. Its zero-set algebra belongs to the established theory of orthogonally decomposable symmetric tensors; see Section 5. The added statement here measures compatibility of the nonlinear field in a distribution norm and supplies the Gaussian application.

### 1.1 Exact zero set

**Lemma 2.** $B_X=I$ and $\Phi_g(X)=0$ if and only if $X\in\mathcal M_m$.

**Proof.** Vanishing in $H^{-1}$ is distributional vanishing. The field is smooth, so it vanishes pointwise. Expand at $x=0$:

$$
g(A_X(x))=g(0)I+g'(0)A_X(x)+\tfrac12g''(0)A_X(x)^2+O(|x|^3).
$$

The constant term of its curl gives

$$
X_re_s=X_se_r. \tag{5}
$$

Thus $A_X(x)e_s=X_sx$. Its degree-one term gives

$$
(X_rA_X+A_XX_r)e_s=(X_sA_X+A_XX_s)e_r.
$$

Use (5) to cancel the leftmost $A_X$ terms and to rewrite the others. This gives $[X_r,X_s]x=0$, hence every pair commutes. Simultaneously diagonalize the symmetric matrices and rotate the input by the same orthogonal matrix as the output. Condition (5) then says that the $r$-th coefficient has no diagonal entry other than its $r$-th one. The equation $B_X=I$ makes each remaining entry (+1) or (-1). Absorb its sign into the corresponding basis vector. This is (1). Conversely a tensor (1) has $B_X=I$, and

$$
g(A_{T_u}(x))=U\operatorname{diag}(g((U^Tx)_i))U^T
$$

is the Jacobian of $U(G((U^Tx)_i))_i$, where $G'=g$. Its curl is zero. This also proves the lemma for $m=1$. $\square$

### 1.2 The first-order kernel

Write $H_{rij}=(H_r)_{ij}$. Coefficients in $\mathcal V_m$ already satisfy symmetry in (i,j), but not initially in all three indices. Define

$$
\Psi_g(X)=(B_X-I,\Phi_g(X)),
$$

with target norm the sum of the two norms in (3). This is a twice continuously differentiable map to $\operatorname{Sym}_m\oplus H^{-1}(\Omega)$. Here are details that also cover repeated eigenvalues. In an eigenbasis of a symmetric matrix $M$,

$$
(Dg(M)[H])_{ij}=g[\lambda_i,\lambda_j]H_{ij},
$$

$$
(D^2g(M)[H,K])_{ij}
=\sum_\ell g[\lambda_i,\lambda_\ell,\lambda_j]
(H_{i\ell}K_{\ell j}+K_{i\ell}H_{\ell j}).
$$

Divided differences use their continuous values at repeated arguments. On a compact spectral interval their magnitudes are bounded by $\sup|g'|$ and $\sup|g''|/2$, respectively. The formulas follow first for polynomials by differentiating matrix products. Approximate $g$ and its first two derivatives uniformly on a slightly larger interval: the displayed bounds make the derivative maps converge uniformly in finite-dimensional matrix norm. This proves both formulas and continuity of the derivatives without differentiating eigenvectors. On any bounded coefficient set, $|A_X(x)|_F$ is uniformly bounded for $x$ in the unit ball. Differentiate into $L^2(\Omega)$ using these uniform bounds, and apply the bounded distributional curl $L^2\to H^{-1}$. Higher local smoothness needed for the Taylor coefficients follows by the same argument.

**Lemma 3.** At $X^0_r=e_re_r^T$,

$$
\ker D\Psi_g(X^0)=T_{X^0}\mathcal M_m. \tag{6}
$$

**Proof.** Suppose the derivative vanishes in direction $H$. Differentiate the constant Taylor coefficient of the curl with respect to the coefficients. Since $g'(0)\ne0$, this gives

$$
H_re_s=H_se_r.
\tag{7}
$$

Together with matrix symmetry, (7) makes $H_{rij}$ fully symmetric. Differentiate the degree-one curl coefficient. The same cancellation used in Lemma 2, now using (7), gives

$$
[e_re_r^T,H_s]+[H_r,e_se_s^T]=0 \quad(r,s=1,\ldots,m).
\tag{8}
$$

For clarity, this follows by applying the differentiated identity to every $e_t$; $g''(0)/2\ne0$ permits cancellation of its scalar factor. For three distinct indices (r,s,t), the ((r,t))-entry of (8) is $H_{rst}$; hence all distinct-index entries vanish. Its ((r,s))-entry, for $r\ne s$, is

$$
H_{rrs}+H_{rss}=0. \tag{9}
$$

The diagonal entries of

$$
DB(X^0)[H]=\sum_r(e_re_r^TH_r+H_re_re_r^T)
$$

are $2H_{iii}$. Thus $H_{iii}=0$. Its off-diagonal entries are the sums in (9), so impose no further conditions. The remaining directions are exactly

$$
H_{iij}=K_{ji},\qquad H_{ijj}=K_{ij}=-K_{ji},
\quad i\ne j,
\tag{10}
$$

for an arbitrary skew-symmetric matrix $K$, with full tensor symmetry understood. These are the derivatives of $\sum_i(\exp(tK)e_i)^{\otimes3}$ at zero. They are precisely the tangent directions of the orthogonal orbit. Conversely differentiation along that orbit gives zero because $\Psi_g$ vanishes on the entire orbit. $\square$

The map from skew matrices to (10) is injective. Therefore the stabilizer of $X^0$ has zero-dimensional Lie algebra and, as a closed subgroup of a compact group, is finite. The orthogonal orbit is a smooth compact embedded manifold. Equivariance of (3), including rotation of the ball and all tensor indices, transfers (6) to every point of the orbit. In dimension one the orbit consists of two points and its tangent space is zero.

### 1.3 Coercivity and proof of Theorem 1

On the unit normal bundle of this compact manifold, define

$$
a=\min_{P\in\mathcal M_m,\;|H|=1,\;H\perp T_P\mathcal M_m}
\|D\Psi_g(P)[H]\|.
\tag{11}
$$

The minimum exists and is positive by Lemma 3 and continuity. Choose $L<\infty$ so that

$$
\|\Psi_g(P+H)-D\Psi_g(P)[H]\|\le L|H|^2
\tag{12}
$$

whenever $P\in\mathcal M_m$ and $|H|\le1$. Such $L$ follows from the bounded second derivative on that compact neighborhood; increase it to at least one.

For $X$ within distance $\rho=\min(1/2,a/(2L))$ of the orbit, take a nearest point $P$. Differentiating the squared distance along any curve in the orbit shows that $H=X-P$ is normal at $P$. Equations (11)–(12) imply

$$
\mathcal E_g(X)\ge a|H|-L|H|^2\ge(a/2)|H|.
\tag{13}
$$

It remains to ensure that small defects place $X$ in this neighborhood; this is where compactness is used, **only to enter a neighborhood with an already proved linear estimate**. If $|B_X-I|_F\le1$,

$$
|X|^2=\operatorname{tr}B_X\le m+\sqrt m\le2m.
$$

On the compact subset of this ball with distance at least $\rho$ from the orbit, $\mathcal E_g$ has a positive minimum $\eta$, by Lemma 2. If this subset is empty, take $\eta=1$. Set $c_{m,g}=\min(1/2,\eta/2)$ and $C_{m,g}=2/a$. Such defects force distance below $\rho$, and (13) proves (4). These variational definitions specify positive constants without a numerical evaluation. $\square$

The nonlinear assumption is significant. With $g(a)=a$, in dimension two take

$$
X_1=2^{-1/2}\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
X_2=2^{-1/2}\begin{pmatrix}0&-1\\-1&0\end{pmatrix}.
$$

The cubic tensor is fully symmetric and $B_X=I$, so its linear-profile curl vanishes. Nevertheless $[X_1,X_2]\ne0$, hence $X\notin\mathcal M_2$. Thus deleting $g''(0)\ne0$ would invalidate the general theorem.

## 2. Gaussian transport: an unconditional consequence

Let $\gamma_m$ be standard Gaussian measure. Set

$$
t(a)=-\log\Phi(-a),\qquad
q(a)=t'(a)=\frac{\varphi(a)}{\Phi(-a)},
$$

where $\varphi,\Phi$ are the one-dimensional standard Gaussian density and distribution function. Let $\nu_m$ be the law of $(E_1-1,\ldots,E_m-1)$, for independent mean-one exponentials.

We need two elementary facts about $q$. Writing $d=q-a$, Gaussian integration by parts in a tail gives

$$
q'=qd>0,\qquad 1-q'=\operatorname{Var}(G\mid G>a)>0.
$$

Thus $q$ is smooth and (0<q'<1). Also

$$
q'(0)=2/\pi,\qquad
q''(0)=\sqrt{2/\pi}(4/\pi-1)>0.
\tag{14}
$$

For symmetric (M,N), eigenbases $u_i,v_j$ give

$$
u_i^T(q(M)-q(N))v_j=(q(\lambda_i)-q(\mu_j))u_i^Tv_j.
$$

Compare with the identical expression for (M-N), square, and sum. The scalar Lipschitz bound proves

$$
|q(M)-q(N)|_F\le|M-N|_F. \tag{15}
$$

**Theorem 4 (stable inverse-hazard Jacobians).** Suppose $F\in H^1(\gamma_m;\mathbb R^m)$, $A\in L^2(\gamma_m;\operatorname{Sym}_m)$, and $DF=q(A)$ almost everywhere. Choose any symmetric coefficients $X_r$ and put $Y=A-A_X$. There are $b_m,K_m>0$ such that

$$
\epsilon=\|Y\|_{L^2(\gamma_m)}+|B_X-I|_F\le b_m
\quad\Longrightarrow\quad
\inf_{U\in O(m)}W_2(\mathcal L(F-\mathbb EF),U_\#\nu_m)
\le K_m\epsilon.
\tag{16}
$$

Here $W_2^2$ is the infimum of the expected squared Euclidean distance over couplings. No log-concavity assumption is needed in this theorem.

**Proof.** On the unit ball, (15) and the lower Gaussian density bound give

$$
\|q(A_X)-DF\|_{L^2(\Omega)}
\le (2\pi)^{m/4}e^{1/4}\|Y\|_{L^2(\gamma_m)}.
$$

The curl of $DF$ vanishes distributionally because weak mixed derivatives commute. The operator curl from matrix $L^2$ to the tensor $H^{-1}$ in (3) has norm at most $2\sqrt m$: pair against tests, integrate once by parts, and use Cauchy–Schwarz on each of its two sums. Consequently

$$
\mathcal E_q(X)\le |B_X-I|_F+
2\sqrt m(2\pi)^{m/4}e^{1/4}\|Y\|_{L^2(\gamma_m)}.
\tag{17}
$$

Theorem 1 gives $T_u$ within $C_m\epsilon$. Gaussian orthogonality shows

$$
\|A_X-A_{T_u}\|_{L^2(\gamma_m)}=|X-T_u|.
$$

Therefore (15) gives

$$
\|DF-q(A_{T_u})\|_{L^2(\gamma_m)}\le K_m\epsilon.
$$

The centered map

$$
G_u(x)=U\bigl(t((U^Tx)_i)-1\bigr)_{i=1}^m
$$

has Jacobian $q(A_{T_u})$ and law $U_\#\nu_m$. Indeed $\Phi(-G)$ is uniform on $(0,1)$. It belongs to Gaussian $H^1$, since $t(G)$ has second moment two and $q(a)\le q(0)+|a|$. Gaussian Poincaré applied componentwise to $F-\mathbb EF-G_u$ now bounds its squared $L^2$ norm by the squared Jacobian norm. Using the same Gaussian input gives the coupling required in (16). $\square$

## 3. Exact dependency boundary for the entropy application

For a full-dimensional log-concave probability density $f$, write $a_f$ and $C_f>0$ for its mean and covariance, and

$$
\Delta(f)=h(f)-m-\tfrac12\log\det C_f,
\qquad
\widehat\mu_f=\mathcal L(C_f^{-1/2}(Z-a_f)),\quad Z\sim f.
\tag{18}
$$

The following is the **imported hypothesis R**, not a theorem independently proved in this note. For every smooth positive probability density $e^{-V}$ with $c_-I\preceq D^2V\preceq c_+I$, the affine normalization and Gaussian Brenier map of OpenAI family 101 exist, with $F\in H^1(\gamma_m)$, $A=q^{-1}(DF)$, $\mathbb EA=0$, and

$$
X_r=\mathbb E(x_rA),\qquad Y=A-\sum_rx_rX_r,\qquad B=\sum_rX_r^2,
$$

$$
2\Delta(f)\ge\frac1{500}\|Y\|_2^2+
\frac1{1000}\sum_i\omega(\lambda_i(B)),
\tag{R}
$$

where

$$
\omega(\lambda)=\frac{3(\lambda-1)^2}{37+3\lambda}
\left(\frac3{20}+\frac{49}{100}\frac{37}{37+3\lambda}\right)
\min\left(\frac{13}{100},\frac{32}{25\sqrt\lambda}\right).
\tag{19}
$$

At zero take the first term in the minimum. The precise public source is *A sharp entropy bound and the simplex inequality for isotropic constants*, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `transport.tex`, Proposition “Affine normalization,” Lemma “Jacobian equation and finite energy,” and `matrix.tex`, Theorem “The smooth entropy bound with a remainder” (`mat:entropy-smooth`). Its remainder involves $\omega$, not an unspecified norm. These source assertions contain the substantial entropy argument; this note does not replace its audit with our finite checks.

**Corollary 5 (conditional square-root entropy stability).** Assuming R, there are $\delta_m,C_m>0$ such that every density in that smooth class with $0\le\Delta(f)\le\delta_m$ satisfies

$$
\inf_{U\in O(m)}W_2(\widehat\mu_f,U_\#\nu_m)
\le C_m\sqrt{\Delta(f)}.
\tag{20}
$$

The same conclusion holds for every full-dimensional log-concave density if, in addition, one uses the approximation lemma stated in the same source: smooth strongly log-concave approximants converge in $L^1$, in second moments, and in entropy. This extension is separately dependent on that approximation input.

**Proof.** The weight (19) is continuous, positive except at one, and grows like a positive multiple of $\sqrt\lambda$ at infinity. Thus its infimum outside $[1/2,3/2]$ is positive. For sufficiently small deficit, (R) places every eigenvalue in that interval. There the minimum in (19) is $13/100$, and direct rational bounds give

$$
\omega(\lambda)\ge\frac1{200}(\lambda-1)^2.
\tag{21}
$$

Indeed bound the denominator by $83/2$ and $37/(37+3\lambda)$ below by $74/83$. The resulting coefficient is strictly greater than $1/200$. Consequently

$$
\|Y\|_2^2\le1000\Delta(f),\qquad
|B-I|_F^2\le400000\Delta(f).
\tag{22}
$$

Apply Theorem 4 to the normalized map supplied by R. Its centered law $\mu$ has a coupling $Z,G$ with $G\sim U_\#\nu_m$ and

$$
\|Z-G\|_2\le K_m\sqrt{\Delta(f)}=:s.
$$

Let $D=\operatorname{Cov}(Z)$. Since $G$ is centered with covariance $I$,

$$
|D-I|_{\rm op}\le(2\sqrt m+s)s.
\tag{23}
$$

For small enough $s$, $\tfrac12I\preceq D\preceq\tfrac32I$. Scalar spectral calculus gives

$$
\|D^{-1/2}\|_{\rm op}\le\sqrt2,
\qquad |D^{-1/2}-I|_{\rm op}\le2|D-I|_{\rm op}.
$$

Thus the same coupling yields

$$
\|D^{-1/2}Z-G\|_2\le\sqrt2s+2\sqrt m(2\sqrt m+s)s\le C_ms.
\tag{24}
$$

If the affine normalization is $P$, then $D=PC_fP^T$. The matrix $O=D^{-1/2}PC_f^{1/2}$ is orthogonal. Hence the whitened normalized law is $O_\#\widehat\mu_f$. Rotate (24) by $O^T$ and absorb $O^TU$ into the infimum in (20). No bound on $P$ is needed.

For the extension, take the approximants from the stated input. Weak convergence plus convergence of second moments implies $W_2$ convergence; this follows, for example, from uniform integrability of squared norms and a weak-convergence coupling, with truncation of the squared cost. Their means and positive covariance matrices converge, so their whitened laws also converge in $W_2$. Their deficits converge. Extract a subsequence of the optimizing orthogonal matrices, which is possible because $O(m)$ is compact; $U_jG\to UG$ in $L^2$ for $G\sim\nu_m$. Pass to the limit in (20). If the limiting deficit equals the chosen threshold, decrease the theorem threshold by a factor two so approximants are eventually within the smooth threshold. This covers zero deficit as well. $\square$

For deficits above the local threshold, independent coupling of two centered isotropic laws gives $W_2\le\sqrt{2m}$. Thus, if the source's nonnegativity assertion is assumed for all log-concave densities, enlarging $C_m$ extends (20) to all deficit values. This elementary extension adds no new upstream certification.

## 4. The power one half cannot be improved uniformly

This section is unconditional and does not require R. In dimension one let $X_R$ have density

$$
f_R(x)=\frac{e^{-x}}{1-e^{-R}}\mathbf1_{[0,R]}(x),\qquad R\ge10,
$$

and put $p=e^{-R}$, $\mu=\mathbb EX_R$, $\sigma^2=\operatorname{Var}X_R$. Elementary integration gives

$$
\mu=1-\frac{Rp}{1-p},\qquad
\sigma^2=1-v,\quad v=\frac{R^2p}{(1-p)^2},
$$

$$
\Delta_R=\log(1-p)-\frac{Rp}{1-p}-\tfrac12\log(1-v).
\tag{25}
$$

These densities are log-concave and full-dimensional. They need not be smooth at the support boundary, so the obstruction is for the all-log-concave version, not a separate sharpness assertion restricted to the smooth strongly convex class.

**Theorem 6 (optimal uniform power).** For all $R\ge10$,

$$
0<\Delta_R\le R^2e^{-R},\qquad
\inf_{U\in O(1)}W_2(\mathcal L((X_R-\mu)/\sigma),U_\#\nu_1)^2
\ge2e^{-R-1}.
\tag{26}
$$

Therefore for every $\alpha>1/2$ and every $C<\infty$, the bound $W_2\le C\Delta^\alpha$ fails along this family. The square-root power in the conditional all-log-concave consequence cannot be replaced by a larger power, even in dimension one. This does not exclude logarithmic refinements at power one half.

**Proof.** The exponential series gives $e^{10}>20000$. For $R\ge10$, the functions $R^kp$, $k=1,2,3$, decrease. Hence $p<1/20000$, $R^2p<1/200$, $R^3p<1/20$, $1-p>9/10$, and $v<1/100$. The elementary bounds

$$
-\frac z{1-z}\le\log(1-z)\le-z,
\qquad z\le-\log(1-z)\le\frac z{1-z},\quad0\le z<1
$$

give

$$
\Delta_R\ge p(R^2/2-R-1)>0,
\quad
\Delta_R\le\frac{v}{2(1-v)}\le R^2p.
$$

The standardized variable has upper endpoint $b=(R-\mu)/\sigma$ and lower endpoint $-\mu/\sigma>-2$. Since $\sigma^{-1}-1\le2v$,

$$
b+1-R\le2R^3p/(1-p)^2+2Rp/(1-p)<1.
\tag{27}
$$

Every coupling to $E-1$ costs at least its excess beyond $b$, so

$$
W_2^2\ge\mathbb E(E-1-b)_+^2=2e^{-b-1}\ge2e^{-R-1}.
$$

Every coupling to $1-E$ costs at least its excess below $-2$, giving $W_2^2\ge\mathbb E(E-3)_+^2=2e^{-3}$, which is larger than the same lower bound. These are the only two orthogonal choices in dimension one. Finally

$$
\frac{\inf_UW_2}{\Delta_R^\alpha}
\ge\sqrt{2/e}\,\frac{e^{(\alpha-1/2)R}}{R^{2\alpha}}\longrightarrow\infty.
$$

The moment and entropy expressions in (25) were integrated directly; neither a floating-point optimization nor the entropy conjecture is used. $\square$

## 5. Verification, provenance, and remaining work

`checks/check_linearization.py` constructs the constant and first spatial Taylor constraints independently using the truncated polynomial profile $g(a)=a+a^2/2$, together with the derivative of normalization. Exact rational elimination checks the kernel dimension and the explicit rotation generators for $m=1,\ldots,6$. Separate exact rational Householder rotations test the nonlinear algebraic zero-set identities. Missing-constraint negative controls demonstrate that normalization, curl, and input/output tensor compatibility cannot simply be dropped. These finite checks support the algebra; the proofs above establish every dimension and all analytic claims.

`checks/check_truncation.py` uses integration-by-parts polynomial identities, rational bounds for exponentials and logarithms, and independent quantile tail integrals to test the explicit obstruction. It provides certified intervals at selected integer $R$, never using rounded floating values as proof inputs. The all-$R$ conclusion is the analytic argument in Section 4.

The exact equality compatibility argument is attributed to the pinned family-101 `rigidity.tex`, Lemma “Rigidity of a linear matrix field.” Our additions are its quantitative transverse-kernel analysis, linear coercivity for a general nonlinear profile, the Gaussian estimate, the complete conditional square-root implication, and the power obstruction. Standard ingredients are spectral functional calculus, Gaussian Poincaré, finite-dimensional compactness and tubular normal directions; none is claimed as a new method on its own.

The Lean file formal/JacobianKernel.lean proves, for an arbitrary index type and real entries, that full tensor symmetry, the entrywise first-order commutator equations, and the diagonal normalization equations imply a skew-matrix rotation representation. Its three exported lemmas have only propext, Classical.choice, and Quot.sound in their reported axiom sets. This covers the forward algebraic kernel calculation in Lemma 3; it does not formalize Taylor extraction, analytic coercivity, Wasserstein transport, or R.

Boralevi–Draisma–Horobeț–Robeva, *Orthogonal and unitary tensor decomposition from an algebraic perspective*, [arXiv:1512.08031](https://arxiv.org/abs/1512.08031), [DOI 10.1007/s11856-017-1588-6](https://doi.org/10.1007/s11856-017-1588-6), establishes an algebraic framework for orthogonally decomposable tensors and their relation to associative algebras. That zero-set viewpoint is prior work, not a new concept of this note. We inspected its primary text, especially Lemma 11, Proposition 12 and the higher-order reduction, as well as its bibliographic record; a complete literature comparison remains pending. The particular nonlinear distribution-norm coercivity and entropy implication require comparison beyond that preliminary check.

Remaining limits: no explicit numerical $C_m$, no dimension-free bound, no Banach–Mazur stability theorem for convex bodies, no relative-entropy or total-variation conclusion, and no independent certification of the global entropy remainder R. The square-root conclusion is **conditional on R**, even though the compatibility theorem and sharpness obstruction are unconditional. No theorem about Mahler, Fujita, Ryser, or Borsuk is claimed here.
