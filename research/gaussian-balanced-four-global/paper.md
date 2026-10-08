---
title: "Four equal Gaussian cells: covariance deformation and tetrahedral rigidity"
author: "mxym/math research project"
date: "8 October 2026"
geometry: margin=25mm
fontsize: 11pt
header-includes:
  - \usepackage{amssymb,amsmath}
---

# Abstract

We prove that a partition of standard Gaussian space into four cells of
probability $1/4$ maximizes the sum of squared first moments precisely when
it is the central regular tetrahedral partition, extended cylindrically
in dimensions above three. Its value is
$12(\arctan\sqrt2)^2/\pi^3$.
The argument introduces a trace-normalized Gaussian covariance value
function. The Gaussian multi-bubble perimeter theorem puts every
full-rank critical value above the tetrahedral value. A constrained
mountain-pass argument would contradict any additional maximizer, but its
covariance domain has a singular boundary. We handle that boundary by
smooth covariance regularization, a normal-cone spectral estimate, and a
uniform separation inequality for balanced winning cells. Rank-two and
rank-one obstructions then exclude all limiting boundary critical points.
The proof is analytic; it uses no numerical search or computer-assisted
Gaussian integration. We state the imported Gaussian isoperimetric
results explicitly. Partial Lean checks cover finite algebra, not the
Gaussian analysis or the complete theorem.

# 1. The theorem and its scope

Let $\gamma_d$ be standard Gaussian probability on $\mathbb R^d$, with
density $(2\pi)^{-d/2}e^{-|x|^2/2}$. A partition is a measurable list
$C_1,\ldots,C_4$, disjoint and covering space up to null sets. Define

$$
 m_i=\int_{C_i}x\,d\gamma_d(x),\qquad F(C)=\sum_{i=1}^4|m_i|^2,
 \qquad \theta=\arctan\sqrt2.
$$

**Theorem 1.** If $d\ge3$ and $\gamma_d(C_i)=1/4$ for every $i$, then

$$
 F(C)\le F_*:=\frac{12\theta^2}{\pi^3}.                 \tag{1}
$$

Equality holds exactly for the following partitions, up to null sets,
orthogonal transformations and relabeling. In an orthogonal
three-dimensional subspace take

$$
 \sigma_1=(1,1,1),\quad \sigma_2=(1,-1,-1),\quad
 \sigma_3=(-1,1,-1),\quad \sigma_4=(-1,-1,1),
$$

and assign $x$ to the label maximizing $\sigma_i\cdot x$. The cells are
central regular tetrahedral cones, with the orthogonal complement
unrestricted.

The same bound and equality classification hold for fractional partitions:
measurable $0\le f_i\le1$ with $\sum_i f_i=1$ almost everywhere and
$\int f_i\,d\gamma_d=1/4$, using $m_i=\int xf_i\,d\gamma_d$.

This solves the equal-mass four-cell first-moment question, including
Heilman's 2014 Conjecture 3 in dimension three [H14], with regularity added
to its stated simplicial-conical classification, and the equal-mass
four-cell case of [H19, Conjecture 1.16]. It does not assert the
arbitrary-mass conjecture, more than four cells, or noise stability at
positive correlation. The arbitrary-mass statement as written in [H19]
is false, as the companion note [EX] explains. The literature screen in
this package is finite and makes no worldwide priority claim.

# 2. Balanced Gaussian assignments and their covariance

Write $\mathbf1=(1,1,1,1)^T$, $P=I-\mathbf1\mathbf1^T/4$ and

$$
 \mathcal K=\{Q=Q^T\succeq0:Q\mathbf1=0,\ \operatorname{tr}Q=1\},
 \qquad Q_*=P/3.
$$

This is a compact convex subset of the six-dimensional Euclidean space
of symmetric matrices annihilating $\mathbf1$, with the Frobenius inner
product. For every such positive semidefinite $Q$, without the trace
restriction, define

$$
 \mathcal C(Q)=\inf_{\lambda\in\mathbb R^4}
 \left\{\frac14\sum_i\lambda_i+
               \mathbb E\max_i(Y_i-\lambda_i)\right\},
 \qquad Y\sim N(0,Q).                                  \tag{2}
$$

Equivalently, it is the largest $\mathbb E Y_I$ among couplings with
$\mathbb P(I=i)=1/4$. At coincident scores such couplings can split tied
labels. Only the dual definition, and the ordinary winning assignment
for distinct scores, are needed below.

For completeness, write $Y=MG$ with centered score rows $v_i$, so
$MM^T=Q$. Fix the gauge $\min_i\lambda_i=0$. The expression in braces,
called $\Psi(M,\lambda)$, is at least $\max_i\lambda_i/4$: choose a
zero-priced label in the pointwise maximum and use its zero Gaussian
mean. Thus a minimizing price exists. For distinct $v_i$, score ties
are null, and differentiation in prices gives

$$
 \partial_{\lambda_i}\Psi=1/4-\gamma(C_i),\qquad
 C_i=\{x:v_i\cdot x-\lambda_i\ge v_j\cdot x-\lambda_j\ \forall j\}.
                                                               \tag{3}
$$

These winning cells therefore have the four required masses. They attain
the linear assignment because the winning score is pointwise largest.
At degenerate scores the coupling interpretation can also be obtained
by approximating $Q$ with positive covariances and taking weakly compact
limits of the four fractional assignments on a common Gaussian space.
The moment integrals pass to the limit because Gaussian coordinates are
in $L^2$.

**Lemma 2 (continuity and scaling).** $\mathcal C$ is continuous on the
closed covariance cone and
$\mathcal C(sQ)=\sqrt{s}\,\mathcal C(Q)$ for $s\ge0$.

*Proof.* Scaling scores and prices proves homogeneity for $s>0$, and
$\mathcal C(0)=0$. Couple $Y=Q^{1/2}G$ and
$\widetilde Y=\widetilde Q^{1/2}G$. For every price the difference of
expected maxima is at most
$\mathbb E|(Q^{1/2}-\widetilde Q^{1/2})G|$. This bound is independent
of prices, hence also bounds the difference of their infima. Continuity
of the matrix square root proves the assertion. $\square$

Suppose now that $Q$ is positive definite on $\mathbf1^\perp$ and take
a centered $4\times3$ matrix $M$ with $MM^T=Q$. The scores are affinely
independent. Every pair has a positive-area winning facet. For its
relatively open part $\Sigma_{ij}$ put

$$
 A_{ij}=\int_{\Sigma_{ij}}\varphi_3\,d\mathcal H^2,
 \quad w_{ij}=\frac{A_{ij}}{|v_i-v_j|},\quad
 (Lu)_i=\sum_{j\ne i}w_{ij}(u_i-u_j).                   \tag{4}
$$

At a lower-rank diagram the same definition in ambient dimension three
is used, with $A_{ij}=0$ for an absent facet. Cylindrical coordinates
integrate to one. Let $B$ be the matrix of actual cell moments.
Gaussian integration by parts gives

$$
 B=LM,\qquad \mathcal C(Q)=\langle M,B\rangle
                  =\operatorname{tr}(LQ).              \tag{5}
$$

Indeed the inward normal to cell $i$ on this facet is
$(v_i-v_j)/|v_i-v_j|$. Truncation by large balls justifies integration
by parts: their additional Gaussian flux tends to zero exponentially.

**Lemma 3 (interior differential identity).** In the positive cone
$\mathcal C$ is smooth, and for every symmetric $D$ with $D\mathbf1=0$,

$$
 d\mathcal C(Q)[D]=\frac12\operatorname{tr}(LD).        \tag{6}
$$

*Proof.* Smoothness can be seen without differentiating moving corners.
The three score differences against label four make a nonsingular affine
change of variables; in those variables all four winning regions are
fixed polyhedral cones. Gaussian density derivatives in the changed
variables are polynomials times locally uniformly dominated Gaussian
densities. The price Hessian is $L$, obtained by normal flux across the
facets. It is positive definite in the gauge $\sum\lambda_i=0$, since
the facet graph is complete. The implicit function theorem gives smooth
balancing prices. This proves smoothness locally everywhere in the
positive cone. Uniqueness of prices in this gauge follows as well:
the Hessian is positive definite along any price segment.

Write $D=MAM^T$ with $A=A^T$, and realize $Q+tD$ using
$M(t)=M(I+tA)^{1/2}$. The envelope derivative of the balanced score value
is $B$, so

$$
 d\mathcal C(Q)[D]=\tfrac12\operatorname{tr}(B^TMA)
                 =\tfrac12\operatorname{tr}(LD).
$$

Every covariance direction has this representation because $M$ maps
onto $\mathbf1^\perp$. $\square$

# 3. Separation of the moments of winning cells

Let $\phi(t)=(2\pi)^{-1/2}e^{-t^2/2}$,
$q=\Phi^{-1}(3/4)$, $h_0=\phi(q)$ and
$k_0=1/(16\phi(0))$.
Every cell of mass $1/4$ has moment norm at most $h_0$:
for a prescribed direction $T=u\cdot X$, let $f$ be any cell indicator
(or fractional indicator) of that mass. Pointwise,
$(T-q)(f-\mathbf1_{T\ge q})\le0$. Integration cancels the $q$ term
by equal masses, giving $\int Tf\le\int_{T\ge q}T=\phi(q)$.
Consequently, for trace-one scores,

$$
 0\le\mathcal C(Q)=\langle M,B\rangle\le2h_0.          \tag{7}
$$

This initially holds in the positive cone, and extends to its boundary
by Lemma 2.

**Lemma 4 (uniform pair separation).** For any distinct-score balanced
winning diagram, and every pair $i\ne j$,

$$
 (b_i-b_j)\cdot\frac{v_i-v_j}{|v_i-v_j|}\ge k_0.        \tag{8}
$$

*Proof.* Put $n=(v_i-v_j)/|v_i-v_j|$ and
$t=(\lambda_i-\lambda_j)/|v_i-v_j|$. On $D=C_i\cup C_j$ the two labels
are separated exactly by $n\cdot X=t$. The subdensity $g$ of $n\cdot X$
restricted to $D$ satisfies $0\le g\le\phi(0)$ and has mass $1/2$.
Both sides of $t$ have mass $1/4$. Thus

$$
 (b_i-b_j)\cdot n=\int|z-t|g(z)\,dz
 \ge\int_0^{1/(4\phi(0))}\left(\tfrac12-2\phi(0)s\right)ds
 =k_0.                                                \tag{9}
$$

Here the constant $t$ cancels by equal masses. The inequality is the
layer-cake formula and the bound on the mass in $[t-s,t+s]$.
No optimality of the squared moment objective is assumed. $\square$

We will also need the price bound

$$
 |\lambda_i-\lambda_j|\le q|v_i-v_j|.                  \tag{10}
$$

Each winning cell lies in its pairwise winning halfspace. Both opposite
halfspaces have probability at least $1/4$, giving (10).

# 4. Boundary continuity of the facet matrix

**Lemma 5.** Suppose centered score lists $M_n\to M_0$ in dimension
three have pairwise separated rows. Let their balanced prices converge
to $\lambda_0$. Then the limiting diagram has four masses $1/4$ and
$L_n\to L_0$, where $L_0$ is its facet matrix. The assertion allows
rank-one or rank-two limits.

*Proof.* Distinct limiting scores have pairwise tie hyperplanes of
Gaussian measure zero. Dominated convergence of the winning indicators
gives the four limiting masses. The same dominated convergence applies
to first moments, since Gaussian coordinates are integrable.

A codimension-one triple tie is impossible in this positive-mass diagram.
Such a tie makes three score vectors affinely collinear with exactly the
same affine relation among their prices. One of the three affine scores
is then globally a strict convex combination of the other two. Its
winning cell is contained in a hyperplane and is null, a contradiction.

For each pair write its facet plane as $n_n\cdot X=t_n$. Its area is
$\phi(t_n)$ times the two-dimensional Gaussian probability of the other
two winning inequalities restricted to that plane. A continuous local
orthonormal frame for $n_n^\perp$ exists near its limiting normal; use it
to express these inequalities in fixed two-dimensional Gaussian
coordinates. A limiting nonconstant inequality has a Gaussian-null
zero set. A constant nonzero one is stable under convergence. A
constant zero inequality would be the prohibited codimension-one triple
tie. Dominated convergence therefore gives each facet area, including
those that tend to zero. Pair separation keeps its denominator nonzero,
proving $L_n\to L_0$. The limiting flux identity (5) holds by the same
integration by parts. $\square$

# 5. A boundary obstruction for self-moment diagrams

**Lemma 6.** There is no balanced four-cell winning diagram in dimension
three whose four distinct inducing vectors are its own cell moments,
whose moment rank is at most two, and whose facet matrix satisfies
$L\preceq P$.

We give the complete proof because this is the boundary hypothesis needed
later; the lemma does not assume global maximality.

First recall the elementary unrestricted three-cell bound

$$
 \sum_{i=1}^3\left|\int_{D_i}x\,d\gamma\right|^2
                \le B_3:=9/(8\pi).                    \tag{11}
$$

To prove it, if its moment sum is $S>0$, divide the centered moments by
$\sqrt S$ to get scores with squared norm sum one. Their span has dimension
at most two, and pointwise maximization gives
$\sqrt S\le\mathbb E\max_i v_i\cdot G$.
The winning cells are at most three planar sectors, possibly empty.
A sector of angle $\alpha$ has moment norm
$\sin(\alpha/2)/\sqrt{2\pi}$. If $x_i=\alpha_i/2$ sum to $\pi$,
$\sum\sin^2x_i=2+2\prod\cos x_i\le9/4$:
a negative cosine makes the product nonpositive; otherwise concavity
of $\log\cos$ bounds the product by $1/8$. Endpoints follow by continuity.
Cauchy--Schwarz for the normalized scores and sector moments now gives
$\mathbb E\max_i v_i\cdot G\le\sqrt{B_3}$, proving (11).
Rank-one cases may be viewed in a plane with an unused coordinate.

The strict profile estimate is

$$
 h_0^2>B_3/4=9/(32\pi),\qquad h_0>3\phi(0)/4.         \tag{12}
$$

Indeed $\pi<22/7<32/9$ gives $\phi(0)>3/8$ and
$e^{-x^2/2}\ge1-x^2/2$ gives
$\Phi(3/4)>1/2+(3/8)(87/128)>3/4$. Thus $0<q<3/4$.
Taylor's theorem implies
$e^{-q^2}>1-9/16+(9/16)^2/2-(9/16)^3/6
=4637/8192>9/16$. This proves both claims in (12).

Now suppose the self-moment rank is two. Write its matrix as $M$.
Flux gives $LM=M$. Hence $W=P-L\succeq0$ annihilates $\mathbf1$ and
the two-dimensional column space of $M$, so

$$
 W=caa^T,\quad c\ge0,\quad a\perp\mathbf1,\quad a^TM=0,
 \qquad w_{ij}=1/4+ca_i a_j.                            \tag{13}
$$

If all four moments are hull vertices, they form a convex quadrilateral.
Its affine dependence has alternating signs, say $a_1,a_3>0$ and
$a_2,a_4<0$. For the scores $s_i=m_i\cdot x-\lambda_i$, the number
$K=\sum a_i s_i=-\sum a_i\lambda_i$ is constant. On an ordinary $13$
facet, $s_1=s_3=T>s_2,s_4$ gives
$K=a_2(s_2-T)+a_4(s_4-T)>0$. On a $24$ facet it gives $K<0$.
Both diagonal facets cannot exist, but (13) gives both positive weights.
This is a contradiction.

Otherwise a moment lies in the hull of the other three. Write
$m_4=\sum_{j=1}^3\alpha_jm_j$, $\alpha_j\ge0$, $\sum\alpha_j=1$.
In (13) take $a=(\alpha_1,\alpha_2,\alpha_3,-1)$.
Then $w_{4j}\le1/4$. Put $t=|m_4|$ and $F=\sum|m_i|^2$.
The classical single-cell Gaussian isoperimetric theorem [B75, ST78]
gives the following perimeter lower bound for the fourth cell, which
has mass $1/4$:

$$
 h_0\le\sum_j A_{4j}\le\tfrac14\sum_j|m_4-m_j|
             \le\tfrac{\sqrt3}{4}\sqrt{F+4t^2}.        \tag{14}
$$

The squared lengths sum to $F+4t^2$ because the four moments sum to zero.
If $t>0$, the convex combination gives some $m_4\cdot m_j\ge t^2$.
Merging these two cells and using (11) yields $F+2t^2\le B_3$.
Projecting all moments onto $m_4/t$, two projections are $t$ and $s\ge t$,
and the other two sum to $-t-s$. Thus
$F\ge t^2+s^2+(t+s)^2/2\ge4t^2$.
For $t=0$ these same two inequalities hold by merging any other cell.
They imply $t^2\le B_3/6$ and $F+4t^2\le4B_3/3$.
Equation (14) now gives $h_0\le\sqrt{B_3}/2$, contradicting (12).
This includes points on hull edges and zero coefficients $\alpha_j$.

For rank one, the four distinct slopes give four ordered intervals,
whose equal masses force endpoints $-q,0,q$. Their own moments are
$(-h_0,h_0-\phi(0),\phi(0)-h_0,h_0)$. The middle facet has weight

$$
 w_{23}=\frac{\phi(0)}{2(\phi(0)-h_0)}>2,
$$

by (12). Hence $\operatorname{tr}L\ge2w_{23}>4$, contradicting
$L\preceq P$ and $\operatorname{tr}P=3$. Rank zero contradicts distinct
moments. This proves Lemma 6. $\square$

# 6. The regular value and its strict local maximum

**Lemma 7.** Put $c_*:=\sqrt{F_*}$. Then
$\mathcal C(Q_*)=c_*$, and $Q_*$ is a strict local maximum of
$\mathcal C$ on $\mathcal K$.

We include the local calculation. For regular scores $m_i^0=a\sigma_i$,
the $12$ facet is the plane $y+z=0$ with wedge
$X\ge|Y|/\sqrt2$. Its angular width is $2\theta$ and Gaussian area is
$\phi(0)\theta/\pi$. Its edge length is $2\sqrt2 a$. Taking
$a=\theta/\pi^{3/2}$ makes every weight $1/4$, so flux gives precisely
the cell moments $m_i^0$. Thus their value is $12a^2=F_*$.
The trace-one scores are $m_i^0/c_*$, with covariance $Q_*$, and their
assignment value is $c_*$.

To check strict local maximality, work near the self-moment list and
remove rotations by polar decomposition. Perturb the scores by the
symmetric map $I+B$, where

$$
 B=\begin{pmatrix}u&b_z&b_y\\b_z&v&b_x\\b_y&b_x&s\end{pmatrix},
 \quad c_0=\frac{\sqrt2}{3\theta},\quad
 h=\frac{\sqrt{\pi/3}}{\theta}.
$$

The latter $h$ is the normalized $X$-mean of the facet wedge: its mass
is $\theta/\pi$ and its unnormalized mean is
$\phi(0)\sqrt{2/3}$. A price variation can be parametrized by an apex
variation $z$, with $\delta\lambda_i=m_i^0\cdot z$ in the zero-sum gauge.
Facet flux gives

$$
 \delta p_i=a\sigma_i\cdot(h(b_x,b_y,b_z)-z).
$$

For example the facet conditional mean is $he_x$ on $12$. Summing all
facet fluxes gives
$\delta p_i=(h/(2a))((m_i^0)^TBm_i^0-a^2\operatorname{tr}B)-m_i^0\cdot z$,
which is the displayed expression. Balanced prices therefore give
$z=h(b_x,b_y,b_z)$.

Set $K_x=c_0(u-(v+s)/2)-(v+s)/2$, with cyclic definitions for $K_y,K_z$.
The two opposite facet-weight derivatives are

$$
 4\delta w_{12}=K_x+(c_0-1)b_x-hz_x,
 \quad4\delta w_{34}=K_x-(c_0-1)b_x+hz_x.              \tag{15}
$$

Here a diagonal perturbation changes the half wedge angle by
$(\sqrt2/3)(u-(v+s)/2)$, and the edge length relatively by $(v+s)/2$.
For $b_x$, the first-order wedge is
$X\ge(1-b_x)|Y|/\sqrt2$: the angle derivative is $(\sqrt2/3)b_x$
and the relative edge derivative is $b_x$. Reflection symmetry makes
the other two off-diagonal angular derivatives zero. Translating the
apex contributes $-A_{12}hz_x$ to its area derivative, with opposite
sign on $34$. These calculations give (15) and its cyclic versions.

Let $H(M)=2\mathcal C(MM^T)-|M|_F^2$. Its score gradient is
$2(B(M)-M)$. At the regular point $L=P$, so

$$
 H''=2\sum_{i<j}\delta w_{ij}\,
          (\delta m_i-\delta m_j)\cdot(m_i^0-m_j^0).
$$

Write $(u,v,s)=\rho(1,1,1)+(u_0,v_0,s_0)$ with sum of the latter zero.
Substitution of (15) and $z=h(b_x,b_y,b_z)$ gives

$$
 H''=-24a^2\rho^2-2a^2(3c_0+1)(u_0^2+v_0^2+s_0^2)
       -8a^2(1+h^2-c_0)(b_x^2+b_y^2+b_z^2).           \tag{16}
$$

The diagonal terms follow from $4a^2\sum K_x(v+s)$; each off-diagonal
pair contributes $-8a^2(1+h^2-c_0)b_x^2$. Also $0<c_0<1$, since
$\arctan\sqrt2>\sqrt2/3$ by the integral defining arctangent.
All coefficients in (16) are strictly negative. Smoothness and Taylor's
theorem give a strict local maximum of $H$ modulo rotations.

For $Q\in\mathcal K$ near $Q_*$ choose centered scores with Gram matrix
$Q$ and multiply them by $c_*$. They have squared norm $F_*$ and are near
the regular self-moment list modulo rotations. Since
$H=2c_*\mathcal C(Q)-F_*$, the preceding strict inequality proves the
claimed strict local maximum on the covariance domain. $\square$

# 7. Perimeter bounds for full-rank critical values

We import the following precise case of the Gaussian multi-bubble theorem
[MN22, Theorem 1.1]: among all four-cell partitions in $\mathbb R^3$
with masses $1/4$, the total Gaussian interface perimeter
$S=\frac12\sum_i P_\gamma(C_i)=\sum_{i<j}A_{ij}$ is at least its value
for the regular tetrahedral fan. The theorem applies because the number
of cells is at most dimension plus one. Its simplicial minimizer is central
in this equal-mass case: for regular scores the balancing prices are unique
modulo a constant by Lemma 3, and symmetry makes all prices equal. The
regular value computed above is

$$
 S_* =6\phi(0)\theta/\pi=c_*\sqrt{3/2}.               \tag{17}
$$

This is an established external theorem, not a new proof of the
multi-bubble result. Its uniqueness part is not needed here.

**Lemma 8.** Any full-rank $Q\in\mathcal K$ at which the trace-constrained
derivative of $\mathcal C$ vanishes satisfies $\mathcal C(Q)\ge c_*$.

*Proof.* By (6), $L=\mu P$ on $\mathbf1^\perp$, and by (5)
$\mathcal C(Q)=\mu$. Each weight is $\mu/4$. Since the rows of $M$
sum to zero and their squared norms sum to one,

$$
 \sum_{i<j}|v_i-v_j|^2=4,\qquad
 S=\frac\mu4\sum_{i<j}|v_i-v_j|
                 \le\mu\sqrt{3/2}.
$$

Combine this upper bound with (17) to get $\mu\ge c_*$.
The perimeter theorem gives a *lower* critical-value bound; the next
argument is necessary to turn it into a global *upper* bound. $\square$

# 8. A constrained mountain-pass lemma with the required sign

**Lemma 9.** Let $K$ be nonempty compact convex in a finite-dimensional
Euclidean space, and let $f$ be $C^2$ on a neighborhood of $K$. Let
$x_0,x_1\in K$. Suppose every continuous path in $K$ joining them meets
a set on which $f\le a<\min(f(x_0),f(x_1))$. Then some $x\in K$ has
$f(x)\le a$ and

$$
 \langle\nabla f(x),y-x\rangle\le0\quad\text{for all }y\in K. \tag{18}
$$

*Proof.* Let $\Gamma$ be these paths and put
$b=\sup_{\gamma\in\Gamma}\min_t f(\gamma(t))\le a$.
The family is nonempty by convexity. Let $\Pi_K$ be Euclidean projection
and $D(x)=\Pi_K(x+\nabla f(x))-x$. The projection inequality tested at
$x\in K$ gives
$\nabla f(x)\cdot D(x)\ge|D(x)|^2$.
Moreover $D(x)=0$ exactly when (18) holds.
This vector field is locally Lipschitz, since $f$ is $C^2$ and projection
is nonexpansive.

If the level $b$ contains no zero of $D$, compactness gives
$\eta,\alpha>0$ with $|D|\ge\alpha$ on
$\{|f-b|\le2\eta\}\cap K$. The level is nonempty by any path and the
intermediate value theorem. Shrink $\eta$ so both endpoint values exceed
$b+2\eta$. Choose a Lipschitz cutoff $0\le\chi\le1$, one for
$|f-b|\le\eta$ and zero for $|f-b|\ge2\eta$.
The flow $x'=\chi(f(x))D(x)$ stays in $K$: every sufficiently small
forward Euler step is a convex combination of $x$ and
$\Pi_K(x+\nabla f(x))$. Euler approximations converge to the locally
Lipschitz flow, giving invariance. Compactness permits any finite
forward time and continuous dependence on the initial point.
Along the flow $f$ never decreases and increases at rate at least
$\alpha^2$ while $|f-b|\le\eta$; the endpoints are fixed.

Choose $\gamma$ with minimum greater than $b-\eta/2$. Applying a fixed
flow time greater than $\eta/\alpha^2$ makes every point on this path
have value at least $b+\eta/2$. Points already above this value do not
descend, and the others reach it within that time. This continuous path
contradicts the definition of $b$. Thus a zero exists at level $b$,
proving the lemma. $\square$

The sign in (18) is the upper normal cone, which is essential below.
The proof uses only Euclidean projection and the elementary existence,
Euler approximation and continuous-dependence theorems for locally
Lipschitz finite-dimensional ODEs. It does not assume nondegenerate
critical points or a smooth boundary of $K$.

# 9. Regularization excludes every additional maximizer

**Theorem 10 (covariance form).** For $Q\in\mathcal K$,
$\mathcal C(Q)\le c_*$, with equality only at $Q_*$.

*Proof.* Suppose $Q_1\ne Q_*$ has $\mathcal C(Q_1)\ge c_*$.
By Lemma 7 choose $r,\delta>0$ so that the closed radius-$r$ ball about
$Q_*$ within the trace affine space lies in the positive cone,
$Q_1$ is outside it, and its boundary has
$\mathcal C\le c_*-\delta$.
For $\varepsilon\downarrow0$ define on $\mathcal K$

$$
 \mathcal C_\varepsilon(Q)=\mathcal C(\widetilde Q),\qquad
 \widetilde Q=(1-\varepsilon)Q+\varepsilon Q_*.
$$

This is smooth on an open neighborhood of $\mathcal K$, and converges
uniformly to $\mathcal C$ by Lemma 2 and compactness.
For small $\varepsilon$, its values at $Q_*,Q_1$ exceed
$c_*-\delta/3$, whereas every joining path meets the sphere with value
at most $c_*-2\delta/3$. Lemma 9 gives $Q_\varepsilon\in\mathcal K$
satisfying the upper-normal condition and

$$
 \mathcal C(\widetilde Q_\varepsilon)\le c_*-2\delta/3.  \tag{19}
$$

Let $L_\varepsilon$ be its full-rank facet matrix. By (6), the
normal condition says that $Q_\varepsilon$ maximizes
$\operatorname{tr}(L_\varepsilon Q)$ on $\mathcal K$.
If $\mu_\varepsilon$ is the largest eigenvalue of $L_\varepsilon$
on $\mathbf1^\perp$, this is equivalent to

$$
 0\preceq L_\varepsilon\preceq\mu_\varepsilon P,\qquad
 (L_\varepsilon-\mu_\varepsilon P)Q_\varepsilon=0.        \tag{20}
$$

Indeed the linear functional on positive trace-one matrices is at most
its top eigenvalue. Equality makes the range of $Q_\varepsilon$ lie in
its top eigenspace; this follows by diagonalizing $L_\varepsilon$ and
using nonnegative diagonal entries of $Q_\varepsilon$ (a zero diagonal
in a positive matrix has zero row).

Choose once and for all a $4\times3$ isometry $U$ onto
$\mathbf1^\perp$ and set
$M_\varepsilon=\widetilde Q_\varepsilon^{1/2}U$,
$B_\varepsilon=L_\varepsilon M_\varepsilon$.
Equations (5) and (20) imply

$$
 \begin{split}
 \mathcal C(\widetilde Q_\varepsilon)
   &=(1-\varepsilon)\mu_\varepsilon+
                     \varepsilon\operatorname{tr}L_\varepsilon/3,\\
 0<\mu_\varepsilon&\le2h_0/(1-\varepsilon),\\
 |B_\varepsilon-\mu_\varepsilon M_\varepsilon|_F^2
   &=\frac\varepsilon3\operatorname{tr}\left[(L_\varepsilon-\mu_\varepsilon P)^2\right]
     \le\varepsilon\mu_\varepsilon^2.
 \end{split}                                           \tag{21}
$$

For the last identity, insert $M_\varepsilon M_\varepsilon^T=
(1-\varepsilon)Q_\varepsilon+\varepsilon P/3$ into the squared norm;
the $Q_\varepsilon$ term vanishes by (20). The three eigenvalues of
$L_\varepsilon$ lie in $[0,\mu_\varepsilon]$, giving the inequality.

Lemma 4 and (21) yield, for every pair,

$$
 k_0\le\mu_\varepsilon
       \bigl(|v_i^\varepsilon-v_j^\varepsilon|+\sqrt{2\varepsilon}\bigr).
                                                               \tag{22}
$$

The factor $\sqrt2$ bounds a difference of two rows of the residual by
$\sqrt2$ times its Frobenius norm. Since $|M_\varepsilon|_F^2=1$,
all pair distances are at most $\sqrt2$. Thus (22) also bounds
$\mu_\varepsilon$ away from zero. Together with its uniform upper bound,
it keeps all score pairs uniformly separated as $\varepsilon\to0$.

Pass to a subsequence with $Q_\varepsilon\to Q_0\in\mathcal K$,
$\mu_\varepsilon\to\mu_0>0$ and $M_\varepsilon\to M_0$.
Normalize prices by minimum zero. Equation (10) bounds them, so take
a further convergent subsequence. Lemma 5 gives balanced limiting cells
and $L_\varepsilon\to L_0$. Their moments satisfy

$$
 B_0=L_0M_0=\mu_0 M_0,\qquad L_0\preceq\mu_0P.         \tag{23}
$$

If $Q_0$ has rank at most two, multiply its scores and prices by $\mu_0$.
The winning cells do not change; their inducing vectors become their
own moments by (23), and their facet matrix becomes $L_0/\mu_0\preceq P$.
Their rows remain distinct, contradicting Lemma 6.
If $Q_0$ has rank three, (23) gives $L_0=\mu_0P$, so Lemma 8 gives
$\mathcal C(Q_0)\ge c_*$. But continuity and (19) give
$\mathcal C(Q_0)\le c_*-2\delta/3$. This is again a contradiction.
There is no $Q_1$ as assumed, proving the theorem. $\square$

# 10. Completion of the partition theorem

Let $M$ have rows $m_i$ for an arbitrary partition in Theorem 1.
Its rows sum to zero, so its rank is at most three, and
$\operatorname{tr}(MM^T)=F$. For every price, its labels are a feasible
linear assignment in (2), giving

$$
 F\le\mathcal C(MM^T).
$$

For $F>0$, Theorem 10 and homogeneity imply
$F\le c_*\sqrt F$, which is (1). The case $F=0$ is strictly smaller.
Equality requires $MM^T=F_*P/3$, by Theorem 10, and equality in the
pointwise optimal assignment. These four regular scores have null ties;
their equal-mass prices are all equal by symmetry and uniqueness.
Hence the original partition is the regular winning partition.
Fractional partitions have the identical feasible-assignment inequality;
equality likewise forces their labels to be the unique winning label
almost everywhere. This proves the stated extension and classification.

As a further consequence, every full-rank balanced self-moment stationary
diagram is regular: its normalized score covariance is an interior critical
point, so Lemma 8 puts its value at least $c_*$ and Theorem 10 puts it
at most $c_*$ with a unique attaining covariance. This is not an assertion
that lower-rank stationary saddles do not exist.

# 11. Dependencies and verification scope

The analytic inputs are the classical single-cell Gaussian isoperimetric
theorem, the Gaussian multi-bubble perimeter theorem [MN22], and elementary
finite-dimensional analysis (dominated convergence, implicit functions,
polar decomposition, spectral decomposition, Gaussian integration by parts,
and locally Lipschitz ODE flow). The three-cell estimate, profile margin,
local tetrahedral calculation, constrained deformation and limiting-rank
obstructions have been proved above.

No floating data, optimized solver, numerical root, or unverified
quadrature sign is a premise of Theorem 1. The older covariance concavity
route is unnecessary; this theorem does not prove that stronger
concavity statement. The partial formal checks in this package explicitly
state their scalar hypotheses and do not formalize Gaussian integrals,
perimeter, the ODE deformation or the complete theorem. Internal model
review is documented separately and is not external human peer review.

# References

- [H14] S. Heilman, *Euclidean Partitions Optimizing Noise Stability*,
  Electronic Journal of Probability 19 (2014), no. 71, 1--37;
  arXiv:1211.7138v2, Conjecture 3 and Definition 1.7.
- [H19] S. Heilman, *Stable Gaussian Minimal Bubbles*,
  arXiv:1901.03934v1, Problem 1.15 and Conjecture 1.16.
- [MN22] E. Milman and J. Neeman, *The Gaussian Double-Bubble and Multi-Bubble
  Conjectures*, Annals of Mathematics 195 (2022), no. 1, 89--206;
  DOI 10.4007/annals.2022.195.1.2; arXiv:1805.10961v3, Theorem 1.1.
- [B75] C. Borell, *The Brunn--Minkowski inequality in Gauss space*,
  Inventiones Mathematicae 30 (1975), 207--216.
- [ST78] V. N. Sudakov and B. S. Tsirelson, *Extremal properties of
  half-spaces for spherically invariant measures*, Journal of Soviet
  Mathematics 9 (1978), 9--18 (Russian original, 1974).
- [KN09] S. Khot and A. Naor, *Approximate Kernel Clustering*,
  Mathematika 55 (2009), 129--165; arXiv:0807.4626v2.
  The three-cell calculation is classical.
- [EX] mxym/math research project, *A counterexample to the prescribed-mass
  Gaussian regular-simplex conjecture*, repository companion
  research/gaussian-fixed-mass-propeller-counterexample, 2026.
- [LOCAL] mxym/math research project, *Rank rigidity and local optimality
  for four balanced Gaussian cells*, repository companion
  research/gaussian-balanced-four-rigidity, commit b627062, 2026.
  The present paper makes the global argument standalone.
