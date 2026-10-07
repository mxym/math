---
title: Effective stability at the symmetric projection-cone endpoint
author: mxym
date: 7 October 2026
abstract: |
  Let $a(K)$ be the affine projection-cone invariant, and let $\mathcal E_d$
  be the class of linear images of Cartesian products of centrally symmetric
  convex bodies of dimensions one and two. For every centrally symmetric
  full-dimensional convex body in $\mathbb R^d$, $d\ge3$, we prove
  $D_{\rm BM}(K,\mathcal E_d)-1\le d^{15}(\tfrac12-a(K))^{1/(6d)}$.
  The estimate imposes no regularity or discreteness assumption. Its proof
  quantitatively excludes long near-half-mass cofactor circuits by a contact-slab
  estimate, then constructs a matching of line and plane normal blocks and
  recovers an actual product using mixed volumes. Corner-truncated cubes have
  upper-end deficit of order $t^d$ and distance at least $t/(5d^2)$ from the
  entire equality class, excluding every universal exponent greater than $1/d$.
---

## 1. The theorem and explicit constants

Let \(K\subset\mathbb R^d\) be any full-dimensional centrally symmetric convex
body, with its center translated to zero. There is no polytope, smoothness,
strict-convexity, absolute-continuity, or positive-curvature assumption. Retain
the entry005 invariant
\[
 a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1,
 \qquad R(K)=\frac{|\Pi K|}{|K|^{d-1}}.
\]
Let \(\mathcal E_d\) consist of all linear images of Cartesian products of
centrally symmetric factors of dimensions one and two. For centered symmetric
bodies use
\[
 d_{\rm BM}(K,L)=\inf\{\lambda\ge1:\ TL\subseteq K\subseteq\lambda TL,
                  \ T\in\mathrm{GL}(d)\},
 \qquad D(K,\mathcal E_d)=\inf_{E\in\mathcal E_d}d_{\rm BM}(K,E).
\]
Write \(\delta=\tfrac12-a(K)\), which is nonnegative by v3.

**Theorem A. Explicit power stability for the entire equality class.** For
\(d=1,2\), \(D(K,\mathcal E_d)=1\). For every \(d\ge3\), define
\[
 \begin{aligned}
 N&=d+1, &\kappa_d&=\frac{\pi^{d/2}}{\Gamma(1+d/2)}, &a_d&=d^{-2d},\\
 Z_d&=\frac{2^{d+9}N\sqrt d\binom d3}{\kappa_d},
 &F_d&=13N+3Z_d, & B_d&=\frac{4NF_d}{a_d},\\
 L_d&=6d^3a_d^{-4}B_d^{1/4},
 &H_d&=d(\sqrt d+1)L_d,
 &C_d&=2d(2dH_d)^{1/d}.
 \end{aligned}
\]
Then, for every such \(K\),
\[
 \boxed{D(K,\mathcal E_d)-1\le C_d\delta^{1/(6d)}.}                 \tag{1.1}
\]
In particular, \(C_d\le d^{15}\), so the following simple numerical version
holds in every dimension \(d\ge3\):
\[
 \boxed{D(K,\mathcal E_d)-1\le
        d^{15}\bigl(\tfrac12-a(K)\bigr)^{1/(6d)}.}              \tag{1.1a}
\]
Equivalently, \(\delta\le(\varepsilon/d^{15})^{6d}\) guarantees a
Banach–Mazur factor at most \(1+\varepsilon\).
All constants are numerical functions of dimension. They are deliberately
conservative. A more informative small-deficit bound is
\[
 D(K,\mathcal E_d)
 \le\frac1{1-(2dH_d\delta^{1/6})^{1/d}},                         \tag{1.2}
\]
whenever
\[
 0<\delta\le\delta_d^*:=
       \left(\frac{2^{-d}}{2dH_d}\right)^6.                       \tag{1.3}
\]
At zero deficit the v4 equality classification applies, or the zero-defect
versions of the lemmas below give the same conclusion directly.

**Theorem B. A dimensional obstruction.** For \(d\ge3\) and \(0<t\le1\), set
\[
 K_t=[-1,1]^d\cap\{x:\ |x_1+\cdots+x_d|\le d-t\},
 \qquad c_d=\frac12-2^{1-d}.
\]
Then
\[
 1+\frac{t}{5d^2}\le D(K_t,\mathcal E_d)\le\frac d{d-t},          \tag{1.4}
\]
and
\[
 \frac12-a(K_t)
 =c_d\frac{2^d-2t^{d-1}/(d-1)!}{d2^d-2t^d/(d-1)!}
       \frac{2t^d}{(d-1)!2^d+2(d-1)t^{d-1}}
 \sim\frac{c_d}{d!2^{d-1}}t^d.                                  \tag{1.5}
\]
Consequently no universal fixed-dimensional power exponent greater than
\(1/d\) is possible. No positive exponent independent of dimension can work,
even when its constants are allowed to depend on dimension. The optimal
exponent remains between \(1/(6d)\) and \(1/d\); neither theorem identifies it.

The proof combines three effective estimates: a cone-specific contact-slab
bound, a quantitative matching of basis coordinates, and a mixed-volume
containment argument. The hypothesis and equality class differ from those
of the lower-end simplex stability problem.

## 2. Cone law, contact identity, and the exact upper-end defect

Sections 2–5 assume \(d\ge3\); dimensions one and two were settled in the
statement.

The v3 cone law is the pushforward of
\(h_K(u)dS_K(u)/(d|K|)\) by \(u\mapsto u/h_K(u)\). Denote it by \(\nu_K\).
For independent samples define
\[
 A=\mathbb E|\det(X_1,\ldots,X_d)|,
 \qquad
 B=\mathbb E\left|\det\begin{pmatrix}X_1&\cdots&X_N\\1&\cdots&1\end{pmatrix}\right|.
\]
We import the v3 identity \(a(K)=B/(NA)\), affine invariance, and the balanced
Rademacher inequality. These hold for arbitrary convex bodies, by the
surface-area formulation and the continuity argument proved there. The law is
even for symmetric \(K\).

Put \(K\) in symmetric John position:
\[
 B_2^d\subseteq K\subseteq\sqrt d B_2^d.                          \tag{2.1}
\]
Then \(\nu_K\) is supported in the unit ball and \(|K|\ge\kappa_d\).
The law can also be sampled by a regular boundary contact \(Y\in\partial K\),
with density
\[
 \frac{\langle Y,n_K(Y)\rangle}{d|K|}\,d\mathcal H^{d-1}(Y),
 \qquad X=\frac{n_K(Y)}{\langle Y,n_K(Y)\rangle}.
\]
The nonregular boundary has surface measure zero. The divergence theorem gives
\[
 \langle Y,X\rangle=1,
 \qquad \mathbb E[Y X^{\mathsf T}]=I/d.                          \tag{2.2}
\]
For every unit vector \(v\), since \(|Y|\le\sqrt d\),
\[
 \mathbb E|\langle v,X\rangle|\ge\frac1{d\sqrt d}.
\]
Conditioning on successive samples and using distance to their span, this
implies
\[
 A=\mathbb E\|X_1\wedge\cdots\wedge X_d\|
 \ge d^{-3d/2}\ge a_d.                                         \tag{2.3}
\]
Indeed, for every fixed proper subspace choose a unit vector perpendicular to
it; the conditional expected distance of the next sample to that subspace is
at least \(d^{-3/2}\). Multiplying these lower bounds proves (2.3), with
dependent partial tuples contributing zero harmlessly. Hadamard gives
\(A\le1\).

For an \(N\)-tuple, let \(c_i\) be its signed horizontal cofactors and put
\(M=\sum|c_i|\). Their relation is \(\sum c_iX_i=0\). Since the points lie
on \(\partial K^\circ\), the Minkowski norm with unit ball \(K^\circ\) gives
\(|c_i|\le M/2\). On \(M>0\), sort the normalized magnitudes as
\(t_1\ge\cdots\ge t_N\), and put
\[
 \mathscr D(t)=\frac12-
        \mathbb E_\epsilon\left|\sum_i\epsilon_i t_i\right|,
 \qquad g=\frac12-t_1.
\]
Define expressions involving \(t\) to be zero on \(M=0\). Sign averaging the
lifted determinant, using evenness, gives the exact identity
\[
 \Delta:=\mathbb E[M\mathscr D(t)]=NA\delta,
 \qquad \mathbb E M=NA\le N.                                   \tag{2.4}
\]
This includes singular tuples. Let \(\phi=Mt_4\) be the fourth-largest
absolute cofactor, set to zero if all cofactors vanish.

## 3. Robust balanced equality and the cone-specific half-mass gate

**Lemma 3.1.** For balanced normalized coefficients as above,
\[
 \mathscr D(t)\ge\min\{t_4/2,g/4\}.                             \tag{3.1}
\]
Their \(\ell_1\)-distance to the entire coefficient equality set (at most
three nonzero entries, or one entry equal to one half) is at most
\(8(N-3)\mathscr D(t)\).

**Proof.** On the capped simplex
\(\{s_i\ge0,\ \sum s_i=1,\ s_i\le1/2\}\), the convex function
\(\mathbb E_\epsilon|\sum\epsilon_i s_i|\) is at most one half by the v3
inequality. Let \(y=(1/4,1/4,1/4,1/4,0,\ldots)\), whose value is \(3/8\).
Set \(\alpha=\min(4t_4,2g)\). If positive, \(\alpha<1\), and
\((t-\alpha y)/(1-\alpha)\) remains in the capped simplex: nonnegativity
uses \(\alpha\le4t_4\); for the first four entries the upper cap is
equivalent to \(t_i+\alpha/4\le1/2\); for the others it follows from
\(\alpha\le2g\). Convexity yields a defect at least \(\alpha/8\), proving
(3.1). If \(\alpha=0\), (3.1) is immediate. To reach the half-mass branch,
increase \(t_1\) by \(g\) and subtract that mass from the other entries,
costing \(2g\). To reach three-point support, remove the tail of mass
\(q\le(N-3)t_4\) and redistribute it in the first three entries without
exceeding the cap, costing \(2q\). Their available capacity is \(1/2+q\).
Use the first construction when the minimum in (3.1) is \(g/4\), and the
second otherwise. This proves the distance bound. \(\square\)

The half-mass branch cannot be dropped: \((1/2,1/6,1/6,1/6)\) has zero
defect and four positive entries. Exact exposedness in v4 removes it at
equality, but does not supply a quantitative margin. We instead use contact
geometry.

**Lemma 3.2. Corner-slab surface area.** If \(Q\subseteq[-1,1]^d\) is any
convex body, the regular boundary part where some three coordinates are within
\(r>0\) of independently chosen signed cube faces has area at most
\[
 d2^{d+1}\binom d3r^2.                                         \tag{3.2}
\]

**Proof.** Fix a triple and its signs and write \(\ell=\min(r,2)\). Each
coordinate projection of the relevant boundary part is contained in a box of
\((d-1)\)-volume at most \(2^{d-3}\ell^2\). If the deleted coordinate is
outside the triple, the sharper bound is \(2^{d-4}\ell^3\), which is no
larger. For any measurable boundary part \(H\), the area formula and convexity
give
\[
 \int_H |n_i|\,d\mathcal H^{d-1}\le2|\pi_iH|.
\]
Almost every fiber has at most an upper and a lower boundary point with nonzero
normal component. Parallel boundary segments have zero such component. Since
\(\sum_i|n_i|\ge1\), summing gives area at most \(d2^{d-2}r^2\) for one
signed triple. There are \(8\binom d3\) choices, proving (3.2), also when
\(r\ge2\). \(\square\)

**Lemma 3.3. Weighted exclusion of long near-half-mass circuits.** For
\(0<\eta\le1/4\) and \(\rho>0\),
\[
 \mathbb E\bigl[M\mathbf1_{\{t_4>\rho,\ g\le\eta\}}\bigr]
 \le Z_d(\eta/\rho)^2.                                        \tag{3.3}
\]
The event is understood on \(M>0\), as already implied by \(t_4>\rho\).

**Proof.** Take a union over the distinguished index \(k\) with
\(|c_k|/M\ge1/2-\eta\), and condition on the other \(d\) samples, arranged
as columns of a matrix \(U\). If \(\det U=0\), this event at \(k\) is
impossible. Otherwise put \(D_0=|\det U|\), \(X_k=U\alpha\), and
\(S=\sum|\alpha_j|\). Cofactor identities give
\[
 |c_k|=D_0,\quad |c_j|=D_0|\alpha_j|,
 \quad M=D_0(1+S),\quad \frac{|c_k|}M=\frac1{1+S}.
\]
On this event \(M\le4D_0\) and \(S-1\le8\eta\). The condition
\(t_4>\rho\) supplies at least three other coordinates with
\(|\alpha_j|>\rho\).

Set \(Q=U^{\mathsf T}K\). Because the columns of \(U\) belong to
\(K^\circ\), \(Q\subseteq[-1,1]^d\) and \(|Q|=D_0|K|\). Under a
primal linear map \(T\), normalized cone mass is preserved and the scaled
normal becomes \(T^{-\mathsf T}X\); hence
\(\nu_Q=(U^{-1})_*\nu_K\). This follows directly from the regular-boundary
formulas
\[
 n'=\frac{T^{-\mathsf T}n}{|T^{-\mathsf T}n|},\quad
 dH'=|\det T|\,|T^{-\mathsf T}n|\,dH,\quad
 h'=h/|T^{-\mathsf T}n|.
\]
For every regular contact \(z\in\partial Q\) generating the conditional
sample \(\alpha\), \(\langle\alpha,z\rangle=1\), so
\[
 \sum_j|\alpha_j|\bigl(1-\operatorname{sgn}(\alpha_j)z_j\bigr)
 =S-1\le8\eta.
\]
The three substantial coordinates therefore put \(z\) within
\(r=8\eta/\rho\) of three signed cube faces. Lemma 3.2 bounds their
surface area. The boundary cone density on \(Q\) is
\(\langle z,n_Q(z)\rangle/(d|Q|)\le\sqrt d/(dD_0|K|)\), so the
conditional probability is at most
\[
 \frac{2^{d+1}\sqrt d\binom d3}{D_0|K|}(8\eta/\rho)^2.
\]
Multiplication by \(M\le4D_0\) cancels the determinant exactly. Integrate
the conditioning variables, sum over \(N\) indices, and use
\(|K|\ge\kappa_d\). The resulting constant is \(Z_d\). \(\square\)

This cancellation treats arbitrarily ill-conditioned conditional matrices.
The estimate uses regular primal contacts, not strong exposedness of polar
points, so atoms caused by flat faces and nonatomic cone laws are both covered.

**Lemma 3.4. Effective short-cofactor estimate.**
\[
 \boxed{\mathbb E\phi\le F_d\delta^{2/3}.}                       \tag{3.4}
\]

**Proof.** First suppose \(0<\delta<1/4\). For
\(\rho\in[\delta,1/4]\), put \(\eta=\delta^{1/3}\rho^{2/3}\le\rho\).
In the weighted tail
\(T(\rho)=\mathbb E[M\mathbf1_{\{t_4>\rho\}}]\), the part with
\(g>\eta\) costs at most \(4\Delta/\eta\) by Lemma 3.1. The other part
costs at most \(Z_d(\eta/\rho)^2\) by Lemma 3.3. Using (2.4),
\[
 T(\rho)\le(4N+Z_d)\delta^{2/3}\rho^{-2/3}.
\]
Since \(t_4\le1/4\), Tonelli gives
\(\mathbb E\phi=\int_0^{1/4}T(\rho)\,d\rho\). The interval below
\(\delta\) costs at most \(N\delta\le N\delta^{2/3}\); the remaining
integral of \(\rho^{-2/3}\) is at most 3. This gives (3.4). If
\(\delta\ge1/4\), use \(\mathbb E\phi\le N/4\le N\delta^{2/3}\).
If \(\delta=0\), for fixed \(\rho>0\) let \(\eta\downarrow0\) in the
same split, with \(\eta\le\min(1/4,2\rho)\), to get \(T(\rho)=0\).
Tonelli proves (3.4) at zero without compactness. \(\square\)

## 4. A quantitative matching of line and plane blocks

**Lemma 4.1.** Let \(\nu\) be any Borel probability law supported in the
unit ball, with \(A\ge a\), \(0<a\le1\), and suppose its expected fourth absolute
cofactor is at most \(\varepsilon\). Put
\(q=4(d+1)\varepsilon/a\). If \(0<q\le1\), there are a basis matrix
\(U\) and a partition of its coordinate indices into singletons and pairs,
with coordinate block union \(\mathcal W\), such that
\[
 |\det U|\ge a/2,\quad \|U\|\le\sqrt d,\quad
 \|U^{-1}\|\le2\sqrt d/a,
\]
\[
 \mathbb E\operatorname{dist}(U^{-1}X,\mathcal W)
 \le6d^3a^{-4}q^{1/4}.                                       \tag{4.1}
\]
For \(\varepsilon=0\), the same conclusion holds with zero distance.
All statements include nonatomic laws and singular sampled tuples.

**Proof.** For a deterministic candidate basis \(b=(b_1,\ldots,b_d)\),
define its section cost
\[
 Q(b)=\int\phi(b,x)d\nu(x)
 +\sum_{j=1}^d\iint\phi(b_1,\ldots,\widehat b_j,\ldots,b_d,x,y)
                         d\nu(x)d\nu(y).
\]
Tonelli gives \(\mathbb E_bQ(b)\le(d+1)\varepsilon\). Since
\(|\det b|\le1\), the event \(|\det b|\ge a/2\) has probability at
least \(a/2\). Markov gives \(\mathbb P(Q>q)\le a/4\). Thus choose
\(U=(b_i)\) with \(D:=|\det U|\ge a/2\) and \(Q(U)\le q\).
The norm bounds follow from unit-length columns and inverse rows, each of
length at most \(1/D\). Cramer's rule also gives
\(|\alpha_i|\le1/D\) for \(\alpha=U^{-1}X\).

Let \(s_3\) be the third-largest coordinate magnitude. The absolute cofactors
of \((b_1,\ldots,b_d,X)\) are \(D\) times
\((1,|\alpha_1|,\ldots,|\alpha_d|)\). If \(s_3\le1\), its fourth
largest is at least \(Ds_3\); otherwise it is at least \(D\), and
\(s_3\le1/D\). In both cases
\[
 \mathbb E s_3\le q/D^2.                                      \tag{4.2}
\]
Fix \(0<t\le1\) and set \(r=Dt^2/2\). Break coordinate ties by index.
For each pair \(ij\), let \(E_{ij}\) be the event that its coordinates are
the largest two, both have magnitude at least \(t\), and \(s_3\le r\).
Write \(p_{ij}=\nu(E_{ij})\).

For distinct \(i,j,k\), take \(x\in E_{ij}\), \(y\in E_{jk}\), with
coordinates \(\alpha,\beta\). In the tuple consisting of the basis except
\(b_j\), followed by \(x,y\), the cofactors attached to \(x,y,b_i,b_k\)
have, up to signs, the values
\[
 D\beta_j,\quad D\alpha_j,\quad
 D(\alpha_i\beta_j-\alpha_j\beta_i),\quad
 D(\alpha_k\beta_j-\alpha_j\beta_k).
\]
These are determinant identities without a rank assumption. The first two
have magnitude at least \(Dt\). Each of the last two has magnitude at least
\(D(t^2-r/D)=Dt^2/2\), since the unwanted coordinate is at most \(r\)
and the other factor at most \(1/D\). Hence
\[
 p_{ij}p_{jk}\le\frac{2q}{Dt^2}.
\]
Pairs with mass exceeding \(w=\sqrt{2q/D}/t\) form a matching. Take its
pairs as plane blocks and every remaining index as a line block. Discarded
pairs have total mass at most \(\binom d2w\).

Outside the discarded-pair events and \(\{s_3>r\}\), a point is within
\(\sqrt d\,t\) of its block: if its second coordinate is below \(t\), use
the block containing its largest coordinate; otherwise use its matched pair,
whose remaining coordinates are at most \(r\le t\). Every point has
coordinate norm at most \(\sqrt d/D\). By (4.2) and Markov,
\[
 \mathbb E\operatorname{dist}(\alpha,\mathcal W)
 \le\sqrt d\,t+\frac{\sqrt d}{D}
 \left[\binom d2\frac{\sqrt{2q/D}}t+\frac{2q}{D^3t^2}\right].     \tag{4.3}
\]
Take \(t=q^{1/4}\). Since \(q\le1\) and \(D\ge a/2\), the right
side is at most
\[
 \sqrt d\,[1+4\binom d2a^{-3/2}+32a^{-4}]q^{1/4}
 \le6d^3a^{-4}q^{1/4}
\]
for \(d\ge3\). This proves (4.1).

At \(\varepsilon=0\), choose \(Q(U)=0\) on the determinant-good event.
Equation (4.2) makes every sample two-sparse almost surely. If two positive-mass
two-coordinate classes shared an index, the displayed omitted-basis tuple
would have four nonzero cofactors on their product, contradicting its
zero section cost. Thus the positive-mass pairs form a matching and the
coordinate distance is zero. This also proves the zero case. \(\square\)

The basis is selected with simultaneous control of all required sections.
Its condition number is bounded explicitly. No limiting choice of a basis or
unique product decomposition is assumed.

## 5. From approximate normals to an actual product body

**Lemma 5.1.** Suppose \(Q\) is a full-dimensional centered symmetric convex
body, \(Q\subseteq R B_2^d\),
and \(\mathbb R^d=\bigoplus_jW_j\) is an orthogonal sum. Set
\(\mathcal W=\bigcup_jW_j\) and
\(P=\prod_j\operatorname{proj}_{W_j}Q\), with \(m\) blocks. If
\(s=\mathbb E_{\nu_Q}\operatorname{dist}(X,\mathcal W)\), then
\[
 |P|/|Q|\le(1+R(\sqrt m+1)s)^d.                               \tag{5.1}
\]
Putting \(v=R(\sqrt m+1)s\), if \(2dv<1\),
\[
 (1-(2dv)^{1/d})P\subseteq Q\subseteq P.                       \tag{5.2}
\]

**Proof.** The projection product contains \(Q\), is symmetric, and lies in
\(\sqrt m R B_2^d\). Its support function agrees with \(h_Q\) on every
block. For \(x\in\partial Q^\circ\), choose a closest block projection
\(z\in\mathcal W\). Support functions are globally Lipschitz with their
circumradii, so
\[
 0\le h_P(x)-1=h_P(x)-h_Q(x)
 \le R(\sqrt m+1)|x-z|.
\]
The cone-law definition, homogeneity, and the first mixed-volume formula give
\[
 \frac{V(Q[d-1],P)}{|Q|}-1
 =\mathbb E_{\nu_Q}[h_P(X)-1]\le v.
\]
Minkowski's first inequality gives (5.1). Consequently
\(\theta=1-|Q|/|P|\le1-(1+v)^{-d}\le dv\).

For completeness, a symmetric nested-body cap converts this relative volume
loss to containment. Let \(\lambda\) be maximal with \(\lambda P\subseteq Q\);
then \(0<\lambda\le1\). If \(\lambda<1\), a touching supporting direction
\(u\) and point \(p\in P\) satisfy
\(h_Q(u)=\lambda h_P(u)\), \(\langle u,p\rangle=h_P(u)\). The image
\[
 \lambda p+(1-\lambda)\bigl(P\cap\{z:\langle u,z\rangle\ge0\}\bigr)
\]
lies in \(P\) by convexity and outside \(\operatorname{int}Q\) by support.
Symmetry makes its volume \((1-\lambda)^d|P|/2\). Hence
\(\theta\ge(1-\lambda)^d/2\), proving (5.2). No inverse cone-volume
uniqueness theorem is used. \(\square\)

**Proof of Theorem A.** Use (2.1). Lemma 3.4 gives
\(\varepsilon=F_d\delta^{2/3}\). By (2.3), apply Lemma 4.1 with
\(a=a_d\), so \(q=B_d\delta^{2/3}\). For \(\delta\le\delta_d^*\),
\(q\le1\): indeed \(H_d\ge B_d^{1/4}\), so
\(B_d(2^{-d}/(2dH_d))^4\le1\). The resulting coordinate law satisfies
\[
 \mathbb E\operatorname{dist}(U^{-1}X,\mathcal W)
 \le L_d\delta^{1/6}.
\]
Apply the primal map \(U^{\mathsf T}\). Its body
\(Q=U^{\mathsf T}K\) lies in \(dB_2^d\), because
\(\|U\|\le\sqrt d\), and its cone law is the coordinate law just obtained.
Its blocks are orthogonal coordinate lines and planes. Lemma 5.1 gives
\(v\le H_d\delta^{1/6}\), with a product \(P\in\mathcal E_d\), proving
(1.2). In the range (1.3), the quantity
\(r=(2dH_d\delta^{1/6})^{1/d}\) is at most \(1/2\), so
\[
 D(K,\mathcal E_d)-1\le\frac r{1-r}
 \le2(2dH_d)^{1/d}\delta^{1/(6d)}.
\]
For larger deficits, a universal elementary bound is
\(D(K,\mathcal E_d)\le d\). In John position,
\(d^{-1/2}[-1,1]^d\subseteq K\subseteq d^{1/2}[-1,1]^d\), and the cube
belongs to \(\mathcal E_d\). If \(\delta\ge\delta_d^*\), the constant in
(1.1) satisfies
\[
 C_d\delta^{1/(6d)}\ge
 2d(2dH_d)^{1/d}(\delta_d^*)^{1/(6d)}=d,
\]
which covers \(D-1\le d-1\). At zero use the zero cases of the lemmas or
v4. For \(d=1,2\), every symmetric body is itself an allowed factor. This
completes the proof. \(\square\)

For the stated simpler constant, the cube inscribed in the unit ball gives
\(\kappa_d\ge(2/\sqrt d)^d\). Using \(N\le2d\) and \(\binom d3\le d^3\),
one obtains
\[
 Z_d\le2^{10}d^{d/2+9/2},\quad
 F_d\le2^{12}d^{d/2+9/2},\quad
 B_d\le2^{15}d^{(5/2)d+11/2},
\]
\[
 H_d\le12\,2^{15/4}d^{(69/8)d+47/8},\qquad
 C_d^d\le2^d(24\,2^{15/4})d^{(77/8)d+55/8}.
\]
Since \(2^d\le d^d\) and \(24\,2^{15/4}<512\le d^6\) for \(d\ge3\),
\[
 C_d^d\le d^{(85/8)d+103/8}\le d^{15d},
\]
where the last inequality is \(35d\ge103\). This proves (1.1a).

## 6. Proof of the dimensional obstruction

We give the full-class argument, since comparing only to the cube would not
establish a distance lower bound to arbitrary planar-factor products.

Let \(D\in\mathcal E_d\) and suppose
\(K_t\subseteq D\subseteq(1+s)K_t\). Any defining Banach–Mazur sandwich
can be rescaled into this form, preserving \(\mathcal E_d\). Write
\[
 D=F_1+\cdots+F_m,\qquad
 \mathbb R^d=W_1\oplus\cdots\oplus W_m,
 \qquad F_j\subset W_j,\quad \dim W_j\in\{1,2\}.
\]
The factors are centered symmetric and full-dimensional in their subspaces.
Let \(P_j\) be the projection onto \(W_j\) along the remaining summands,
and set \(a_{ji}=h_{F_j}(e_i)\ge0\). Then
\[
 P_j^2=P_j,\quad\operatorname{tr}P_j=\dim W_j,\quad\sum_jP_j=I,
 \qquad 1\le\sum_ja_{ji}\le1+s.                               \tag{6.1}
\]
Every cube vertex \(\sigma\in\{\pm1\}^d\) except the two all-equal ones
belongs to \(K_t\). Since \(P_j\sigma\in F_j\), the nonnegative quantities
\(a_{ji}-\sigma_i(P_j\sigma)_i\) sum to at most \(s\). Therefore
\[
 |(P_j\sigma)_i-a_{ji}\sigma_i|\le s.                          \tag{6.2}
\]
For any coordinate \(k\), assign both signs among the other coordinates;
this is possible since \(d\ge3\). Both vertices obtained by changing only
\(\sigma_k\) are retained. Subtract (6.2) for them to obtain
\[
 |(P_j-\operatorname{diag}(a_{j1},\ldots,a_{jd}))_{ik}|\le s.     \tag{6.3}
\]
This controls all entries even when the original decomposition is badly
conditioned.

Suppose \(s\le1/(4d)\), and write \(p_{ji}=(P_j)_{ii}\). Idempotence gives
\(|p_{ji}(p_{ji}-1)|\le(d-1)s^2\). Thus some \(z_{ji}\in\{0,1\}\) satisfies
\[
 |p_{ji}-z_{ji}|\le2(d-1)s^2.
\]
Inside \([0,1]\), this follows from \(q(1-q)\ge q/2\) for distance
\(q\le1/2\) to an endpoint; outside the interval it follows directly.
The integer trace and sum identities in (6.1), with errors less than one half,
give
\(\sum_i z_{ji}=\dim W_j\) and \(\sum_jz_{ji}=1\). Hence
\(J_j=\{i:z_{ji}=1\}\) partitions the indices into sets of size one or two.
For \(i\notin J_j\), (6.3) gives
\(a_{ji}\le s+2(d-1)s^2\).

Let \(u=(1,\ldots,1)\). Choose a retained vertex with plus signs on
\(J_j\) and a minus sign outside it. Equation (6.2) implies
\[
 h_{F_j}(u)\ge\sum_i a_{ji}-3ds-4d(d-1)s^2
            \ge\sum_i a_{ji}-4ds.
\]
Summing gives \(h_D(u)\ge d-4d^2s\), while containment in
\((1+s)K_t\) gives \(h_D(u)\le d-t+ds\). Therefore \(t\le5d^2s\).
If \(s>1/(4d)\), the same lower bound follows from \(t\le1\).
This proves the lower part of (1.4) for every product decomposition. The upper
part follows from
\((1-t/d)[-1,1]^d\subseteq K_t\subseteq[-1,1]^d\).

For the exact deficit, the two removed corner simplices each have volume
\(t^d/d!\), and every coordinate facet has area
\(\alpha=2^{d-1}-t^{d-1}/(d-1)!\). The two new area-normal vectors are
\(\pm t^{d-1}u/(d-1)!\), with area times support number
\(\beta=(d-t)t^{d-1}/(d-1)!\). Put
\[
 V_t=2^d-2t^d/d!,\quad D_t=d2^d-2t^d/(d-1)!,\quad
 p=\frac{2^d-2t^{d-1}/(d-1)!}{D_t},\quad
 r=\frac{2(d-t)t^{d-1}}{(d-1)!D_t}.
\]
The cone law has direction pairs \(\pm e_i\), each with total probability
\(p\), and \(\pm u/(d-t)\), with total probability \(r\). Within pairs
signs are uniform; \(dp+r=1\). Direct type enumeration gives
\[
 A=d!p^{d-1}\left(p+\frac{dr}{d-t}\right).
\]
Only \(N\)-tuples containing all \(d+1\) different direction types have a
nonzero Rademacher defect. Tuples with fewer than \(d\) types have zero
cofactors; those with exactly \(d\) types have a repeated parallel direction
and a two-term cofactor relation. For the all-distinct tuple, cofactor magnitudes
are 1 and \(d\) copies of \(q=1/(d-t)\). Averaging the sign multiplying 1
gives \(\mathbb E\max(1,|q\sum_{i=1}^d\epsilon_i|)\). For \(t\le1\),
only the two all-equal sign patterns exceed 1, so its value is
\(1+2^{1-d}(dq-1)\). The defect is \(c_dt/(d-t)\). The probability of
all-distinct types is \(N!p^dr\), giving
\[
 \delta_t=\frac{c_dprt}{(d-t)p+dr}.
\]
Substitute \(p,r\) to get (1.5). Also \(p\le1/d\), hence
\(\delta_t\le c_dt^d/(d!2^{d-1})\). Combining this with (1.4) excludes
every exponent greater than \(1/d\) as \(t\downarrow0\). In dimension three,
\[
 \delta_t=\frac{t^3(8-t^2)}{8(24-t^3)(4+t^2)}.
\]
This proves Theorem B. \(\square\)

## 7. Comparison with primary cone-volume and stability literature

The relevant antecedent is Böröczky–Lutwak–Yang–Zhang,
[The logarithmic Minkowski problem](https://www.renyi.hu/~carlos/minkowski0-prob.pdf),
JAMS 26 (2013), 831–852. Its subspace concentration condition and
complementary-subspace clause characterize existence of symmetric cone-volume
measures. They do not supply the near-short-circuit estimate (3.4), a quantitative
matching into dimensions at most two, or the present invariant's endpoint.

Böröczky–Henk,
[Cone-volume measure and stability](https://www.renyi.hu/~carlos/cone-volume-stability.pdf),
Adv. Math. 306 (2017), 24–50, Theorem 1.1 gives complementary-factor stability
with containment exponent \(1/(5d)\) from almost saturated cone mass on an
**exact** proper subspace; its constants and smallness threshold are stated as
dimension-dependent, rather than numerical formulas. Its U-functional stability
targets parallelotopes. Our equality class includes all symmetric planar
factors, and our hypothesis is determinant magnitude, not the U-functional's
independence indicator. Thus that theorem is not an equivalent endpoint result.

The exact-subspace premise cannot be inferred here: for even integers
\(p\to\infty\), smooth strictly convex \(\ell_p\) balls converge to the
cube and have \(a\to1/2\), yet their cone-volume measures give zero mass to
every proper linear subspace. On each open coordinate octant the Gauss map is a
diffeomorphism with positive curvature; the omitted coordinate-zero parts have
surface measure zero, proving absolute continuity. Our method instead produces
an expected distance to blocks and recovers an actual product by Lemma 5.1.

Böröczky–De,
[Stable solution of the logarithmic Minkowski problem in the case of hyperplane symmetries](https://arxiv.org/abs/2101.03395),
J. Differential Equations 298 (2021), 298–322, obtains quantitative inverse
cone-volume estimates under Coxeter symmetry and a tube concentration margin.
The reducible-group margin degenerates at concentration on a proper
group-invariant product block, and the
symmetry hypothesis does not cover arbitrary symmetric planar factors. Their
anisotropic-squeeze example also explains why normalization is necessary.
Abdallah–Mérigot,
[On the reconstruction of convex sets from random normal measurements](https://arxiv.org/abs/1402.5010),
gives a surface-area inverse estimate of order \(1/d\) with area and rotundity
control. Cone-volume data additionally contains the unknown support function;
Lemma 5.1 avoids solving that inverse problem.

Böröczky–De also compare a cube with a volume-normalized unconditional body
obtained by truncating its vertices: the cone-volume Wasserstein distance is
\(O_d(\varepsilon)\), whereas the containment loss is
\(\Omega_d(\varepsilon^{1/d})\). This is a related cap-volume obstruction.
Theorem B instead computes the upper-end scalar deficit
\(1/2-a(K_t)\) and proves a distance lower bound against every affine product
of symmetric one- and two-dimensional bodies. A comparison with one fixed cube
would not establish that lower bound.

Saroglou's
[Volumes of projection bodies of some classes of convex bodies](https://doi.org/10.1112/S0025579311001860)
is a primary projection-body comparison. Only its publication record and
abstract were available; a full-text comparison remains incomplete.
The recent Liu–Xiong–Yang mixed-volume
stability paper, DOI
[10.1016/j.aim.2026.110886](https://doi.org/10.1016/j.aim.2026.110886),
is relevant to broader mixed-volume stability questions. No theorem from
either of these two papers is imported as a dependency. The present literature
comparison is confined to the primary statements described above.

## 8. Dependencies, reproducibility, and open questions

The affine calculus and cone-law representation are inherited from entry 005
versions 2–3; the exact equality class is the version 4 theorem. The pinned
sources are listed below. The quantitative contact-slab, matching, and product
recovery arguments in Sections 3–5 are supplied in full here. In particular,
the lower-end simplex modulus and the balanced-recursion spectral theorem are
separate results and are not inputs to this proof.

The accompanying exact programs test 4,930 balanced rational coefficient
multisets, 750 omitted-basis cofactor identities, and 16 corner-truncation
facet-minor calculations. They use only integers and rational arithmetic, and
explicit exceptions keep the checks active under Python optimization. These
finite regressions supplement the written analytic proof. The package records
source hashes and separates regenerated outputs from shipped reference reports.

The constants are deliberately coarse. The optimal universal exponent remains
between $1/(6d)$ and $1/d$ for $d\ge3$. Sharpening the matching estimate and the
conversion of normal concentration to product containment may reduce the gap.

## References and provenance

- [005v2] mxym, *Projection-volume calculus for joins and Cartesian products*,
  entry 005, version 2. Definitions, affine invariance, and product calculus.
  [Pinned source](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v2/paper.md).
- [005v3] mxym, *Random-determinant rigidity, sharp symmetric cone bounds, and
  spectral nonattainment*, entry 005, version 3. Cone-law representation and
  symmetric inequality.
  [Pinned source](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v3/paper.md).
- [005v4] mxym, *Equality in the symmetric projection-cone bound*, entry 005,
  version 4. The equality class and its qualitative stability.
  [Pinned source](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v4/paper.md).
- [BLYZ] K.J. Böröczky, E. Lutwak, D. Yang, and G. Zhang, *The logarithmic
  Minkowski problem*, Journal of the American Mathematical Society 26 (2013),
  831–852. [DOI](https://doi.org/10.1090/S0894-0347-2012-00741-3).
- [BH] K.J. Böröczky and M. Henk, *Cone-volume measure and stability*, Advances
  in Mathematics 306 (2017), 24–50.
  [DOI](https://doi.org/10.1016/j.aim.2016.10.005).
- [BD] K.J. Böröczky and A. De, *Stable solution of the logarithmic Minkowski
  problem in the case of hyperplane symmetries*, Journal of Differential
  Equations 298 (2021), 298–322.
  [DOI](https://doi.org/10.1016/j.jde.2021.07.002).
  [Primary preprint, version 2](https://arxiv.org/html/2101.03395v2).
- [AM] H. Abdallah and Q. Mérigot, *On the reconstruction of convex sets from
  random normal measurements*. [Primary preprint](https://arxiv.org/abs/1402.5010).
- [S] C. Saroglou, *Volumes of projection bodies of some classes of convex
  bodies*, Mathematika 57 (2011), 329–353.
  [DOI](https://doi.org/10.1112/S0025579311001860).
- [LXY] Y.-D. Liu, G. Xiong, and K.-W. Yang, *Sharp quantitative stability for the
  Minkowski first inequality via a quadratic estimate for the cone-volume
  measure*, Advances in Mathematics 492 (2026), 110886.
  [DOI](https://doi.org/10.1016/j.aim.2026.110886).
- [Sch] R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, second
  expanded edition, Cambridge University Press, 2014. Support functions,
  surface area, John normalization, and mixed volumes.

Versions2–4 credit the projection-volume product and simplex computations
inherited from OpenAI family 088, pinned at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This supplement uses the inherited
identities through the explicitly cited entry 005 sources.
