# Direct quantitative recovery from off-block normals

Date: 7 October 2026. This is a separate research note. It does not alter the
completed upper-end stability supplement.

## 1. Statement

Let \(d\ge2\), and let \(Q\subset\mathbb R^d\) be an origin-symmetric
(\(Q=-Q\)), full-dimensional convex body such that

\[
rB_2^d\subset Q\subset RB_2^d,\qquad 0<r\le R.
\]

Let \(\mathbb R^d=\bigoplus_{j=1}^m W_j\) be an orthogonal decomposition
into nonzero subspaces, let \(\mathcal W=\bigcup_jW_j\), and put

\[
P=\prod_{j=1}^m\operatorname{proj}_{W_j}Q,
\qquad
I=\int_{\partial Q}\operatorname{dist}(n_Q(x),\mathcal W)
       \,d\mathcal H^{d-1}(x).
\]

Regular boundary points suffice in this integral; the omitted set has
surface measure zero. Thus

\[
I=\int_{S^{d-1}}\operatorname{dist}(u,\mathcal W)\,dS_Q(u).
\]

Write \(\kappa_k=|B_2^k|\), including \(\kappa_0=1\), and set

\[
 A_{d,r,R}=\frac{2}{\kappa_{d-2}}
       \left(\frac{2(\sqrt2R+r)}r\right)^{d-2}.
\]

**Theorem.** The product built from the actual block projections satisfies

\[
 d_H(Q,P)\le m(A_{d,r,R}I)^{1/(d-1)},                 \tag{1.1}
\]

\[
 d_{\rm BM}(Q,P)-1
 \le\frac mr(A_{d,r,R}I)^{1/(d-1)}.                 \tag{1.2}
\]

Equivalently, for the cone-law measurement

\[
s=\mathbb E_{\nu_Q}\operatorname{dist}(X,\mathcal W)
  =\frac I{d|Q|},
\]

one has the explicit estimate

\[
\boxed{d_{\rm BM}(Q,P)-1
\le \frac mr
\left(A_{d,r,R}\,d\kappa_d R^d\,s\right)^{1/(d-1)}.}  \tag{1.3}
\]

No atomicity, polyhedrality, smoothness, or uniqueness of a product
decomposition is required. The dimensions of the blocks do not enter the
proof. If every block has dimension one or two, \(P\) is in the equality
class of the completed theorem, so its distance to the entire class has
the same upper bound. For \(m=1\), \(P=Q\), and all claims are immediate.

## 2. A planar mixed-normal lemma

**Lemma.** Let \(C\subset\mathbb R^2\) be a full-dimensional compact
convex set. Suppose \(C\) contains points \((-b_0,0)\) and \((0,-a_0)\),
where \(a_0,b_0>0\), while \(\operatorname{dist}(0,C)\ge t>0\). Then

\[
\int_{\partial C}\min(|n_1|,|n_2|)\,d\mathcal H^1\ge t. \tag{2.1}
\]

**Proof.** Intersect with the closed negative quadrant. Choose the closest
intersection points to the origin on its coordinate axes and write them
as \((-b,0)\) and \((0,-a)\), with \(a,b>0\). They exist because the
original two points are in \(C\), and positivity follows from the
distance assumption. For \(-b\le x\le0\), let

\[
 f(x)=\max\{y:(x,y)\in C\cap(-\infty,0]^2\}.
\]

The segment connecting the two chosen points proves that this function
is defined on the entire interval. Convexity shows that \(f\) is concave;
it is continuous, \(f(-b)=0\), and \(f(0)=-a\). The choice of \(b\)
gives \(f(x)<0\) for \(-b<x\le0\). Concavity and \(f\le0\) imply
that \(f\) is nonincreasing. Its open graph belongs to the boundary of
the original \(C\), because both quadrant constraints are inactive there.

Put \(g=-f\). This is a nonnegative, nondecreasing convex function,
with \(g(-b)=0\) and \(g(0)=a\). It is absolutely continuous and its
almost-everywhere derivative is nonnegative and nondecreasing. At
regular graph points the unit outward normal is
\((g'(x),1)/\sqrt{1+g'(x)^2}\), so the graph contribution is

\[
\int_{-b}^0\min(1,g'(x))\,dx.
\]

Since \(g'\) is nondecreasing, let \(x_*\in[-b,0]\) be a crossing point
of the level one, with the natural endpoint choices if \(g'\ge1\)
everywhere or \(g'\le1\) everywhere. Integration before and after the
crossing gives

\[
\int_{-b}^0\min(1,g')\,dx=g(x_*)-x_*
                      =\min_{[-b,0]}(g(x)-x).
\]

Each graph point \((x,-g(x))\in C\) is at Euclidean distance at least

\(t\) from the origin. Its distance in the \(\ell_1\) norm is
\(g(x)-x\), hence the displayed minimum is at least \(t\). All other
boundary contributions are nonnegative. This proves (2.1). Endpoint
vertical segments, if present, have zero mixed-normal contribution and
do not change the argument. \(\square\)

## 3. Two-factor recovery by thickening a planar section

Fix an orthogonal bipartition \(\mathbb R^d=E\oplus F\) into nonzero
subspaces and put

\[
 P_{E,F}=\operatorname{proj}_E Q\times\operatorname{proj}_F Q,
\qquad
 I_{E,F}=\int_{\partial Q}
        \min(|\operatorname{proj}_E n|,|\operatorname{proj}_F n|)
        \,d\mathcal H^{d-1}.
\]

We claim

\[
 d_H(Q,P_{E,F})^{d-1}\le A_{d,r,R}I_{E,F}.            \tag{3.1}
\]

Since \(Q\subset P_{E,F}\), choose a point \(p\in P_{E,F}\) where
\(t=\operatorname{dist}(p,Q)=d_H(Q,P_{E,F})\) is attained. If \(t=0\)
the claim is immediate. Choose \(q_A,q_B\in Q\) with

\[
 \operatorname{proj}_E q_A=\operatorname{proj}_E p,
\qquad
 \operatorname{proj}_F q_B=\operatorname{proj}_F p.
\]

Then \(a=p-q_A\in F\) and \(b=p-q_B\in E\) are nonzero and
orthogonal. Define the two-dimensional plane

\[
 L=\operatorname{span}\{b,a\},\quad
 e_1=b/|b|\in E,\quad e_2=a/|a|\in F,\quad T=L^\perp.
\]

Because each component of \(p\) is a projection of a point of \(Q\),
\(|p|\le\sqrt2R\). Also \(t\le |p|\le\sqrt2R\), because \(0\in Q\). Set

\[
 \eta=\frac{t}{2(\sqrt2R+r)}\in(0,1).
\]

For every \(z\in T\) with \(|z|<\eta r\), the points

\[
 q_{A,z}=(1-\eta)q_A+z,\qquad
 q_{B,z}=(1-\eta)q_B+z
\]

belong to the interior of \(Q\): each is the convex combination of a
point of \(Q\) and the interior-ball point \(z/\eta\). They share an
affine plane parallel to \(L\) with

\[
 p_z=(1-\eta)p+z.
\]

Relative to \(p_z\), the endpoints have coordinates
\((0,-(1-\eta)|a|)\) and \((-(1-\eta)|b|,0)\). Furthermore

\[
 \operatorname{dist}(p_z,Q)
 \ge t-|p-p_z|
 \ge t-\eta\sqrt2R-|z|
 \ge t/2.                                           \tag{3.2}
\]

The planar section \(C_z=Q\cap(p_z+L)\) is full-dimensional in its
plane and contains both endpoints. Applying the planar lemma gives

\[
 \int_{\partial C_z}
       \min(|n_{C_z}\cdot e_1|,|n_{C_z}\cdot e_2|)
       \,d\mathcal H^1\ge t/2.                     \tag{3.3}
\]

The linear projection \(\pi_T:\partial Q\to T\) has tangential
\((d-2)\)-Jacobian \(|\operatorname{proj}_L n|\). For almost every
transverse parameter, its slice has outward normal

\[
 n_{C_z}=\frac{\operatorname{proj}_L n}
                 {|\operatorname{proj}_L n|}
\]

at almost every regular intersection point. The coarea formula therefore
gives, with zero integrand when \(\operatorname{proj}_L n=0\),

\[
\begin{aligned}
I_{E,F}
&\ge\int_{\partial Q}\min(|n\cdot e_1|,|n\cdot e_2|)
                       \,d\mathcal H^{d-1}\\
&\ge\int_{\{|z|<\eta r\}\subset T}
   \int_{\partial C_z}
       \min(|n_{C_z}\cdot e_1|,|n_{C_z}\cdot e_2|)
       \,d\mathcal H^1\,dz\\
&\ge\kappa_{d-2}(\eta r)^{d-2}\,t/2\\
&=\frac{\kappa_{d-2}}2
       \left(\frac{r}{2(\sqrt2R+r)}\right)^{d-2}t^{d-1}.
\end{aligned}
\]

This is (3.1). For \(d=2\), the transverse space has dimension zero,
and the same formula is interpreted with \(\kappa_0=1\).

The coarea argument applies to arbitrary convex bodies: their boundaries
are countably rectifiable and regular almost everywhere. The singular
boundary has zero \((d-1)\)-measure and therefore zero weighted coarea
contribution. For almost every transverse parameter, the intersection of
the regular boundary is the section boundary up to length-zero sets. The
ball thickening ensures that all sections used here have nonempty relative
interior. Flat facets and nonatomic surface-area laws are both allowed.

## 4. Recovering all factors

For each \(j\), apply (3.1) to
\(E=W_j\), \(F=W_j^\perp\), and write the resulting two-factor
product as \(P_j\). For any unit vector \(n\),

\[
 \min(|\operatorname{proj}_{W_j}n|,
       |\operatorname{proj}_{W_j^\perp}n|)
 \le \operatorname{dist}(n,\mathcal W).
\]

Indeed, if the largest block component is the \(j\)-th one, the
right-hand side is exactly the complementary norm; if another block
component is largest, the right-hand side is at least the \(j\)-th
component norm. Consequently

\[
 e_j:=d_H(Q,P_j)\le(A_{d,r,R}I)^{1/(d-1)}.            \tag{4.1}
\]

Fix any \(p\in P\), start with \(q_0\in Q\), and successively replace
the \(j\)-th block coordinate of \(q_{j-1}\) by that of \(p\). Call the
new point \(z_j\). It belongs to \(P_j\), because its \(j\)-th component
is feasible in the projection of \(Q\), while the complementary component
is the projection of \(q_{j-1}\in Q\). Choose \(q_j\in Q\) such that

\[
 q_j=z_j+\varepsilon_j,\qquad |\varepsilon_j|\le e_j.
\]

Writing \(\pi_j=\operatorname{proj}_{W_j}\), the recurrence is

\[
 q_j=\pi_jp+(I-\pi_j)q_{j-1}+\varepsilon_j.
\]

The mutually orthogonal coordinate projections commute. After all blocks
have been replaced, the original \(q_0\) contributes zero and

\[
 q_m-p=\sum_{j=1}^m
       \left(\prod_{k=j+1}^m(I-\pi_k)\right)\varepsilon_j.
\]

Every displayed product is an orthogonal projection, so
\(|q_m-p|\le\sum_j e_j\). Taking the maximum over \(p\in P\) proves
(1.1).

Finally, if \(e=d_H(Q,P)\), support functions satisfy

\[
 h_P(u)\le h_Q(u)+e\le(1+e/r)h_Q(u)
\]

for unit \(u\), because \(h_Q(u)\ge r\). Hence

\[
 (1+e/r)^{-1}P\subset Q\subset P.
\]

This proves (1.2), and \(|Q|\le\kappa_dR^d\) gives (1.3).

## 5. Consequences and limits

The weighted corner cuts in `geometry-next.md`, and their all-product
distance obstruction imported from the audited supplement, show that the
exponent \(1/(d-1)\) in (1.3) cannot be improved in general when the
blocks have dimension one or two. Their radii can be kept uniformly
bounded above and below. Thus this direct recovery theorem closes the
geometry-only exponent gap; it does not identify the sharp exponent of
the original upper-end deficit.

The selected basis in the completed rank lemma already gives an explicit
inradius sufficient to apply this theorem. If its columns have Euclidean
norm at most one and determinant \(D\ge a_d/2\), every row of its inverse
has norm at most \(1/D\) by the cofactor-wedge bound. Therefore

\[
 \|U^{-1}\|\le\sqrt d/D,\qquad
 U^TK\supset \frac{a_d}{2\sqrt d}B_2^d
\]

when \(K\) is in symmetric John position. The same transformed body
satisfies \(U^TK\subset dB_2^d\). Thus the existing estimate
\(s\le L_d\delta^{1/6}\) yields an improved geometric exponent
\(\delta^{1/[6(d-1)]}\), with constants obtained directly from (1.3).
The direct geometric estimate and its use in the stronger matching
assembly passed an independent analytic model audit. It does not change
the completed release and does not rely on the extra-factor estimate
refuted in `geometry-next.md`.

## 6. Stronger homothetic recovery without an inradius constant

The interior-ball thickening can be replaced by a thickening with \(Q\)
itself. This removes the inradius from the small-error bound.

Keep \(Q=-Q\), \(Q\subset RB_2^d\), and the orthogonal block
decomposition from above. Define

\[
T=\left(2^{2d-1}\,dR\,s\right)^{1/(d-1)},\qquad
\lambda=\max\{\alpha\ge0:\alpha P\subset Q\}.
\]

**Theorem.** For arbitrary nonzero block dimensions,

\[
\boxed{1-\lambda\le mT.}                              \tag{6.1}
\]

If \(mT\le1/2\), then

\[
d_{\rm BM}(Q,P)-1\le2mT.                              \tag{6.2}
\]

When all block dimensions are one or two, the global whole-class estimate
is

\[
\boxed{D(Q,\mathcal E_d)-1
       \le2md\left(2^{2d-1}dR\,s\right)^{1/(d-1)}.}    \tag{6.3}
\]

The global estimate uses the symmetric John bound only for the regime
\(mT>1/2\). It is an estimate to the entire affine product class; in that
regime it does not claim control of distance to the one fixed product \(P\).

### 6.1. Bipartition lemma

For an orthogonal bipartition \(E\oplus F\), put \(P_{E,F}\) and
\(I_{E,F}\) as in Section 3, and set

\[
\lambda_{E,F}=\max\{\alpha:\alpha P_{E,F}\subset Q\},
\qquad \tau=1-\lambda_{E,F}.
\]

We prove

\[
\boxed{\tau^{d-1}\le
       2^{2d-1}R\,\frac{I_{E,F}}{|Q|}.}                \tag{6.4}
\]

Both bodies contain the origin in their interiors, and \(Q\subset
P_{E,F}\), so \(\lambda_{E,F}\in(0,1]\). The claim is immediate when
\(\tau=0\). Otherwise compactness of the support-function ratio gives a
unit vector \(u\) such that

\[
h_Q(u)=\lambda_{E,F}h_{P_{E,F}}(u).
\]

Write \(H=h_{P_{E,F}}(u)>0\), and choose \(p\in P_{E,F}\) with
\(u\cdot p=H\). Choose \(q_A,q_B\in Q\) sharing respectively the \(E\)
and \(F\) components of \(p\). As before,

\[
a=p-q_A\in F,\quad b=p-q_B\in E,\quad
L=\operatorname{span}\{b,a\},\quad T_0=L^\perp.
\]

The two vectors \(a,b\) are nonzero: the support gap at \(p\) is
\(\tau H>0\). Furthermore \(u_L=\operatorname{proj}_L u\ne0\), because

\[
u\cdot a=H-u\cdot q_A\ge\tau H>0.
\]

Set \(\eta=\tau/4\in(0,1/4)\). For any
\(z\in\operatorname{int}_{T_0}(\operatorname{proj}_{T_0}Q)\), choose an
interior lift \(q\in\operatorname{int}Q\) with
\(\operatorname{proj}_{T_0}q=z\). Such a lift exists because a surjective
linear map sends the interior of a convex body onto the interior of its
image. Consider

\[
p_q=(1-\eta)p+\eta q,\quad
q_{A,q}=(1-\eta)q_A+\eta q,\quad
q_{B,q}=(1-\eta)q_B+\eta q.
\]

The endpoints belong to the interior of \(Q\), share a plane parallel to
\(L\) with \(p_q\), and relative to \(p_q\) have the same negative-axis
form as in Section 3. Central symmetry gives \(u\cdot q\ge-h_Q(u)\).
Consequently

\[
\begin{aligned}
u\cdot p_q-h_Q(u)
 &=\tau H-\eta(H-u\cdot q)\\
 &\ge\tau H-\eta(H+h_Q(u))\\
 &\ge\tau H-2\eta H=\tau H/2.
\end{aligned}
\]

On this fixed affine plane, only the component \(u_L\) of the normal
varies. Thus the distance of \(p_q\) to the planar section is at least

\[
\frac{\tau H}{2|u_L|}.
\]

Apply the planar lemma and then the same weighted coarea identity as in
Section 3. The transverse parameters now fill

\[
(1-\eta)\operatorname{proj}_{T_0}p+
       \eta\operatorname{proj}_{T_0}Q,
\]

whose \((d-2)\)-volume is
\(\eta^{d-2}|\operatorname{proj}_{T_0}Q|\). The boundary of this
projection has measure zero. Every interior parameter has an interior
lift, so its section is full-dimensional; no measurable selection of the
lift is needed, since the lower bound holds for each such section.
It follows that

\[
I_{E,F}\ge
\eta^{d-2}|\operatorname{proj}_{T_0}Q|\,
       \frac{\tau H}{2|u_L|}.                        \tag{6.5}
\]

For any fixed transverse parameter \(w\), its fiber in \(Q\) is contained
in a planar rectangle with side lengths at most

\[
\frac{2h_Q(u)}{|u_L|}\le\frac{2H}{|u_L|}
\quad\hbox{and}\quad 2R.
\]

The first follows from
\(-h_Q(u)\le u_L\cdot x_L+u_{T_0}\cdot w\le h_Q(u)\);
the second follows from \(Q\subset RB_2^d\) in the perpendicular direction
inside \(L\). Fubini therefore yields

\[
|Q|\le\frac{4RH}{|u_L|}\,
          |\operatorname{proj}_{T_0}Q|.              \tag{6.6}
\]

Substitute (6.6) into (6.5), and use \(\eta=\tau/4\):

\[
\frac{I_{E,F}}{|Q|}
\ge\frac{\tau^{d-1}}{8\,4^{d-2}R}
 =\frac{\tau^{d-1}}{2^{2d-1}R}.
\]

This proves (6.4), also in dimension two with the zero-dimensional
transverse volume convention.

### 6.2. Combining the homothetic inclusions

For each single-block bipartition
\(P_j=\operatorname{proj}_{W_j}Q\times
\operatorname{proj}_{W_j^\perp}Q\), let
\(\lambda_j=\max\{\alpha:\alpha P_j\subset Q\}\). The pointwise normal
inequality from Section 4 and \(I=d|Q|s\) give

\[
1-\lambda_j\le T.                                   \tag{6.7}
\]

We claim

\[
\left(\prod_{j=1}^m\lambda_j\right)P\subset Q.         \tag{6.8}
\]

Fix \(p\in P\), write \(p_j=\operatorname{proj}_{W_j}p\), and prescribe
the adjusted coordinates

\[
\widetilde p_j=\left(\prod_{k<j}\lambda_k\right)p_j.
\]

Each adjusted coordinate lies in its factor projection, since that factor
is convex and contains zero. Start with \(q_0=0\in Q\). For \(j=1,\ldots,m\),
replace the \(j\)-th block of \(q_{j-1}\) by \(\widetilde p_j\) to obtain
\(z_j\in P_j\), and then set \(q_j=\lambda_j z_j\in Q\).
The \(j\)-th block of \(q_m\) is

\[
\left(\prod_{k=j}^m\lambda_k\right)\widetilde p_j
=\left(\prod_{k=1}^m\lambda_k\right)p_j.
\]

Therefore \(q_m=(\prod_j\lambda_j)p\in Q\), proving (6.8).
Since the \(\lambda_j\) lie in \((0,1]\),

\[
1-\prod_j\lambda_j\le\sum_j(1-\lambda_j)\le mT.
\]

This proves (6.1). In the small-error regime it gives

\[
(1-mT)P\subset Q\subset P,\qquad
d_{\rm BM}(Q,P)-1
 \le\frac{mT}{1-mT}\le2mT,
\]

which is (6.2). For the whole-class estimate, the same bound applies when
\(mT\le1/2\), and otherwise symmetric John's theorem gives
\(D(Q,\mathcal E_d)-1\le d-1\le2mdT\). This proves (6.3).

### 6.3. Original endpoint implication

The completed proof's final coordinate body satisfies \(Q\subset dB_2^d\).
Thus (6.2) or (6.3) can be used without paying for the small determinant of
the selected basis. In particular, the existing
\(s\le L_d\delta^{1/6}\) improves the deficit exponent from \(1/(6d)\)
to \(1/[6(d-1)]\). Any independent improvement in the matching-stage power
can be combined with this proof, after checking its precise inputs.

The \(1/(d-1)\) power in (6.3) is sharp in fixed dimension by the corner
cut bodies and the all-product distance lower bound in geometry-next.md.
The new proof does not infer a sharp original-deficit exponent from that
intermediate sharpness.

The direct recovery proof uses thickening by the body itself and a shared support direction to cancel the conditioning loss. Its small-error estimate needs no inradius constant and has geometric power \(1/(d-1)\). The optimal original-deficit exponent remains unresolved.
