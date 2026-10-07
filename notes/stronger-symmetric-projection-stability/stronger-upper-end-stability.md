# A stronger upper-end exponent from weighted rank-two matching

7 October 2026. This note proves a strengthening of the completed symmetric
projection-cone stability theorem. The completed supplement is unchanged.
The new steps are a sharp square-root matching estimate and a direct recovery
theorem from off-block normals. No heuristic tuning of thresholds is used.

## 1. Statement

Let \(K\subset\mathbb R^d\) be a centrally symmetric full-dimensional convex
body, centered at zero, and let \(a(K)\) be the entry005 affine projection-cone
invariant. Set \(\delta=1/2-a(K)\). Let \(\mathcal E_d\) be the entire class
of linear images of Cartesian products of centrally symmetric convex factors
of dimensions one and two. Use
\[
d_{\rm BM}(K,E)=\inf\{\lambda\ge1:TE\subseteq K\subseteq\lambda TE,
\ T\in\mathrm{GL}(d)\},\qquad
D(K,\mathcal E_d)=\inf_{E\in\mathcal E_d}d_{\rm BM}(K,E).
\]

**Theorem 1 (weighted matching).** For every \(d\ge3\) and every such \(K\),
\[
\boxed{D(K,\mathcal E_d)-1
\le d^{12}\bigl(\tfrac12-a(K)\bigr)^{1/(3d)}.}                 \tag{1}
\]
There is no smoothness, curvature, polytope, atom, or absolute-continuity
hypothesis. In dimensions one and two the distance is one.

For the explicit unsimplified constants put
\[
\begin{aligned}
N&=d+1,&\kappa_d&=\pi^{d/2}/\Gamma(1+d/2),&a_d&=d^{-2d},\\
Z_d&=2^{d+9}N\sqrt d\binom d3/\kappa_d,
&F_d&=13N+3Z_d,&B_d&=4NF_d/a_d,\\
\widehat L_d&=5d^2a_d^{-2}B_d^{1/2},
&\widehat H_d&=d(\sqrt d+1)\widehat L_d,
&\widehat C_d&=2d(2d\widehat H_d)^{1/d}.
\end{aligned}
\]
The proof gives the stronger constant \(\widehat C_d\le d^{12}\), and
\[
D(K,\mathcal E_d)-1\le\widehat C_d\delta^{1/(3d)}.            \tag{2}
\]
If
\[
0<\delta\le\widehat\delta_d^*:=
 \left(\frac{2^{-d}}{2d\widehat H_d}\right)^3,
\]
there is also the explicit containment estimate
\[
D(K,\mathcal E_d)
\le\frac1{1-(2d\widehat H_d\delta^{1/3})^{1/d}}.              \tag{3}
\]
The constants are conservative and depend on dimension. The earlier all-class
corner-truncation obstruction still excludes exponents above \(1/d\).
The next theorem further improves the geometric exponent.

**Theorem 2 (weighted matching and direct geometric recovery).** Under exactly
the same hypotheses,
\[
\boxed{D(K,\mathcal E_d)-1
\le d^{19}\bigl(\tfrac12-a(K)\bigr)^{1/[3(d-1)]}.}             \tag{8}
\]
Both estimates hold globally, so their minimum is also a valid modulus.
The remaining optimal-exponent interval is \([1/[3(d-1)],1/d]\).
The factor \(d^{19}\) is deliberately coarse.

## 2. The inputs retained from the completed proof

The normalized cone law is
\[
\nu_K=(u\mapsto u/h_K(u))_*
       \left[\frac{h_K(u)}{d|K|}\,dS_K(u)\right].
\]
For independent samples \(X_i\) define
\[
A=\mathbb E|\det(X_1,\ldots,X_d)|,\quad
B=\mathbb E\left|\det\begin{pmatrix}
X_1&\cdots&X_{d+1}\\1&\cdots&1
\end{pmatrix}\right|.
\]
Entry005 v3 proves \(a(K)=B/((d+1)A)\) for general convex bodies. For a
\((d+1)\)-tuple, write \(\phi\) for its fourth-largest absolute horizontal
cofactor. The completed proof supplies the following three established inputs.

1. In symmetric John position \(B_2^d\subseteq K\subseteq\sqrt d B_2^d\),
   the law is supported in the unit ball and
   \(A\ge d^{-3d/2}\ge a_d\). This follows from the regular-contact identity
   \(\mathbb E[Y X^{\mathsf T}]=I/d\) and sequential wedge expectations.
2. The cone-specific contact-slab argument gives
   \(\mathbb E\phi\le F_d\delta^{2/3}\). Its conditional determinant
   denominator cancels before integration. The estimate includes singular
   tuples, nonatomic laws, flat-face atoms, and the zero-deficit case.
3. If \(Q\) is centered symmetric and full-dimensional, \(Q\subseteq RB_2^d\),
   and \(\mathcal W\) is the union of an orthogonal block decomposition,
   then its product of block projections \(P\) satisfies
   \[
   (1-(2dv)^{1/d})P\subseteq Q\subseteq P,
   \quad v=R(\sqrt m+1)\mathbb E_{\nu_Q}\operatorname{dist}(X,\mathcal W),
   \quad 2dv<1.                                             \tag{4}
   \]
   Here \(m\) is the number of blocks. The proof bounds
   \(V(Q[d-1],P)/|Q|-1\) by \(v\), uses Minkowski's first inequality,
   and inserts a homothetic image of a symmetric half of \(P\) into its missing
   cap. It assumes no inradius bound or inverse cone-volume uniqueness theorem.

These inputs are Sections 2, 3 and 5 of the completed English proof. For
Theorem 1 the replaced argument is its Section 4 matching estimate; Theorem 2
also replaces the final geometric recovery step. The full new
matching proof is in the accompanying [matching.md](matching.md), and its
essential quantitative mechanism is recorded next.

## 3. Why weighted matching improves the power

For a bounded Borel law with \(A\ge a>0\), \(\mathbb E\phi\le\varepsilon\),
put \(q=4(d+1)\varepsilon/a\). The simultaneous Fubini-section selection
in [matching.md](matching.md) gives a sampled basis \(U\), with
\(D=|\det U|\ge a/2\), whose one-sample and every omitted-basis two-sample
section each have fourth-cofactor expectation at most \(q\). In particular
\[
\|U\|\le\sqrt d,\quad \|U^{-1}\|\le2\sqrt d/a,
\quad |\alpha_i|\le1/D,\quad
\mathbb Es_3(\alpha)\le q/D^2,\qquad\alpha=U^{-1}X,
\]
where \(s_3\) is the third-largest coordinate magnitude.

Retain the two largest coordinates of each vector, with fixed-index tie
breaking. In an omitted-basis section the cofactors, up to signs, are
\[
D\alpha_j,\quad D\beta_j,\quad
D(\alpha_i\beta_j-\alpha_j\beta_i)\quad(i\ne j).
\]
Truncating both vectors changes each entry by at most
\(2s_3(\alpha)+2s_3(\beta)\). Absolute value and a fixed order statistic are
1-Lipschitz in the maximum norm, so the truncated section expectation is at
most \(q+4q/D^2\).

Give a coordinate pair \(ij\) the weighted mass
\[
m_{ij}=\mathbb E\left[
\min(|\alpha_i|,|\alpha_j|)
\mathbf1_{\{ij\text{ is the chosen top pair}\}}\right].
\]
For adjacent pairs \(ij,jk\), their two truncated vectors make four cofactors
at least \(D^2r_\alpha r_\beta\), where \(r\) denotes the smaller retained
magnitude. Thus
\[
m_{ij}m_{jk}\le\frac{q+4q/D^2}{D^2}\le\frac{5q}{D^4}.       \tag{5}
\]
Pairs with mass exceeding \(\sqrt{q+4q/D^2}/D\) form a matching. Use them
as plane blocks and the remaining indices as line blocks. A discarded pair
contributes its smaller coordinate to distance from the chosen block union,
rather than its entire probability mass. Consequently, for \(0\le q\le1\),
\[
\begin{aligned}
\mathbb E\operatorname{dist}(\alpha,\mathcal W)
&\le\frac{\sqrt d\,q}{D^2}
 +\binom d2\frac{\sqrt{q+4q/D^2}}D\\
&\le\frac{\sqrt d+\sqrt5\binom d2}{D^2}\sqrt q
\le5d^2a^{-2}\sqrt q.                                     \tag{6}
\end{aligned}
\]
The last inequality follows from
\(4(\sqrt d+\sqrt5\binom d2)\le4d+5d(d-1)\le5d^2\).
For \(q=0\), all positive-weight edges form a matching and the third
coordinate vanishes almost surely. This proves the zero case without a limit.
All selections are finite Borel partitions, so no point needs positive mass.

## 4. Complete assembly of the stronger theorem

Put \(K\) in symmetric John position, and apply (6) with
\(a=a_d\), \(\varepsilon=F_d\delta^{2/3}\). Then
\[
q=B_d\delta^{2/3},\qquad
\mathbb E\operatorname{dist}(U^{-1}X,\mathcal W)
\le\widehat L_d\delta^{1/3}.                               \tag{7}
\]
For \(\delta\le\widehat\delta_d^*\), the condition \(q\le1\) is valid:
\(\widehat H_d\ge B_d^{1/2}\), and therefore
\[
q\le B_d\left(\frac{2^{-d}}{2d\widehat H_d}\right)^2\le1.
\]

Apply the primal map \(U^{\mathsf T}\). The body
\(Q=U^{\mathsf T}K\) is contained in \(dB_2^d\); its cone law is exactly
\((U^{-1})_*\nu_K\). Its coordinate line and plane blocks are orthogonal.
Thus (4), with \(R=d\), \(m\le d\), and (7), gives (3). Every projection
factor is centrally symmetric and full-dimensional in its block, so
\(P\in\mathcal E_d\). No decomposition has to be canonical or unique.

At the smallness threshold,
\[
r:=(2d\widehat H_d\delta^{1/3})^{1/d}\le1/2.
\]
The sandwich \((1-r)P\subseteq Q\subseteq P\) gives
\[
D(K,\mathcal E_d)-1\le\frac r{1-r}
\le2(2d\widehat H_d)^{1/d}\delta^{1/(3d)}.
\]
For every larger deficit use the John sandwich with a cube, which gives
\(D(K,\mathcal E_d)\le d\). The global coefficient in (2) covers this range
because
\[
\widehat C_d(\widehat\delta_d^*)^{1/(3d)}=d.
\]
At \(\delta=0\), (6) gives exact block support and (4) gives the product
itself. For \(d=1,2\), \(K\) is already an allowed factor. This proves (2)
and (3) in all cases.

To prove the stated numerical constant, the inscribed cube bound
\(\kappa_d\ge(2/\sqrt d)^d\) yields
\[
Z_d\le2^{10}d^{d/2+9/2},\quad
F_d\le2^{12}d^{d/2+9/2},\quad
B_d\le2^{15}d^{(5/2)d+11/2}.
\]
Consequently
\[
\widehat L_d\le5\,2^{15/2}d^{(21/4)d+19/4},\qquad
\widehat H_d\le10\,2^{15/2}d^{(21/4)d+25/4},
\]
and
\[
\widehat C_d^d
\le20\,2^{d+15/2}d^{(25/4)d+29/4}.
\]
For \(d\ge3\), \(20\,2^{15/2}<4096\le d^8\), while
\(2^d\le3^{d-1}\le d^{d-1}\): the first inequality starts at \(8\le9\)
and its ratio decreases by \(2/3\) with each increment of \(d\). Hence
\[
\widehat C_d^d\le d^{(29/4)d+57/4}\le d^{12d},
\]
where the last inequality is exactly \(19d\ge57\). This proves (1).
\(\square\)

### 4.1. The direct geometric recovery theorem

The full proof in [geometry-rigidity.md](geometry-rigidity.md) gives the
following stronger geometric input. For a centered symmetric full-dimensional
body \(Q\subset RB_2^d\), an orthogonal decomposition into \(m\) nonzero
blocks, its projection product \(P\), and
\(s=\mathbb E_{\nu_Q}\operatorname{dist}(X,\mathcal W)\), put
\[
T=(2^{2d-1}dR s)^{1/(d-1)}.
\]
Then
\[
(1-mT)P\subset Q\subset P                                  \tag{9}
\]
whenever \(mT<1\). In particular the Banach–Mazur excess to this product
is at most \(2mT\) when \(mT\le1/2\). If the factors have dimensions
one or two, the globally valid whole-class excess is at most \(2mdT\).
No inradius or inverse-basis norm occurs in these estimates.

For clarity, the mechanism and constants can be summarized independently.
For an orthogonal bipartition \(E\oplus F\), write \(P_{E,F}\) for the
two-factor projection product, \(\lambda P_{E,F}\subset Q\) for its maximal
centered homothetic inclusion, and \(\tau=1-\lambda\). A support witness
\(u,p\) has \(u\cdot p=H=h_{P_{E,F}}(u)\) and \(h_Q(u)=(1-\tau)H\).
Lift the two block components of \(p\) to \(q_A,q_B\in Q\). Their differences
from \(p\) span a two-dimensional plane \(L\) with orthogonal axes in
\(E,F\). Its normal component \(u_L\) is nonzero.

Contract \(p,q_A,q_B\) by \(1-\eta\) toward any interior point of \(Q\),
with \(\eta=\tau/4\). The contracted witness remains outside \(Q\) by
support height at least \(\tau H/2\). In every resulting planar section,
the mixed-normal boundary length is therefore at least
\(\tau H/(2|u_L|)\). The planar assertion is proved by writing its negative
quadrant frontier as \(y=-g(x)\): convexity makes \(g'\) nondecreasing, and
\(\int\min(1,g')=\min(g(x)-x)\) is at least the distance to the witness.

The transverse parameters fill a scaled copy of \(\operatorname{proj}_{L^\perp}Q\)
of measure \(\eta^{d-2}|\operatorname{proj}_{L^\perp}Q|\). The coarea
Jacobian on the regular boundary is \(|\operatorname{proj}_L n|\), so
\[
I_{E,F}:=\int_{\partial Q}
\min(|\operatorname{proj}_E n|,|\operatorname{proj}_F n|)\,d\mathcal H^{d-1}
\ge\eta^{d-2}|\operatorname{proj}_{L^\perp}Q|
      \frac{\tau H}{2|u_L|}.
\]
Every planar fiber has area at most \(4RH/|u_L|\), by the same support slab
and the outer-radius bound. Fubini cancels the transverse projection and
support denominator, giving
\[
\tau^{d-1}\le2^{2d-1}R I_{E,F}/|Q|.
\]
For a single-block bipartition, its normal integrand is at most
\(\operatorname{dist}(n,\mathcal W)\). Homogeneity of distance cancels the
cone weight, so the latter integral is exactly \(d|Q|s\), and every
single-block homothetic loss is at most \(T\).

The single-block inclusions multiply: successively replace coordinates by
their desired projection-product values, scaled by the preceding inclusion
factors. The resulting point is in \(Q\) and has all coordinates scaled by
\(\prod_j\lambda_j\). Thus \((\prod_j\lambda_j)P\subset Q\), with
\(\prod_j\lambda_j\ge1-\sum_j(1-\lambda_j)\ge1-mT\), proving (9).
The full note supplies the planar lemma and coarea regularity details for
arbitrary convex boundaries, including flat facets and nonatomic laws.

### 4.2. Complete assembly and numerical constant for Theorem 2

Retain \(M_d=\widehat L_d=5d^2a_d^{-2}\sqrt{B_d}\), and define
\[
G_d=(2^{2d-1}d^2M_d)^{1/(d-1)},\qquad C'_d=2d^2G_d,
\qquad\beta_d=\frac1{3(d-1)}.
\]
The coordinate body from (7) has \(R=d\), \(m\le d\), and
\(s\le M_d\delta^{1/3}\). Therefore \(T\le G_d\delta^{\beta_d}\).
For
\[
0<\delta\le\delta'_d:=(1/(2dG_d))^{3(d-1)},
\]
we have \(mT\le1/2\). The matching condition \(q\le1\) also holds:
\(M_d\ge\sqrt{B_d}\), hence \(G_d^{d-1}\ge\sqrt{B_d}\), and
\[
q\le B_d/(2dG_d)^{2(d-1)}\le1.
\]
The small-deficit excess is consequently at most
\(2dG_d\delta^{\beta_d}\). At all larger deficits use the John bound
\(D-1\le d-1\); it is covered by the global coefficient since
\(C'_d(\delta'_d)^{\beta_d}=d\). At zero deficit, the exact matching
case and (9) give the product itself. This proves
\(D-1\le C'_d\delta^{\beta_d}\) in every case.

To bound \(C'_d\), the earlier estimate on \(B_d\) gives
\[
M_d\le5\,2^{15/2}d^{(21/4)d+19/4},
\qquad
(C'_d)^{d-1}\le5\,2^{3d+11/2}d^{(29/4)d+19/4}.
\]
For \(d\ge3\), \(8\le d^2\), and
\(5\,2^{11/2}<243\le d^5\). Thus
\[
(C'_d)^{d-1}\le d^{(37/4)d+39/4}\le d^{19(d-1)},
\]
where the final inequality is exactly \(39d\ge115\), valid already at
\(d=3\). Hence \(C'_d\le d^{19}\), proving (8). \(\square\)

## 5. What is genuinely sharp, and what remains open

The accompanying complete notes isolate different hypotheses.

- [halfmass.md](halfmass.md) proves that the cone-specific power \(2/3\),
  its near-half-mass tail power two, and the contact-slab area power two are
  sharp for actual cone laws in every fixed \(d\ge3\). The bodies are a
  doubly truncated three-cube times intervals, already in John position.
- [matching.md](matching.md) proves that the improved power \(1/2\) is sharp
  for bounded laws with determinant mass bounded below, even over every choice
  of basis and every line/plane decomposition. Its first obstruction is an
  arbitrary even law. The separate [global-next.md](global-next.md) strengthens
  the sharpness statement to actual cone laws and proves a geometric
  all-product distance obstruction for that family.
- [geometry-next.md](geometry-next.md) proves that the cap exponent \(1/d\)
  is sharp under volume-only information. With the stronger off-block normal
  measurement, truncated cubes instead exclude powers above \(1/(d-1)\).
  The general recovery theorem with power \(1/(d-1)\), now proved directly
  in [geometry-rigidity.md](geometry-rigidity.md), closes this intermediate
  geometric gap. It is sharp for the stronger normal input.

These sharpness examples do not establish optimality of (8): independent
losses need not be simultaneously sharp on the same cone law. They rule out
improving the first two isolated lemmas under their present hypotheses, and
explain why a further gain should retain more geometry or couple the stages.

The universally valid weighted relation
\[
\mathbb E[\phi g]\le(d+1)A\delta,
\quad g=1/2-\max_i(|c_i|/\sum_j|c_j|),
\]
with \(g=0\) on the singular event \(\sum_j|c_j|=0\),
retains information lost by the unweighted fourth-cofactor moment. On the
sharp half-mass family, the actual mixed-volume support surplus is linear in
\(\delta\). However, inserting an extra global containment factor into the
support-surplus estimate is false: the explicit near-coordinate cuts in
[geometry-next.md](geometry-next.md) give a counterexample. No unproved
coupled support-surplus theorem is used in either bound.

No quantitative inverse-Minkowski theorem is a proof input. The direct
section/coarea proof supplies the geometric estimate used here.

## 6. Dependency and verification scope

The complete baseline proof is included in
[dependencies/completed-proof.md](dependencies/completed-proof.md). Its
corrected text has SHA-256
`6a31c8d2dff76b3f73b862a0b6ef2ea192afc9de23b3605208b465ee3a5c1193`;
the immutable original has SHA-256
`08f6f55c6a694da05d348d3dcbda18be186044fd39570c51bf786507aaef862c`.
The baseline pins the v2–v4 sources of `mxym/math` to
`6785c1c830f8e19e2eb07b0bb89f4d475a8b154a`. The exact dependency map remains
applicable. Bibliographic attributions and comparisons are corrected separately;
this package includes the corrected baseline mathematical proof in
`dependencies/completed-proof.md`. Neither the lower-end simplex modulus
nor the v5 spectral recursion is imported here.

The new rational programs check the polynomial identities and exact examples
described in their adjacent notes. They use explicit exceptions and retain
checks under Python optimization. They do not prove the general integral,
surface-measure, or convex-geometric assertions. The written proof and its
independent model audit are separate from these finite regressions. No human
peer review, proof-assistant verification, or novelty claim is made.

The optimal final exponent remains unresolved between \(1/[3(d-1)]\)
and \(1/d\). The isolated intermediate examples do not establish
optimality of the composed bound. The original completed release is preserved.
