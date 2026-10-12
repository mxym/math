# Geometry gate: exact obstructions and one restricted improvement

Date: 7 October 2026. This note leaves the completed quantitative theorem
unchanged. It isolates what can and cannot be inferred from the inputs of its
product-recovery lemma. Every assertion below is proved explicitly; the
general recovery theorem subsequently obtained is in the separate note
`geometry-rigidity.md`.

## 1. Measurements and a cancellation worth preserving

Let \(Q\) be a centered full-dimensional convex body, let
\(\mathbb R^d=\bigoplus_j W_j\) be an orthogonal decomposition, and write
\(\mathcal W=\bigcup_jW_j\),
\(P=\prod_j\operatorname{proj}_{W_j}Q\). Set

\[
s(Q,\mathcal W)=\mathbb E_{\nu_Q}\operatorname{dist}(X,\mathcal W),
\qquad
v(Q,P)=\mathbb E_{\nu_Q}[h_P(X)-1].
\]

Because distance to the union of linear subspaces is homogeneous, the cone
weight cancels exactly:

\[
s(Q,\mathcal W)=\frac1{d|Q|}\int_{S^{d-1}}
       \operatorname{dist}(u,\mathcal W)\,dS_Q(u).       \tag{G1}
\]

There is no support-height factor left in (G1). This is valid for arbitrary
surface-area measures, including atoms. The mixed-volume identity likewise is

\[
v(Q,P)=\frac1{d|Q|}\int(h_P(u)-h_Q(u))\,dS_Q(u)
       =\frac{V(Q[d-1],P)}{|Q|}-1.                    \tag{G2}
\]

The completed proof bounds \(v\le R(\sqrt m+1)s\), then converts relative
volume loss into a containment loss. The example below distinguishes those
two steps.

## 2. A complete exact calculation for weighted corner cuts

Fix \(d\ge3\), positive coefficients \(a_i\le1\) with
\(\max_i a_i=1\), and \(0<t\le\min_i a_i\). Let

\[
S=\sum_i a_i,\quad H=S-t,\quad A_* =\prod_i a_i,\qquad
Q_{a,t}=[-1,1]^d\cap\{x:|\langle a,x\rangle|\le H\}.      \tag{G3}
\]

Both removed corner simplices are contained in their respective cube corner
regions: writing \(y_i=1-x_i\), the positive cap is
\(y_i\ge0,\ \sum_i a_i y_i<t\), and its intercepts are
\(t/a_i\le1\). Their interiors are disjoint. In particular

\[
V:=|Q_{a,t}|=2^d-\frac{2t^d}{d!A_*}.                      \tag{G4}
\]

For any coordinate block of size at most two, its projection is the entire
coordinate cube. Indeed, at any vertex of that block choose signs among the
remaining coordinates so that the full vertex is neither of the two
all-equal vertices. Such a full vertex has
\(|\langle a,x\rangle|\le S-2\min_i a_i\le S-t\).
All coordinate-block cube vertices therefore lift to points of \(Q_{a,t}\),
and convexity proves the claim. Hence \(P=[-1,1]^d\) for every such
coordinate partition. (The same statement holds for a single coordinate
projection without needing a partition.)

Each coordinate facet has area

\[
\alpha_i=2^{d-1}-\frac{t^{d-1}}{(d-1)!\prod_{k\ne i}a_k}.
\]

The two new facet area-normal vectors are

\[
\pm c a,\qquad c=\frac{t^{d-1}}{(d-1)!A_*}.                \tag{G5}
\]

For example, projecting a new facet onto \(e_i^\perp\) gives a
\((d-1)\)-simplex of volume
\(t^{d-1}/((d-1)!\prod_{k\ne i}a_k)=ca_i\), proving (G5) by
the projection area formula. All old facet normals belong to \(\mathcal W\),
and the new cone-law sample is \(\pm a/H\). Consequently the exact formulas
are

\[
\boxed{
s(Q_{a,t},\mathcal W)
 =\frac{2t^{d-1}\operatorname{dist}(a,\mathcal W)}
        {d(d-1)!A_* V},\qquad
v(Q_{a,t},P)=\frac{2t^d}{d(d-1)!A_* V}.
}                                                        \tag{G6}
\]

Their ratio is particularly informative:

\[
\frac{v}{s}=\frac{t}{\operatorname{dist}(a,\mathcal W)}.     \tag{G7}
\]

These formulas account for every facet, rather than just the new faces. The
normalization can also be checked directly:

\[
2\sum_i\alpha_i+2cH=dV.
\]

The maximal centered homothetic containment is exactly

\[
\lambda P\subseteq Q_{a,t},\qquad
\lambda=\frac{S-t}{S},\qquad \tau:=1-\lambda=\frac tS.     \tag{G8}
\]

Indeed, the sole new slab constraint forces and suffices for this factor.

## 3. Two sharp upper restrictions, with different exponents

For \(a=(1,\ldots,1)\), write \(K_t=Q_{a,t}\). If the coordinate
partition has largest block dimension \(b\in\{1,2\}\), then

\[
s(K_t,\mathcal W)=
\frac{2\sqrt{d-b}}{d(d-1)!|K_t|}\,t^{d-1},\qquad
v(K_t,P)=\frac{2}{d(d-1)!|K_t|}\,t^d.                     \tag{G9}
\]

Here \(P=[-1,1]^d\),
\(\tau=t/d\), and
\(\theta=1-|K_t|/|P|=2t^d/(d!2^d)\).
Thus the relative-volume-to-homothetic-containment exponent \(1/d\) is
optimal already in this nested symmetric family. It cannot be increased
even when both bodies have uniformly bounded radii and a fixed positive
inradius.

For the stronger conclusion involving distance to the **entire** product
class, the completed and independently audited Theorem B proves

\[
D(K_t,\mathcal E_d)-1\ge\frac{t}{5d^2}.                    \tag{G10}
\]

Combining (G9) and (G10) proves the following precise intermediate
obstruction. No estimate

\[
D(Q,\mathcal E_d)-1\le C_{d,r,R}s(Q,\mathcal W)^\beta
\]

can hold for all bodies and all coordinate line/plane decompositions with
\(rB\subseteq Q\subseteq RB\) when \(\beta>1/(d-1)\).
One may take \(r=2/3\), \(R=\sqrt d\), and the same fixed partition
throughout: \(K_t\) contains \((1-t/d)[-1,1]^d\), so these bounds hold
for \(0<t\le1\). This obstruction does **not** prove that the present
geometric \(1/d\) exponent is sharp as a function of \(s\). The exact
normal measurement has a different scale from relative missing volume.

## 4. A rigorous \(1/(d-1)\) recovery theorem for this full weighted family

Assume in addition \(t\le1/2\). Choose a coordinate block attaining the
maximum projected norm of \(a\). At least one index \(k\) is outside
that block because every block has dimension at most two and \(d\ge3\).
Since all coefficients are at most one,

\[
A_*\le a_k\le\operatorname{dist}(a,\mathcal W).
\]

Using \(V\le2^d\) in (G6) gives

\[
s\ge\frac{t^{d-1}}{d!2^{d-1}}.
\]

Since \(S\ge1\), (G8) yields

\[
D(Q_{a,t},\mathcal E_d)-1
\le\frac{t}{S-t}\le2t
\le\boxed{2\bigl(d!2^{d-1}s\bigr)^{1/(d-1)}}.             \tag{G11}
\]

This restricted theorem is uniform over arbitrarily small coefficients

\(a_i\), subject only to \(t\le\min_i a_i\): nearly coordinate normals
do not destroy the improved exponent for weighted corner cuts. Together
with (G9)–(G10), it identifies \(1/(d-1)\) as the optimal geometry
exponent within this family. It does not silently assert that the general
body is a polytope or belongs to this family.

## 5. An obstruction to an attractive extra-factor argument

It is tempting to replace \(v\le C s\) by \(v\le C\tau s\), with
\(\tau=1-\lambda\). That stronger intermediate assertion is false,
even with fixed radius and inradius bounds and in the explicit family above.

Take \(a=(1,\varepsilon,\ldots,\varepsilon)\), \(t=\varepsilon\),
\(0<\varepsilon\le1/2\), and all coordinate lines as blocks. Then

\[
S=1+(d-1)\varepsilon,\quad
V=2^d-\frac{2\varepsilon}{d!},\quad
\tau=\frac{\varepsilon}{1+(d-1)\varepsilon},
\]

\[
s=\frac{2\sqrt{d-1}\,\varepsilon}{d(d-1)!V},\qquad
v=\frac{2\varepsilon}{d(d-1)!V},\qquad
\frac{v}{\tau s}
=\frac{1+(d-1)\varepsilon}{\sqrt{d-1}\,\varepsilon}
\longrightarrow\infty.                                  \tag{G12}
\]

In particular no constant depending only on \(d\), \(r\), and \(R\)
can justify this factor. Here \(Q\subseteq\sqrt d B\) and, by (G8),
\(Q\supseteq(1-\varepsilon)[-1,1]^d\supseteq\tfrac12 B\).

Even the pointwise proposed estimate

\[
h_P(X)-1\le C\tau\operatorname{dist}(X,\mathcal W)
\]

fails at both new facet samples: the left-hand side is
\(\varepsilon/H\), whereas the distance is
\(\sqrt{d-1}\varepsilon/H\). The ratio before inserting \(\tau\)
is fixed. The small facets responsible for a missing corner can instead be
macroscopic nearly coordinate facets, with a normal angle of order
\(\varepsilon\). This is an actual convex-body counterexample, not a
synthetic law unrelated to its body.

## 6. What this resolves and what remains

The cap-to-distance step is sharp **under its volume-only input**. The
separate note `geometry-rigidity.md` now proves the general
\(1/(d-1)\) recovery theorem under fixed radius and inradius bounds,
with explicit constants. Its direct proof thickens a two-dimensional
convex section and applies the coarea formula to the off-block surface
integral (G1). Thus (G9)--(G10) identify the sharp geometric exponent
under these stronger inputs. No extra \(\tau\) factor is inserted
in (G2), and the volume-only cap conversion is bypassed.

The half-mass and matching stages may also be coupled directly to the
support surplus \(v\), instead of first bounding \(s\). Equations (G7)
and (G12) show why such a coupling must preserve information about the
normal direction and cannot depend only on global containment error.

The all-product distance lower bound (G10) is imported only from the
completed audited theorem; its proof handles arbitrary oblique planar
factor products and does not assume uniqueness of the decomposition.

## 7. Exact finite verification

The adjacent script `check_geometry_next.py` uses rational arithmetic to
verify facet normalization, the exact \(v\) identity, squared \(s\)
identities, and the near-coordinate counterexample for finitely many
dimensions and rational weights. It is supplementary verification, not a
proof of any universal statement. It needs only Python's standard library,
uses explicit exceptions, and retains checks under `python -O`.

The corner-cut examples distinguish missing volume of order \(t^d\) from off-block normal mass of order \(t^{d-1}\). The geometric \(1/(d-1)\) estimate is established separately; the extra containment factor proposed for mixed-volume recovery is contradicted by the displayed family.
