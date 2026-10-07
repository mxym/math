# Finite multiscale counterexamples to integer-degree harmonic dimension comparison

## 1. Statement

For a complete Riemannian manifold \((M,g)\) and \(d\ge 0\), let
\(\mathcal H_d(M,g)\) be the space of harmonic functions satisfying
\[
 |u(x)|\le C_u(1+d_g(o,x))^d,
\]
and write \(h_d(M,g)=\dim_{\mathbb R}\mathcal H_d(M,g)\).
For Euclidean three-space and integer \(d\ge0\),
\[
 h_d(\mathbb R^3,g_{\mathrm E})=(d+1)^2.
\]

The three-dimensional construction in OpenAI/math family 361 proves that,
for every sufficiently large integer \(k\), one can choose a metric
depending on \(k\) for which this comparison fails.  We show that any
prescribed finite number of widely separated scales can instead be handled
by one metric.

**Theorem 1 (finite multiscale counterexample).**
Fix
\[
 \varepsilon>0,\qquad m\in\mathbb N,\qquad 1<\beta<\frac32.
\]
Given arbitrary lower bounds \(K_1,\ldots,K_m\), there exist integers
\[
 K_r\le k_r,\qquad k_1<k_2<\cdots<k_m,
\]
and a single complete smooth metric \(g\) on \(\mathbb R^3\) such that:

1. \(g\) is Euclidean near the origin,
   \(\operatorname{Ric}_g\ge0\), and \(\operatorname{Ric}_g>0\) outside
   a compact set;
2. the identity map is globally \((1+\varepsilon)\)-bi-Lipschitz:
   \[
   (1+\varepsilon)^{-2}g_{\mathrm E}
   \le g\le
   (1+\varepsilon)^2g_{\mathrm E};
   \]
3. simultaneously for every \(r=1,\ldots,m\) and every integer
   \[
   k_r\le d\le \lfloor\beta(k_r+1)\rfloor-1,
   \]
   one has
   \[
   h_d(\mathbb R^3,g)>(d+1)^2
   =h_d(\mathbb R^3,g_{\mathrm E}).
   \]

The integers \(k_r\) may be taken arbitrarily far apart.  The metric can
also be chosen with asymptotic volume ratio arbitrarily close to one.  It
has the same qualitative tangent-cone and radial-sectional-curvature
features as the pinned upstream construction: uncountably many pairwise
nonisometric pointed tangent cones at infinity, and negative radial
sectional planes along a sequence tending to infinity.

The theorem does not assert the existence of one metric with violations at
infinitely many unbounded degrees.  It proves every finite version of that
quantifier reversal.

## 2. Pinned ingredients from the three-dimensional construction

All imported analytic ingredients are pinned in DEPENDENCIES.md.  We use
the fixed-area angular gauge \(h(w)\) on \(S^2\), the round metric
\(g_0\), and
\[
 B_\ell=(\ell+1)^2.
\]
For a sufficiently small conformal neighborhood \(\mathcal U\), the
upstream proof supplies the following facts.

### 2.1 Ordered-frequency comparison

After shrinking \(\mathcal U\), there is \(C_*>1\), as close to one as
desired, such that for every \(H=h(w)\), \(w\in\mathcal U\),
\[
 \lambda_j(H)\le C_*\,\ell(\ell+1)
 \quad\text{whenever}\quad
 B_{\ell-1}<j\le B_\ell.
\]
Writing
\[
 \mathfrak d(x)=\frac{-1+\sqrt{1+4x}}2,
\]
we have \(\mathfrak d(x)\le\sqrt x\), hence
\[
 \mathfrak d(a^{-2}\lambda_j(H))
 <
 a^{-1}\sqrt{C_*}\,(\ell+1).
 \tag{2.1}
\]

### 2.2 Isolated adjacent doubles

For
\[
 L=\lfloor\sqrt k\rfloor,\qquad
 M=\lfloor\vartheta k\rfloor,\qquad
 I=\{B_L+1,\ldots,B_M\},
\]
the upstream adjacent-double lemma gives, for every sufficiently large
\(k\), an exact isolated double at each adjacent pair in \(I\), inside any
prescribed sufficiently small \(\mathcal U\).

The retaining-double lemma is stronger than the cutoff used in the
one-scale paper: if a chosen exact double lies at positions \(i,i+1\),
then for every finite \(q\ge i+1\) it can be perturbed arbitrarily little
while keeping that double exact and making every other spectral inequality
through \(q\), including the gap after \(q\), strict.

The finite-cutoff avoidance lemma joins simple endpoints by a path that is
simple through any prescribed finite cutoff.  These two lemmas let one
place doubles from several disjoint bands into one common finite program
while protecting the largest cutoff.

### 2.3 Finite-program realization

The radial, transfer, matching, and growth parts of the upstream proof use
only the following properties of a fixed finite periodic angular program:

- a common fixed area form and a uniformly positive Gauss-curvature margin;
- a protected outer gap after a fixed finite rank \(p\);
- a smooth continued real eigenframe through the first \(p\) positions;
- only finitely many isolated, linearly split double crossings per period;
- at every crossing, a conformal control direction with nonzero
  off-diagonal first variation;
- for each pair of continued labels, either a uniform gap or isolated
  simple crossings recurring with bounded phase gaps;
- finite smooth bounds for the fixed program.

No step in those sections uses the fact that the return permutation has
only one nontrivial cycle.  Consequently the same proofs apply to any
finite program satisfying the list above.  They produce one complete
Ricci-nonnegative metric and \(p\) independent entire harmonic functions
whose exact logarithmic growth exponents are the periodic means of the
continued cone frequencies
\[
 \mathfrak d(a^{-2}\lambda_i(s)).
 \tag{2.2}
\]
A dependency-by-dependency audit is in PROOF_AUDIT.md.

## 3. A finite multiband angular program

We now build one angular program for \(m\) scales.

Choose numbers
\[
 \beta<\vartheta<\frac{3a}{2},\qquad \frac23<a<1,
\]
with \(a\) sufficiently close to one for the desired
\((1+\varepsilon)\)-bi-Lipschitz bound.  Choose
\[
 a^2<\kappa_*<1.
\]
Shrink \(\mathcal U\) so that every link in it has Gauss curvature
greater than \(\kappa_*\), the tensor comparison needed for the final
bi-Lipschitz estimate holds, and
\[
 \frac{2\vartheta}{3a}\sqrt{C_*}<1.
 \tag{3.1}
\]

We choose the integers \(k_r\) recursively and arbitrarily large.  Put
\[
 L_r=\lfloor\sqrt{k_r}\rfloor,\qquad
 M_r=\lfloor\vartheta k_r\rfloor,\qquad
 p_r=B_{M_r}=(M_r+1)^2,
\]
and
\[
 I_r=\{B_{L_r}+1,\ldots,B_{M_r}\}.
\]
Besides all one-scale largeness requirements, impose
\[
 M_{r-1}<L_r\qquad(r\ge2).
 \tag{3.2}
\]
This is possible because \(k_r\) has no upper restriction.  Thus the
bands \(I_r\) are pairwise disjoint.

The same asymptotic calculation as in the one-band angular program gives
\[
 a^{-1}\sqrt{C_*}\,
 \frac{\displaystyle
   \sum_{\ell=L_r+1}^{M_r}(2\ell+1)(\ell+1)}
 {\displaystyle
   (M_r+1)^2-(L_r+1)^2}
 <k_r
 \tag{3.3}
\]
after \(k_r\) is sufficiently large.  Indeed, after division by \(k_r\),
the left side tends to
\[
 \frac{2\vartheta}{3a}\sqrt{C_*}<1.
\]
We also require
\[
 a^{-1}\sqrt{C_*}(L_r+1)<k_r
 \tag{3.4}
\]
and
\[
 M_r\ge\lfloor\beta(k_r+1)\rfloor.
 \tag{3.5}
\]
All these are eventually automatic.

Set \(p=p_m\).  For each adjacent pair \(i,i+1\) lying in one of the
bands \(I_r\), first take the double supplied by the adjacent-double
lemma.  Apply the retaining-double lemma with the common cutoff \(p+1\).
The resulting metric still lies in \(\mathcal U\), still has the exact
double at \(i,i+1\), and has no other multiplicity through \(p+1\).
Choose a short crossing segment through it with nonzero linear splitting.

Choose one base parameter simple through \(p+1\).  By finite-cutoff
avoidance, join the two endpoints of every crossing segment to this base
by paths simple through \(p+1\).  The resulting loop has precisely the
designated double through the protected range.  Reparametrize each loop
smoothly so that it is constant near all joins.

For each \(r\), concatenate the loops for
\[
 i=B_{L_r}+1,\ B_{L_r}+2,\ \ldots,\ p_r-1
\]
in that order, and concatenate the \(m\) band programs.  Extend the
resulting path periodically with period \(S\).

Let \(C\) be the return permutation of continued labels after one period.
Because every designated adjacent transposition stays inside one band,
\[
 C=C_1C_2\cdots C_m,
\]
where the supports are disjoint, each \(C_r\) is one cycle on \(I_r\),
and every position outside the union of the \(I_r\) is fixed.  No
unwanted crossing occurs through \(p+1\).

## 4. Mean frequencies for all scales at once

The crucial point is that adding the other bands does not change the
rank-average identity.

Fix \(r\) and a label \(i\in I_r\).  Let
\[
 N_r=|I_r|=(M_r+1)^2-(L_r+1)^2.
\]
At a noncrossing phase \(t\in[0,S]\), let \(\sigma_t\) be the permutation
that maps the ranks at the period base to the ranks at phase \(t\).
Every partial permutation is a product of adjacent transpositions within
the separate bands, so
\[
 \sigma_t(I_r)=I_r.
\]
In the \(q\)-th repetition of the period, the rank of label \(i\) at the
same phase is
\[
 \sigma_t C^q(i).
\]
As \(q=0,\ldots,N_r-1\), the points \(C^q(i)\) run once through \(I_r\).
Therefore, ignoring the finitely many crossing phases of measure zero,
\[
 \frac1{N_rS}\int_0^{N_rS}
   \mathfrak d(a^{-2}\lambda_i(s))\,ds
 =
 \frac1{N_rS}\int_0^S
   \sum_{j\in I_r}\mathfrak d(a^{-2}\lambda_j(H(t)))\,dt.
 \tag{4.1}
\]
This identity is exact.  In particular, the durations and geometry of all
the other band loops are already averaged over the full set of ranks in
\(I_r\); they create no extra error term.

Applying (2.1) rank by rank to (4.1) gives precisely the left side of
(3.3).  Hence every label in \(I_r\) has mean frequency strictly below
\(k_r\).

Now consider a label among the first \(p_r\).

- If it belongs to an earlier band \(I_q\), \(q<r\), its mean is below
  \(k_q<k_r\).
- If it lies in no band, then its rank is fixed throughout the program.
  By the disjointness condition (3.2), every such rank at most \(p_r\)
  but outside \(I_r\) and all earlier bands lies at or below \(B_{L_r}\).
  Its instantaneous frequency is therefore bounded by
  \(a^{-1}\sqrt{C_*}(L_r+1)<k_r\).
- If it belongs to \(I_r\), (4.1) and (3.3) apply.

Thus, writing \(\mu_i\) for the periodic mean of the \(i\)-th continued
frequency,
\[
 \max_{1\le i\le p_r}\mu_i<k_r
 \qquad(r=1,\ldots,m).
 \tag{4.2}
\]

## 5. One metric and all harmonic functions

The combined program is finite.  It has the protected gap after \(p=p_m\),
finitely many isolated simple double crossings, the required control
directions, and the same fixed-area and curvature bounds as the one-band
program.  Apply the finite-program realization from Section 2.3.

It gives one complete smooth metric \(g\) and \(p_m\) independent entire
harmonic functions
\[
 U_1,\ldots,U_{p_m}.
\]
For every \(i\), the exact logarithmic spherical growth exponent of \(U_i\)
is \(\mu_i\).  The all-radius contraction and local elliptic estimate in
the pinned growth proof imply that whenever \(\mu_i<k\),
\[
 U_i\in\mathcal H_k(\mathbb R^3,g).
\]
Applying this separately to each finite prefix in (4.2) yields
\[
 h_{k_r}(\mathbb R^3,g)\ge p_r=(M_r+1)^2.
 \tag{5.1}
\]

The metric is the same for all \(r\).

## 6. Consecutive blocks at every selected scale

Let
\[
 D_r=\lfloor\beta(k_r+1)\rfloor-1.
\]
By (3.5), \(D_r\le M_r-1\).  The inclusion
\(\mathcal H_{k_r}\subseteq\mathcal H_d\) for \(d\ge k_r\), together with
(5.1), gives for every integer \(k_r\le d\le D_r\)
\[
 h_d(\mathbb R^3,g)
 \ge (M_r+1)^2
 > M_r^2
 \ge (d+1)^2.
\]
This proves the simultaneous comparison failure on all \(m\) blocks.

The recursive choice of \(k_r\) only imposes lower bounds, so the prescribed
\(K_r\) can be met and the scales can be separated by arbitrarily large
factors.

## 7. Geometry of the final metric

The radial realization is exactly the pinned one applied to the combined
finite angular program.  Hence \(g\) is Euclidean near the origin,
complete, Ricci nonnegative, and Ricci positive outside a compact set.

Choose \(a\) and the tensor neighborhood as in the near-Euclidean
corollary of the upstream paper.  Then
\[
 (1+\varepsilon)^{-2}g_{\mathrm E}
 \le g\le
 (1+\varepsilon)^2g_{\mathrm E}.
\]
Its asymptotic volume ratio is \(a^2\), which can be made arbitrarily close
to one.

The combined angular path is nonconstant because it contains designated
crossings.  The tangent-cone argument from the pinned geometry section
therefore still gives a continuum of nonisometric link spectra and hence
uncountably many pairwise nonisometric pointed tangent cones at infinity.
The same radial-sectional-curvature calculation applies at a phase where
the angular derivative is nonzero and produces negative radial sectional
planes along a sequence escaping to infinity.

## 8. What remains open

Theorem 1 proves
\[
 \forall m<\infty\ \exists g\ \exists k_1<\cdots<k_m
\]
with simultaneous integer-degree failures, and in fact with a linear-size
block of failures around every \(k_r\).

It does not interchange the first two quantifiers to produce one metric
working for infinitely many \(k_r\).  The finite proof deliberately fixes
the largest cutoff \(p_m\) before the radial and graph-transform constants
are chosen.  Passing to infinitely many bands requires a new argument that
controls an unbounded sequence of protected cutoffs or replaces the single
finite graph transform by a compatible diagonal family.  That is the
remaining high-value problem.

No novelty or priority claim is made here.
