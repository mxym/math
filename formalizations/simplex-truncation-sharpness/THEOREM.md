# The proved truncation sharpness theorem

**Proved:** `Entry005.truncationSharpness : Entry005.truncationSharpnessGoal`.

**Still open in this package:** `Entry005.sharpMainGoal`, the prescribed-maximum-simplex stability upper bound. The result below is the literal sharpness obstruction, not the full paper or Main.

The formal source of every definition is [Targets.lean](project/formal/Entry005/Targets.lean). The final inhabitant is [TruncationSharpness.lean](project/formal/Entry005/TruncationSharpness.lean#L12). The definitions file has not been weakened or replaced.

## The geometric invariant

Work in `Space d = EuclideanSpace ℝ (Fin d)`. Volumes are the actual Euclidean Borel/Haar volumes; projection volume is measured in the orthogonal subspace with its induced Euclidean volume.

For a set `K` in an `n`-dimensional real Euclidean space and a unit vector `u`, let

\[
b_K(u)=|\operatorname{proj}_{u^\perp}K|_{n-1},\qquad
\Pi K=\{x:\langle u,x\rangle\le b_K(u)\text{ for every unit }u\}.
\]

Thus `projectionBodySet` is an actual intersection of halfspaces. Its identification with the appropriate support-function body or facet zonotope is a theorem used in the proof, not an uninterpreted assumption. Put

\[
R_n(K)=\frac{|\Pi K|_n}{|K|_n^{n-1}},\qquad
P K=\operatorname{conv}\bigl((K\times\{0\})\cup\{(0,1)\}\bigr).
\]

For `K` in dimension `d`, the unchanged definitions are

\[
A(K)=\left(\frac d{d+1}\right)^d\frac{R_{d+1}(P K)}{R_d(K)}-1,
\qquad e(K)=A(K)-\frac1{d+1}.
\]

Here `A` denotes `entryA` and `e` denotes `entryDefect`. The formal divisions and `ENNReal.toReal` operations are the ones in the original target. The proof establishes the relevant finiteness and positivity before using these ratios for `K_t`; it does not obtain a result through an infinite-volume-to-zero conversion.

## Maximum simplex and its own centroid

For a genuine `d`-dimensional `Affine.Simplex` `S`, write `|S|` for the volume of the convex hull of its points. The predicate `maximumInscribed K S` means both

1. the simplex carrier is contained in `K`; and
2. for **every** genuine affine simplex `T` of dimension `d`, containment of `T` in `K` implies `|T| ≤ |S|`.

The second condition ranges over arbitrary inscribed affine simplices. It is not restricted to simplices whose vertices are extreme points of `K`.

Let `g(S)` be `S.centroid`, the centroid of this same original simplex. The formal definitions are

\[
D_a(S)=g(S)+(1+a)(S-g(S)),\qquad
\operatorname{excess}(K,S)=\inf\{a\ge0:K\subseteq D_a(S)\}.
\]

`centeredDilation` is literally the image of the simplex carrier under this homothety, and the infimum is the real `sInf`. No freely optimized center or ambient reference-simplex centroid is substituted.

## Complete quantifiers

For every natural number `d ≥ 3`, every real `α > 1/(d-1)`, every real `C ≥ 0`, and every real `ε > 0`, there exist

- `t` with `0 < t < min(ε,1)`;
- a compact convex body `K` whose carrier is exactly
  \[
  K_t=\{x:x_i\ge0\text{ for all }i,\quad t\le\sum_i x_i\le1\};
  \]
- a genuine affine simplex `S` that is `maximumInscribed K S`;

such that `K` has nonempty interior and

\[
0<e(K)<\varepsilon,
\qquad C\,e(K)^\alpha<\operatorname{excess}(K,S).
\]

The same `t`, `K`, and `S` satisfy all these conjuncts. Both the truncation parameter and the actual positive geometric defect can be made arbitrarily small. The final theorem has no additional premise supplying the actual defect formula, a maximum-simplex identity, a centroid formula, or a projection/pyramid identity.

## Explicit witnesses and exact formulas

For a fixed coordinate index `i`, the proof uses

\[
S_{t,i}=\operatorname{conv}(t e_i,e_1,\ldots,e_d).
\]

The following source results support the final statement:

- [TruncationVolume.lean](project/formal/Entry005/TruncationVolume.lean#L62), `truncation_actual_volume`: for `d > 0` and `0 ≤ t ≤ 1`, the actual real volume is `(1-t^d)/d!`.
- [TruncationMaximum.lean](project/formal/Entry005/TruncationMaximum.lean#L208), `truncationSimplex_maximumInscribed`: for `d > 0` and `0 < t < 1`, `S_{t,i}` satisfies the universal competitor condition.
- [TruncationSimplexActualVolume.lean](project/formal/Entry005/TruncationSimplexActualVolume.lean#L11), `truncation_simplex_actual_volume`: for `d > 0` and `0 ≤ t < 1`, its actual real volume is `(1-t)/d!`.
- [TruncationCentroid.lean](project/formal/Entry005/TruncationCentroid.lean#L201), `truncation_simplex_excess_exact`: for `d ≥ 2` and `0 ≤ t < 1`, the own-centroid excess is `(d+1)t`.
- [TruncationActualDefect.lean](project/formal/Entry005/TruncationActualDefect.lean#L249), `truncation_entryDefect_exact`: for `d ≥ 2` and `0 < t < 1`, the actual defect is
  \[
  e(K_t)=\frac{t^{d-1}\bigl[d(d-1)-(d+1)(d-2)t-2t^d\bigr]}
  {(d+1)(1-t^d)\bigl[d+1+(d-1)t^{d-1}\bigr]}.
  \]
- [TruncationSharpness.lean](project/formal/Entry005/TruncationSharpness.lean#L16), `truncation_entryDefect_pos` and `truncation_entryDefect_quotient_tendsto`: for `d ≥ 3`, the actual defect is positive on `0 < t < 1` and
  \[
  \lim_{t\to0+}\frac{e(K_t)}{t^{d-1}}=\frac{d(d-1)}{(d+1)^2}>0.
  \]

The exact formula is a geometric theorem. `truncationRationalDefect` first packages its right-hand side as a scalar expression; a separate proof identifies that expression with the unchanged `entryDefect`. The conditional assembly lemma is not the final result by itself: [TruncationSharpness.lean](project/formal/Entry005/TruncationSharpness.lean#L12) supplies the proved geometric equality to it.

## Meaning and limits of sharpness

For each `d ≥ 3`, these witnesses obstruct every improved exponent `α > 1/(d-1)` in an inequality asserted for every body and **every** maximum inscribed simplex, even arbitrarily near zero defect. Choosing one actual maximum is enough to contradict such a universally quantified improved upper bound.

The theorem does not say that every maximizing simplex of `K_t` has excess `(d+1)t`, or that the same obstruction remains after taking the infimum over all maximizing simplices. It does not classify all maximizing simplices or formalize the general `S_p` calculations discussed in the preserved analytic notes. It does not prove the critical-exponent upper bound, its explicit `gSharp` constant, an optimal constant, a Banach–Mazur estimate, or a Rogers–Shephard obstruction. No full-paper formalization is claimed.

The old introductory sentence in `Targets.lean` saying that no final target inhabitant is claimed is historical. Its separate comment describing `thresholdGateGoal` as unproved is also historical: the threshold gate has an inherited proof. These comments are preserved for byte identity; the named closed theorem above establishes the current sharpness status, while `sharpMainGoal` remains separate and unproved here.
