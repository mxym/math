# Mathematical correctness, dependency and reproducibility audit

**Date:** 8 October 2026. **Status:** Model-assisted author self-audit. No external human peer review, blanket originality claim or proof-assistant formalization is asserted.

## Scope of the new claims

- The improved lower floor `T>486139/10^7` applies to **any** finite or countably summable nonnegative coefficient sequence in the *even-power* Bellman family, **assuming one checks separate product closure at all actually attainable pairs of operands**. It does **not** assert that the true recursive-class growth constant is above `exp(1+48613/10^6)`, or rule out a different proof architecture yielding the binary `T5` constant.
- The three necessary self-product constraints come from **real point-generated polytopes** in dimensions 5, 13, 36. Their H-values follow directly from the exact inherited product/join formulas; the source's [exact 48D Pareto data](../exact-product-join-finite-optima/certificates/frontiers48.json) are separately hash-pinned and cross-checked.
- The sharper separate `check_sharp_dual.py` **solves the entire infinite three-state moment linear programme exactly**: rational dual weights computed by Cramer’s rule saturate precisely degrees 2,4,8, while the unique positive primal coefficients solve the corresponding logarithmic 3-by-3 linear system; every other even degree is strictly dual-inactive. This does not establish global product closure of that primal profile.
- The original weighted obstruction is a **rational dual inequality**, not a numerical linear-program decision. Six even-degree columns are tested as rational comparisons. A single rational geometric power bound closes **all degrees 14,16,18,... without a maximum degree**. Three logarithms of positive rational multipliers are bounded by rational atanh intervals and shown strictly greater than `48613/10^6` after weighting.
- The third theorem forces infinite exact orbit anchors and the unique near-zero quadratic curvature of **any continuous convex sharp homogeneous Bellman supersolution** built by ordinary separate closure; the rational curvature interval is rigorously enclosed. The second theorem concerns the particular *exact binary-tail rate functional*. The proven negative join defect `<-3/10` prevents its direct use in ordinary join induction. This does not disprove the direct inequality that all binary continuations are bounded by the T5 continuation; it only invalidates one route to establishing that inequality. Finally a fully rational convex hinge profile is checked to satisfy the original three self-product tests at endpoint `191/4000` but fail at the attained level-two T5 binary seed `(85,24)`. This witnesses both the limited scope of the power-cone obstruction and the need for all-dimensional tests.

## Inherited inputs and reproducibility

1. **Affine geometry**: the exact point-generated `D,H,Q` calculus and `H`-range are from `preprints/005-simplex-product-optimum/v2/paper.md`, pinned Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`. That manuscript credits the upstream OpenAI/math family-088 simplex-product mechanism.
2. **Strict certified binary-orbit upper endpoint**: `notes/mixed-bellman-product-join/sharpened-binary-lower/LIMIT_INTERVAL.md` and `check_limit_interval.py` independently place the binary \(T_5\) orbit rate below `2.853465550704`. Our first checker proves `exp(1+48613/10^6)` exceeds this rational endpoint using only positive rational Taylor terms; it does not recompute the inherited endpoint in that checker.
3. **Attainable reference states**: `notes/exact-product-join-finite-optima/certificates/frontiers48.json` is pinned by SHA-256 `975c4cc5c37f309426d57661e8b5d4dcb45fb2811c6a000da3204faeb4ddea38`. The older file has its own complete independent checker and is not modified.
4. **Analytic inputs**: only standard Robbins factorial bounds and elementary convexity/positive Taylor series are used, all explicitly displayed in `paper.md`. The `G(d)` series in the second theorem is *infinite* but its omitted tail is bounded for **every** index, and the two-sided pi bracket is checked from Machin's arctangent identity.

## Checkers and trust boundary

`code/check_sharp_dual.py` independently proves exact strong duality and uniqueness in the infinite three-state relaxation. `code/check.py` checks explicit source geometries, every finite dual column, the all-degree tail cutoff, the weighted lower logarithmic bound, and a concrete convex hinge escape/failure profile. `code/check_binary_tail.py` separately verifies the exact binary normalization, Robbins/pi rational enclosures, an entire infinite-series tail, the strict negative join defect and the orbit-imposed quadratic-curvature interval. `code/negative_controls.py` attacks a falsely increased floor, bad dual weights, impossible source geometry, a false pi bracket, and a corrupted binary-tail functional; each must cause an exception.

Both checkers make all decisions with exact Python integers and `fractions.Fraction`, never with floating point, a proprietary solver, optimization heuristics, network input or `assert` statements. Mathematical truth also depends on the standard Robbins analytical estimate and the imported affine geometric calculus, not just scripts returning success. Ordinary and optimized Python reports are frozen and compared byte-identically.

Read-only replay from repository root:

```sh
python3 notes/projection-bellman-power-obstruction/code/check.py
python3 -O notes/projection-bellman-power-obstruction/code/check.py
python3 notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 -O notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 -O notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 notes/projection-bellman-power-obstruction/code/negative_controls.py
(cd notes/projection-bellman-power-obstruction && sha256sum -c SHA256SUMS)
```

These results do not classify the global extremum, establish a new lower construction, or validate a sharp nonpolynomial Bellman supersolution. That remains the high-priority research gap.
