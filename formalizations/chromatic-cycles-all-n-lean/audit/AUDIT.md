# Audit and trust boundary for the complete all-cycle Lean proof

## The mathematical claim

The **public theorem is about the actual Mathlib `SimpleGraph.cycleGraph n`**, not an arbitrary preselected polynomial. The graph-coloring part proves `P_n(q) = Fintype.card (cycleGraph n).Coloring (Fin q)` for **every natural q**. The polynomial coefficient part then proves its signed/absolute coefficient formulas. Finally the infinite-iteration classification is established by an actual invariant-preservation theorem for all iterates and explicit failures outside the positive range.

**Scope:** all `n ≥ 3`; positive side `3 ≤ n ≤ 11`, finite negative cases `12 ≤ n ≤ 16`, symbolic infinite family `n ≥ 17` with a third-iteration witness. Boundary convention is zero extension on `ℕ` including `a₀ = 0`.

## Compiled proof chain

Modules are compiled in the order recorded in `scripts/replay.sh` or by the standard Lake target `ChromaticCyclesAllN`:

1. `CycleSequenceAlgebra`: binomial first-six formulas, exact third iterate, quartic positivity for arbitrary `n ≥ 17`.
2. `CyclePolynomialAll`: extracts actual signed coefficients of the explicit polynomial, proves the binomial formulas from `Nat.choose`, and propagates equality through three iterates.
3. `CycleInfinitePositive`: proves the three-factor strong invariant is preserved for **arbitrary iterations**, finite certificates for all 3–11, finite failures for 12–16, and their all-`n` classification.
4. `CyclePolynomialClassification`: connects the coefficient formula and the all-iterate theorem for the explicitly defined polynomial.
5. `GeneralCycleColoring`: proves genuine `cycleGraph n` adjacency is equivalent to modular successor adjacency for **all `n ≥ 3`**, with no fixed 17 assumption.
6. `GeneralCycleWalk`, `GeneralCycleLoops`, `GeneralColorLoopCard`, `GeneralColorLoopBijection`: build the closed complete-color-graph walk from any proper cycle coloring and back; prove injectivity on both finite sides, and establish exact equality of cardinalities.
7. `GeneralCycleTrace`: proves the complete-graph adjacency-matrix identity and trace formula in terms of `(q − 1)^n` and `(-1)^n`.
8. `GeneralCycleChromatic`: combines these into the all-q counting specification and the **actual graph/chromatic-polynomial infinite classification**.

## Source and toolchain pins

`lean-toolchain` fixes Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`). `lake-manifest.json` fixes Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` along with all transitive upstream git revisions. Other revisions are **not** silently treated as verified. `SHA256SUMS` pins all publication-owned source and audit assets. Binary compiled `.olean` caches, private machine paths and downloaded toolchains are **not committed**.

## Actual kernel trust

The all-length theorem and its graph, coefficient and infinite-iteration components were recompiled under Lean 4.34.1. `audit/AxiomsAudit.lean` asks Lean to report the axioms for each exported root; `scripts/check_axioms.py` rejects any axiom outside the standard set `{propext, Classical.choice, Quot.sound}`. `audit/InvalidProof.lean` is a deliberately invalid `False` proof and **must fail compilation**. The shell verifier treats any unexpected acceptance as failure. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or arithmetic trust shortcuts occur in the owned main proof modules.

The formalization does *not* independently re-prove the Mathlib library or the trusted Lean kernel; those are the explicit upstream dependencies. It does not assert a separate human mathematical peer-review outcome.

## Reproduction

```sh
lake exe cache get
bash scripts/replay.sh
(cd . && sha256sum -c SHA256SUMS)
```

The package-level GitHub Actions workflow runs equivalent steps using [`leanprover/lean-action@v1`](https://github.com/leanprover/lean-action) on a clean runner and checks the source manifest. A GitHub Actions **green run is reported only when it actually succeeds**.

The previous [C17-only Lean proof](../../chromatic-infinite-logconcavity-counterexample/README.md) is an independent earlier result and is preserved unchanged. This package does not overwrite or reassign its provenance.
