# Independent three-cell Gaussian Lean development: CI repair

Fixed proof commit: `da16f54190bb53651a78640bd94a30a5c2cc9e08`, on `research/gaussian-three-cell-20261008`.

This is a different research branch and workflow from the earlier `research/gaussian-three-cell-elementary-20261008` repair. The failed runs were inspected, and the current branch was compiled in a separate scratch checkout. During repair another contributor added `GaussianThreeSharp` and `GaussianThreeEquality` in commit `2a755ab3aa69be9820a1887ab28a96d9883cd853`; that work was preserved and included in the fix. No force push was used.

## Repairs

- Replace unavailable absolute-value expansion and dependent finite-supremum rewriting with valid pinned Mathlib lemmas and a pointwise upper/lower-bound argument.
- Use the correct inner-product negation lemma, expand pointwise function addition for integral rewriting, restrict vector rescaling to the inner-product argument, and remove a redundant unfolding after `change`.
- Normalize finite-sum associativity, split the positive/negative alternatives produced by `norm_num`, and exclude negative norms by nonnegativity.
- Make reverse-edge norm equalities explicit in the finite equality-classification cases and fully simplify the three-term finite sum.

The mathematical statements and hypotheses were not weakened. No placeholder, custom axiom or unchecked decision procedure was introduced.

## Local verification

Pinned Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` were used. The full default `lake build` succeeded (3,884 jobs), reusing official dependency cache artifacts and previously compiled unchanged owned modules. All four direct `lake env lean` commands used by CI also exited successfully. The four compiled source files match the pushed Git blobs byte for byte; hashes are in [LOCAL_AUDIT.json](LOCAL_AUDIT.json).

All nine printed roots in the width, sharp-bound and equality modules have only `propext`, `Classical.choice` and `Quot.sound` in their transitive axiom inventories. This includes `three_cell_momentEnergy_bound`, `three_cell_energy_equality_iff_regular_fan` and `three_cell_energy_strict_small_dimension`. See the saved local build and direct-compile logs. This is a normal Lean compiler/kernel check, not a new empty-environment replay of every dependency.

## Remote verification

GitHub Actions completed successfully on the exact fixed commit: https://github.com/mxym/math/actions/runs/37865338678. All workflow steps passed, including the complete Lake build and the four direct module compilations. All nine theorem-root inventories were printed during both build and audit; every inventory contains only the three standard logical axioms, and no `sorryAx` appears. See [CI_STATUS.json](CI_STATUS.json) and [ci.log](ci.log).

## Reproduction

Check out the exact fix commit, enter `formalizations/gaussian-simplex-all-k-progress/`, and use its pinned toolchain and manifest:

```sh
lake exe cache get
lake build
lake env lean sources/GaussianThreeScoreAlgebra.lean
lake env lean sources/GaussianThreeGaussianWidth.lean
lake env lean sources/GaussianThreeSharp.lean
lake env lean sources/GaussianThreeEquality.lean
```

The repaired endpoint concerns actual equal-mass three-label Gaussian fractional partitions and their equality cases. It does not extend the completed Lean theorem to all numbers of cells or establish a mathematical novelty claim. The all-k preprint and its published-theorem-based written proof are separate.
