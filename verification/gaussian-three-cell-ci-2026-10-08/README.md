# Elementary three-cell Gaussian CI repair

Fixed proof commit: `c601b080c76f0038aeccba45446d10ce3fa82cf7`, on `research/gaussian-three-cell-elementary-20261008`.

The user's failed workflow was inspected from actual GitHub logs. The earlier integral/Pi-add and scalar-norm rewrite failures received upstream fixes. A subsequent local compilation of the complete current three-cell module found a remaining error in `exact_three_gaussian_model`: `norm_num` converts the squared edge-length equation to the alternatives norm=1 or norm=−1; `nlinarith` cannot split that disjunction. The repair explicitly splits the alternatives and excludes the negative one using norm nonnegativity. No theorem, hypothesis or Gaussian constant was changed, and no check was skipped.

Selected owned dependencies were freshly built in a separate scratch copy with pinned Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, reusing the official dependency cache. The complete corrected `GaussianThreeCellElementary.lean` then compiled with exit code zero. All 13 printed theorem-root axiom inventories contain only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` remains. The compiled source SHA256 equals the pushed Git blob. [Local audit](LOCAL_AUDIT.json).

Remote CI: https://github.com/mxym/math/actions/runs/37863169707. **Completed successfully** on the exact fixed commit: all steps passed, all 13 theorem-root axiom inventories contain only the three standard logical axioms, and no `sorryAx` appears. [CI status](CI_STATUS.json) and [full remote log](ci.log) record the actual evidence.

To reproduce at the exact fixed commit, enter `formalizations/gaussian-simplex-all-k-progress/` with the pinned toolchain, then run:

```sh
lake exe cache get
lake build +GaussianMinimalCovarianceRows +GaussianScoreSymmetry +GaussianHalfspaceFlux +GaussianRegularPerimeter +GaussianRegularStationarity +GaussianEquidistantRigidity +GaussianMomentCovariance
lake env lean sources/GaussianThreeCellElementary.lean
```

The final endpoint is `GaussianMeasureBridge.three_cell_sharp_first_moment` for actual equal-mass fractional Gaussian 3-partitions. This audit does not claim a new empty-kernel replay, all-k formalization, an equality classification or a new mathematical discovery of the known three-cell inequality. The general all-k preprint has an ordinary written proof using the published Milman–Neeman theorem; its incomplete full Lean coverage is a separate issue.
