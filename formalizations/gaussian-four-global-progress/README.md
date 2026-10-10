# Four equal-mass Gaussian cells — partial Lean formalization

**Partial formalization. The global sharp inequality and complete equality
classification are not proved in this package. No completion Release exists.**

This development extends the repository's actual standard Gaussian measure,
measurable fractional labels, Bochner moments, balanced prices and winning-cell
construction. It does not replace those objects by an abstract finite model.

## Development scope

The new analytic route proves pair separation by integrating a triangular cap
against the actual Gaussian density. It retains the manuscript's constant
`1/(16 φ(0)) = sqrt(2*pi)/16`, applies first to fractional labels separated by a
hyperplane, then to balanced four-cell winning diagrams. The accompanying
boundary statements concern separation of convergent moments, non-coalescence
under a limiting self-moment relation, and the residual estimate in equation
(22). The positive-mass collinear-score argument excludes the degenerate price
relation producing a triple tie.

**Initial source checkpoint:** the new Lean scripts are under active compiler
verification; the presence of a source file is not a passed check. Only later
source-hash-bound build/replay receipts establish verification of those bytes.
Do not treat old Gaussian-package logs as new verification.

`GaussianFour.lean` is the entry point for the partial project.
`DEPENDENCY_MAP.md` records manuscript statements, reusable theorem types and
remaining obligations. In particular, neither the Gaussian multi-bubble theorem
nor single-cell isoperimetry is introduced as an axiom or claimed as proved.

## Pinned build

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and its locked dependencies
are recorded in `lake-manifest.json`. The actual Gaussian layer is the sibling
package `../gaussian-measure-primal-dual` in the same repository revision.

Run from this directory, not from the repository root:

```sh
lake exe cache get
lake build
```

If third-party cache object files were removed while their trace metadata was
retained, an ordinary cache fetch can skip their extraction. After the fetch,
`lake exe cache unpack!` restores downloaded artifacts without that shortcut.
No existing owned object file is acceptable as evidence for changed source.

## Author and provenance

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China
University of Technology. ORCID 0009-0000-3864-3536. Contact:
mxymmxym1@gmail.com. No external funding. AI-assisted research and formalization.
New original material is all rights reserved; existing repository and
third-party notices are preserved. No external human peer review is claimed.
