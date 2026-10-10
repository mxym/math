# Provenance, licensing, and research disclosure

Author of the new research/formalization material: Yongxian Zhang (张永贤),
School of Computer Science and Engineering, South China University of Technology.
Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536. No external funding.
AI assisted the research, proof development, tooling, and documentation.
Original material retains all rights unless separately authorized; no new
license is imposed on the inherited or third-party work.

Unchanged inherited sources, not claimed as new progress:

* `GaussianPartition.lean`: `mxym/math`, main audit baseline `586ed2e`,
  `formalizations/gaussian-measure-primal-dual/GaussianPartition.lean`,
  Git blob `a6f7bb535b119270ebc68be3ccaf1efaa673164d`.
* `GaussianHalflineFlux.lean`: `mxym/math` commit
  `e6091c945dcf0712a1de22596da78f58a4a6a720`,
  `formalizations/gaussian-simplex-all-k-progress/sources/GaussianHalflineFlux.lean`,
  Git blob `bef8d81d55ee53230ee7ac8a31a07de0229c586f`.
* `GaussianHalfspaceFlux.lean`: the same immutable commit and source directory,
  Git blob `3858d2f9602fb18a1524390351e8e263911729f7`.

The replay verifier is adapted from the existing
`formalizations/gaussian-measure-primal-dual/Replay.lean`; its dependency-closure
collection and empty-kernel checking mechanism are inherited engineering, not a
new mathematical result. Source files are stored with LF line endings.

Lean, Mathlib and their dependencies retain their existing license notices in
the pinned upstream repositories. The lockfile records every exact revision;
no source from those libraries is re-licensed by this package. This stage does
not depend on an unformalized Gaussian multi-bubble theorem, solver oracle, or
external analytic assumption. It does not constitute external peer review or a
claim of first mathematical priority.
