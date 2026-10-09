# Qutrit–qudit APPT: Lean formalization continuation

**Status: IN PROGRESS; NOT a complete APPT purity formalization.** This
working copy is separate from the immutable
[`appt-qutrit-purity-interim-v1`](https://github.com/mxym/math/releases/tag/appt-qutrit-purity-interim-v1)
Release. No interim sources, recorded hashes, or Release assets are changed.

The modules are built with Lean 4.34.1 and pinned Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The initial refactor
extracts small, independently compilable pieces of the all-`n` proof:

- `APPT.UniformDefs`: definitions of the outer spectrum and population sums;
- `APPT.UniformSpectrumGaps`: exact gap inversion and nonnegativity;
- `APPT.SpectrumReindex`: sorted outer index map and middle/outer sum split.

The original 1,635-term polynomial identity remains in `APPT.Uniform`.
Its Lean kernel compilation is **not established**. Consequently
`UniformBridge` and `OrderedSpectrum` remain dependent on an uncompiled
module, regardless of the status of their independent components.
A full proof still needs all-`n` polynomial kernel verification, APPT-to-
Hildebrand necessity, quantum attainment (all unitary orbits), and a final
state-level theorem. The six finite-dimensional certificate bounds are
already in the immutable interim package and are copied unchanged here.

Run the pinned modular smoke build from `lean/`:

```bash
lake exe cache get
lake build APPT.Core APPT.Compression APPT.UniformDefs APPT.UniformSpectrumGaps APPT.SpectrumReindex
```

The corresponding GitHub Actions workflow is
`.github/workflows/appt-qutrit-lean-progress.yml`.
Passing this build would *not* establish the full all-`n` result.
