# State-level spectral moment bridge

`APPT/Quantum/SpectralMoment.lean` proves the exact equalities

- `trace_square_eq_eigenvalues_square`: for every finite Hermitian complex matrix,
  `trace (A*A) = sum (eigenvalues A)^2`;
- `purity_eq_sum_eigenvalues_sq`: the existing real `Quantum.purity` is the
  sum of squares of real Hermitian eigenvalues;
- `density_eigenvalues_sum_one`: the real Hermitian eigenvalues of a density
  matrix sum to one.

These have been independently compiled with Lean 4.34.1 and the pinned Mathlib,
and are recompiled in `.github/workflows/appt-spectral-moment-lean.yml`.
No spectral necessity matrix theorem is assumed here. These identities are
not themselves the final APPT maximal-purity theorem; the remaining semantic
bridge must show actual APPT implies the displayed `matA` and `matB` PSD for
its ordered spectrum, including the qutrit-qudit dimension index equivalence.
