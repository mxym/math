# Actual finite spectral protocols

This package extends the unchanged `spectral-extraction-core` and `spectral-extraction-local-cap` packages. It uses Lean 4.34.1 and the same pinned Mathlib commit. The present first module proves the exact partial-transpose conjugation identity for arbitrary product Kraus maps on all complex input matrices, and derives `Extraction.PTConjugatePositive` from the actual Kraus representation. Completeness is not needed for this positivity bridge.

It does not assert Schur-Weyl duality, the paper's asymptotic conclusions, or its circuit-synthesis bounds.

Run `lake build SpectralProtocol`.