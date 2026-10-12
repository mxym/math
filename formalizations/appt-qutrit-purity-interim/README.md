# Qutrit-qudit APPT purity: interim formalization package

This interim package publishes the written proof, exact rational certificate data, and the finite-dimensional Lean support completed so far. It is a reviewable checkpoint, not a claim of a complete Lean formalization.

## Mathematical scope

The written proof states the qutrit-qudit (`3 × n`) purity formula for `n ≥ 3`: `(3n+8)/(3n+2)^2` for `3 ≤ n ≤ 8`, and `3/(8n)` for `n ≥ 9`. The six finite certificate JSON files and the uniform parameter certificate are exact rational data checked by the included independent Python verifiers.

## Lean scope at this checkpoint

`APPT.Core` supplies the explicit real matrices and PSD consequences. `Finite9`, `Finite12`, `Finite15`, `Finite18`, `Finite21`, and `Finite24` compile with exact certificate identities and nonnegativity proofs. The included `FiniteSpectrumGaps` and `Finite*Bound` modules independently bridge arbitrary sorted, nonnegative, normalized finite spectra to the corresponding certificate bounds for dimensions `9, 12, 15, 18, 21, 24` (the `n=3..8` branch). These bridges explicitly assume the displayed A/B matrices are PSD. They do not identify those assumptions with APPT, and they do not provide the full quantum semantic theorem.

`Uniform.lean`, `UniformBridge.lean`, and `OrderedSpectrum.lean` are included as source for the next stage. The uniform all-`n≥9` Lean certificate and its bridge are **pending** at this checkpoint: the giant 1,635-term expression did not produce an `.olean` within the recorded single-thread attempts. The full APPT/Hildebrand spectral criterion connection, quantum orbit arguments, and final all-`n` Lean theorem are also **pending**.

## Reproduction

Use Lean 4.34.1 with Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, one thread and a `12288` MiB memory threshold. Compile the finite modules in dependency order. The `verification/compilation` records contain commands, source hashes, stdout and stderr. `verification/source-status.json` records this checkpoint's boundaries.

No novelty, priority, external peer review, APPT semantic equivalence, or complete formalization claim is made by this interim Release. A later immutable Release may add the closed uniform and quantum interfaces without modifying this checkpoint.
