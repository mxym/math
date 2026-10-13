# Quantum theorem → proof components → exact verification

| Component | Written proof | Lean / exact computation |
| --- | --- | --- |
| Original ECQC score and all-setting equality | PAPER §1–2; exact original min-of-p score | Not Lean |
| Holevo and necessary commuting-state equality | Published Holevo/Ruskai, explicitly cited | Not Lean, external theorem |
| Flat spectrum; complete-MUB rank-gap argument | PAPER §2 | Not Lean |
| Boundary saturation gives displaced parity on both marginals | PAPER §2, computational/Fourier/chirp rigidity | Not Lean |
| True projected MUB measurement → reduced monomial amplitude | PAPER §3 | Not Lean |
| Distinguished Fourier column forces diagonal scalar | PAPER §3 | `diagonal_rigidity_of_distinguished_column`; actual Fourier specialization remains analytic |
| Entire prime-field quadratic-residue reflection forces κ=0 and -1 square | PAPER §4 | `residue_reflection_forces_square_neg_one`, all prime p≥5 |
| Obstructed p≡3 mod4 congruence class | PAPER §4 | `no_residue_reflection_mod_four_three`, all prime p≥5 |
| Unique reduced amplitude and exceptional p=3 singlet | PAPER §4 | Two explicit finite residue-reflection kernel positive controls, not the quantum classification |
| Actual states, marginal spectra and all Born settings | PAPER §5, arbitrary prime analytic proof | Exact forty-five-state finite-prime checker, 329,660 probability entries |
| All p⁴ rays; all score values | PAPER §5 | Full arbitrary-prime claim is written proof; finite scores checked exactly |

The conditional Fourier hypothesis in the helper theorem is disclosed and
proved for the real quantum Fourier matrix in the written proof; it is not
silently promoted to an unconditional Lean quantum theorem.
