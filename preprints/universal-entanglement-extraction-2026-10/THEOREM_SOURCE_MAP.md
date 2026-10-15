# Theorem-to-source and verification correspondence

The authoritative final statements are the eight TeX files and their bound PDF.
Author research details live in `research/submission-protocol-depth-20261016/`;
the current versions are `PAPER-v4.md`, `ADDENDUM_FIXED_SPECTRUM-v2.md`, and
`ADDENDUM_PURE_CIRCUIT-v3.md`. Older versions preserve real revision history.

| Manuscript | Source | Exact verification boundary |
| --- | --- | --- |
| Lemma 2.1, Rains and collision/local caps | `spectral-principles.tex`; core `Extraction/KrausRains.lean`, `RainsBudget.lean`, `OverlapConverse.lean`; extension `LocalCap/ActualCap.lean` | Actual Kraus completeness and positivity of the partial-transpose-conjugated map imply actual effect bounds; no caller-supplied quadratic budget |
| Lemma 2.2, coherent packing | `spectral-principles.tex`; `Extraction/FiniteFidelity.lean` | `Extraction.finite_projection_fidelity_extractor`: one original-space U and two complete local Kraus families before every actual density supported in P; exact d/K overlap under the integer floor rank condition |
| Proposition 2.3, support/average comparison | `spectral-principles.tex` | Its finite physical lower code and pointwise upper envelope are Lean-certified. Ensemble averaging and minimax synthesis are ordinary mathematical arguments |
| Full finite upper envelope | `LocalCap/ActualCap.lean` | `ExtractionLocalCap.kraus_target_overlap_full_envelope`: every actual density, every initial U, and every actual channel satisfying the stated positivity condition have overlap at most min{1,a/K,sqrt(ab Tr(rho²))/K} |
| Theorem 2.4, spectral envelope | `spectral-principles.tex`; predecessor `research/global-unitary-ppt-extraction/PROOF.md` | Ordinary spectral grouping/Hölder proof; not a new full Lean endpoint |
| Theorem 3.1, Corollary 3.2 | `universal-protocol.tex`; author `PAPER-v4.md` | Ordinary Schur identification, multiplicity truncation, information-spectrum and Berry–Esseen proof |
| Theorems 4.1–4.2 | `asymptotic-laws.tex`; two preserved extraction predecessors | Ordinary type/variational, reliability and Gaussian arguments, with the exact boundary restrictions in the statements |
| Theorems 5.1–5.2, Corollary 5.3 | `unknown-support.tex`; author `PAPER-v4.md` | Ordinary Haar/character identities, two-moment asymptotics, floor packing and target-uniform minimax proof |
| Corollary 5.4 | `unknown-support.tex`; `ADDENDUM_FIXED_SPECTRUM-v2.md` | Ordinary support-orbit argument; arbitrary positive spectra receive the same zero-error law, not the flat-spectrum fixed-error profile |
| Proposition 5.5 and Section 5.4 | `unknown-support.tex`; `ADDENDUM_PURE_CIRCUIT-v3.md` | Ordinary effective compression/completion, gate synthesis, integer optimality and all-state compatibility arguments |
| Section 6.1 | `applications-verification.tex`; separate APPT sources cited in the bibliography | Ordinary capacity application. The older APPT audits are unchanged and are not rerun or enlarged by this manuscript |

The formal packages quantify finite Kraus representations. The converse
equivalence between abstract finite-dimensional CP maps and Kraus forms is a
standard mathematical input, not formalized here. The converse only needs a
necessary positivity property of completely PPT channels, which suffices for
the manuscript's upper bounds.

The 83-root core and 11-root cap extension have different source bindings and
overlapping dependency closures. Their closure counts must not be added as a
count of distinct verified declarations. Old 39/91/235/444 audits retain their
original literal inputs, roots and meanings.
