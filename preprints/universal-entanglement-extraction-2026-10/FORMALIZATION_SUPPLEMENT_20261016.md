# Lean formalization supplement, 2026-10-16

This supplements the frozen 21-page manuscript *The finite-block cost of
universality in entanglement extraction*. It does not replace its eight TeX
files, PDF, previous source ZIP, or the dated original theorem/source map.
The manuscript is **not fully formalized**.

The new combined scope is
[`formalizations/extraction-connections`](../../formalizations/extraction-connections/README.md).
It contains **608 explicitly listed roots**, **237 bound source/configuration
inputs**, and **31 same-type forged-proof rejection controls**. These are roots
including necessary lemmas, not 608 distinct original research results. Existing
39/91/235/444 and 83/11 scopes are unchanged. An additional 4,299 older files are
checked for byte preservation; this does not audit all their mathematical claims.
Completed-run evidence and exact closure statistics are in `VERIFICATION_CONNECTIONS.json`.
Historical component audits describe their own exact commits; their dependency
counts must not be added together.

| Manuscript topic | Current actual Lean endpoint | Exact boundary |
| --- | --- | --- |
| Lemma 2.1, Lemma 2.2 | Original 83-root physical core and 11-root local cap | Frozen; actual finite matrix/channel hypotheses and integer packing retained |
| Proposition 2.3 | `MinimaxProfile.physical_finite_ensemble_bound`, `common_support_profile_protocol`, `actual_minimax_finite_bounds` | Finite physical ensemble averaging and minimax synthesis; no asserted Haar identity |
| Theorem 2.4, spectral envelope | `SpectralProtocol.oneShotSpectralEnvelope_actual_lower`, `oneShotSpectralEnvelope_actual_upper` | Original-space unitary and actual complete local lower channel; actual arbitrary PPT upper; derived spectral selections, quarter loss and harmonic factor |
| Universal construction and first-order laws | `MinimaxProfile.universal_compression_protocol`, `universal_subcritical_rate` | One input-independent family with retained complete product-local witnesses; actual integer floors, orbit support, iid density and type count; fixed dimensions and admissible target sequence |
| Gaussian law | `MinimaxProfile.universal_gaussian_limit`; `KrausPPTProtocol.tensor_gaussian_converse` | Full pointwise fidelity limit for each fixed actual input of positive varentropy; both local target caps are essential, including boundary sequences |
| Entropy strong converse | `MinimaxProfile.KrausPPTProtocol.tensor_rate_strong_converse`; `ExtractionSpectrum.kraus_tensor_rate_strong_converse` | Every actual finite-Kraus PPT sequence above the entropy threshold; a complete two-sided local-cap capacity classification is not asserted here |
| Variational and type estimates | `ExtractionSpectrum.nonnegative_escort_renyi_variational_identity`, `density_strict_direct_renyi_variational_identity`, `optimized_escort_typical_subsets` and type/direct modules | Actual eigenvalue laws, positive-support reductions, attained variational values and constructed subsets; no supplied LLN/CLT/Sanov or large-deviation certificate |
| Theorems 5.1–5.2: pure balanced subcase | `MinimaxProfile.balanced_pure_target_uniform_minimax` | Entire unknown pure-iid continuum and supremum over all positive integer targets for each fixed balanced local dimension; actual symmetric rank and adversarial average are internal |
| General rank promise | `ExtractionRankSupport.rankBudgetSpace_eq_densityTensorSpace`, `rankBudgetProjector_log_rank_per_copy_limit` | Intrinsic minimum common support, actual projector and exponential rank rate; not the sharp Schur polynomial constant or Haar second moment |
| Corollary 5.4 and integer Bell claims | `SpectralProtocol.fixedSpectrum_iid_integerBell_actual_extractor`, `fixedSpectrum_iid_integerBell_optimal`, `rankBounded_iid_integerBell_optimal_all_blocklength`, and real-floor/first-order theorems | **Two-qubit one-copy inputs**; every actual fixed spectrum and its unknown-basis unitary orbit, all blocklengths including zero; intrinsic rank retained. No general-dimension Weyl formula or flat-spectrum fixed-error profile is substituted |
| Common sector decoding | `SpectralProtocol.exists_common_multisector_decoder`, `finite_multisector_uniform_baseline_lower` | One actual joint unitary and two complete local channels, cross-sector coherence removed and reset baseline proved; no efficient gate list |
| Literal Bell pairs | `SpectralProtocol.bellPairTensor_eq_bellProjector` | Matrix identity for the target; no synthesis/circuit-cost result follows from it |

The universal compressor uses the established polynomial orbit-span mechanism
from universal quantum compression, already credited to Jozsa and coauthors in
the manuscript. It provides an independently proved route to the fixed-dimension
first- and second-order limits. It does not identify the manuscript's individual
Schur blocks or reproduce their sharper finite-block constants.

The lower protocol class is one arbitrary global preprocessing unitary followed
by two complete local channels. `IsProductLocal` includes actual local Kraus
witnesses and equality of their product action with the chosen postprocessing
channel. The upper class retains actual Kraus representations for the channel
and its partial-transpose conjugate. Equivalence with an arbitrary abstract CP
map presentation has not been formally connected.

The tensor input uses a fixed dimension-preserving coordinate bijection. Lower
and upper bounds use the identical actual matrix. A literal standard copywise
Alice/Bob coordinate identity and its fixed permutation bridge are not asserted
by these declarations. No gate complexity bound is certified by an abstract
unitary or coordinate equivalence.

The important remaining formalization work is:

1. The actual Schur unitary/direct sum, Weyl/hook dimensions and character laws,
   and singular-input block identities.
2. General-rank sharp support asymptotics and Haar average second moments,
   including inverse-moment uniform integrability and the resulting sharp
   target-uniform minimax constant for intermediate ranks.
3. Operational matching fidelity exponents, the full high-rate local-cap branch,
   strict reliability inverses, and fixed-error Gaussian quantile inversion.
4. Explicit finite-block Berry--Esseen constants and growing-dimension conditions.
5. Ancilla-free gate lists, effective angles, gate counts and approximation error.
6. A single protocol family combining the sharp pure minimax guarantee with all
   mixed-input laws, plus the abstract CP/Kraus and canonical-coordinate bridges.

The independent probability subagent reviewed the universal connections and
identified the local-witness quantifier issue, which was repaired before source
freeze. Its review is documented in `extraction-connections/REVIEW.md`. This is
internal AI review, not external human peer review or a novelty certification.
No new journal submission, aiXiv submission, release or DOI was made for this
formalization supplement.
