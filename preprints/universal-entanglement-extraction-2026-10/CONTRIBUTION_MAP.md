# Contribution and prior-work map

The resource is one global entangling unitary on the existing input register,
followed by deterministic local/LOCC/completely-PPT channels. Fidelity means
overlap with the normalized Bell projector. This resource convention is essential
to every comparison below.

| Component | What this paper proves | Attribution and limits |
| --- | --- | --- |
| Finite spectral method, Section 2 | Deterministic variable-size Bell packing, coherent common-support construction, spectral envelope and a support-versus-average comparison | Rains fidelity effects and the quadratic entropy converse are prior inputs; the actual constructions and physical finite bounds have separate Lean endpoints |
| Pointwise universal laws, Sections 3–4 | One physical state-independent family matches state-aware capacity, all-rate fidelity exponent, strict-direct reliability and a nondegenerate entropy-limited Gaussian threshold | Consolidates the author's two preserved extraction predecessors. Universal compression, Schur methods, classical source coding and CLT are established methods |
| Dimension-explicit finite block control, Theorem 3.1 and Corollary 3.2 | An all-blocklength information-spectrum sandwich with explicit representation/dimension overhead; quantitative Gaussian error and sufficient triangular-array hypotheses | No uncontrolled joint dimension/copy limit; no claim at the local cap or zero-varentropy boundary |
| Two moments of an unknown support, Theorem 5.1 | An explicit constant for the common Schur support and asymptotic equality of its dimension with the inverse purity of the Haar-averaged flat-rank input | Schur--Weyl theory, Weyl dimensions and averaging identities are standard. The reciprocal-moment tail is controlled, not replaced by typicality alone |
| Target-uniform minimax, Theorem 5.2 and Corollary 5.3 | One rank-budget protocol and an adversarial average match relatively for every target integer; exact leading constant, logarithmic target-size cost and the n=ms cap transition | Rank budget s is known; spectrum and support are unknown. D and s are fixed before k grows. General nonuniform known spectra receive the exact-extraction corollary only |
| Pure-promise circuit, Proposition 5.5 | Optimal integer Bell pairs from unknown two-qubit pure iid inputs; effective original-register implementation with no supplied memory | Symmetric compression and streaming concentration are prior work. The new claim is the matched extraction/resource accounting in the present model, not discovery of symmetric compression or the best possible gate count |
| APPT application, Section 6.1 | Capacity as half the entropy deficit, capped by log m; explicit purity-based comparison and APPT example | Direct application, not a separate novelty claim. Companion APPT purity and entropy results keep their own scopes |

The bibliography explicitly credits Rains; Keyl–Werner; Jozsa et al.;
Matsumoto–Hayashi; Hayashi; the 2026 universal coding/distillation and work papers;
Kondra et al.; Lami; symmetric-compression and circuit-synthesis predecessors.
Recent-paper comparisons are bounded literature checks, not exhaustive priority
certificates. Internal AI review does not substitute for external human review.
