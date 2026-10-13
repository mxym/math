# Growing-order APPT Rényi theorem: proof and formalization map

Prepared 2026-10-14. The map was started before the high-order draft and updated
as the endpoint and profile statements were added. All objects are actual density
matrices on C^m tensor C^n, with partial-transpose positivity after every global
unitary. The new results are ordinary mathematical proofs. No new Lean module,
audit root, trusted input or source-bound kernel claim is made.

| Written statement | Necessary proved inputs and bridges | Actual Lean coverage of this new statement |
| --- | --- | --- |
| G1: all-aspect moment-excess/entropy law for α→∞, α=o(m) | Physical paired rearrangements; bounded exceptional square mass; O(1/m) middle spectrum; scalar Taylor bounds; explicit adaptive projection-plus-spike lower construction | Not formalized. The complete real-power objective, adaptive order/parameter limits and uniform quantifiers are new written work. |
| G2: bounded-aspect law for every α→∞, with no upper growth restriction | Actual second-largest eigenvalue gap; bounded total square mass; isolate the largest power; pure-spike witness | Not formalized. No old finite-order entropy audit is extended to α growing with dimension. |
| G3: bounded-aspect sharp moment and entropy near-minimizer criteria | Uniform actual-state largest-power reduction; exact logarithm; strict scalar comparison; physical shifted star to flatten the remaining spectrum | Not formalized. This is not the earlier fixed-order rigidity statement. |
| Z1: α→0 uniform all-aspect entropy law | Shifted star gives the least-value width cap; exact pivot centering after multiplying the kernel by α; endpoint convex scalar optimization; singular and adaptive negative-family lower states | Not formalized. This new zero-order window is not the fixed-order subunit theorem with limits exchanged. |
| Z2: finite (α log m, α n/m) near-minimizer classification | Uniform actual-state deficit identity; physical variance/least-value constraint; compactness with two critical branches | Not formalized. No old rigidity root or audit certifies these new moving-order limits. |
| U1–U2: every positive order uniformly in bounded aspect, and every sublinear order uniformly in all aspects | New endpoint windows G1–G3 and Z1–Z2; inherited fixed-order Φ law; finite-grid monotonicity/continuity on compact order intervals; subsequence assembly | Complete ordinary profile proof, not formalized. This combines ranges of the same APPT research direction rather than counting separate guesses. |
| S1: complete fixed-aspect spectral criteria on every limiting order, including both critical orders | Actual-state compact-order kernel Lipschitz estimate; inherited critical rigidity; strict mixed half/von-Neumann comparison; endpoint G3/Z1 identities | Written classification only. Source-bound audits keep their original roots; no new critical-order or moving-order coercivity claim is attributed to Lean. |
| M1: macroscopic high-order law for arbitrary aspect and order growth | Bounded exceptional mass; second-largest gap; O(1/m) actual middle interval; pure-spike lower witness | Written absolute-error theorem only. It does not claim the first nonzero equivalent in the unresolved α≈m/unrestricted-aspect window. |
| E1: exact finite entropy minimum and every equality state for 0<α≤1/(512D) | Two actual rank-two Schmidt witnesses; tail spread/variance estimate; uniform concave-power Taylor bound; actual singular APPT attainment | Complete ordinary finite proof, not formalized. The small explicit band is sufficient and is not claimed to be the sharp transition threshold. |
| Exceptional/bulk physical estimates | `SHARP_ASPECT_RATIO.md` Section 3 (A8), `ENTROPY_ASYMPTOTIC.md` Sections 2 and 4 (E7, E8, E17, E18), uniform-Schmidt interval witness | Their complete ordinary derivations are identified, with definitions rechecked. No additional statement is attributed to Lean merely from a package name. |
| Exact finite adaptive lower family | `ASYMPTOTIC.md` A1–A4 / `PROOF.md` joint construction; parameters are selected with H=ceil(sqrt(αm)); actual Schmidt SOS rederived in this manuscript | Complete ordinary all-unitary proof is included. Existing finite construction formalizations are not automatically claimed to cover the new adaptive-limit theorem. |
| Exact operator-norm cap and pure spike | Rank-two physical witness; `ENTROPY_ASYMPTOTIC.md` Section 13 (E44); all-unitary pure-projector partial transpose bound | Elementary existing mathematical endpoint, explicitly reproved where used. It is not presented as a newly discovered endpoint. |
| Exact auxiliary checks | Rational SOS specializations and a real 25×25 rational density whose partial transpose rejects a wrong protection coefficient; growing-order evaluation diagnostics | Python checks only, no Lean, no sampled-unitary sufficiency claim. These supplement rather than replace the universal proof. |
| Finite downward-spike lower family used in Z1 | Actual PSD density/rank/trace/purity/APPT construction with 0<H≤m and k<D | `APPTSubunit.exists_negative_rank_state` in NegativeState.lean and `negativeSpike_absolutelyPPT` in NegativeJoint.lean cover the original finite family under their exact hypotheses. The adaptive limits, objective and Z1/Z2 remain unformalized. |

The 8-module/39-root APPTSubunit audit still covers its original physical
half-order head and finite downward-spike family. The positive lacunary
companion verification retains its own fixed scope. Neither certificate
certifies G1–G3, their new manuscript, or the full APPT entropy optimization.
This map records those gaps rather than replacing them with assumptions.
