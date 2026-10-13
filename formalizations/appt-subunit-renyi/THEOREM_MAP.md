# Research proof → necessary lemmas → exact Lean coverage

| Research obligation | Exact endpoint | Scope |
|---|---|---|
| R8: positive half-kernel gap | `halfEntropyGap_lower` | Complete scalar inequality with exact radicals. |
| R10: rational comparator | `halfHeadPolynomial_nonneg`, `half_head_rational_comparison` | Complete continuum inequality; all seven rational cells checked by kernel identities. |
| R7: arbitrary head inequality | `halfEntropyHead_le_two` | Complete for every finite head, including β₁=1. |
| R6: physical shifted star and actual pivot | `density_appt_paper_halfEntropyHead` | Complete from actual density/all-unitary APPT, with signs and ordering discharged. |
| R18: downward spike SOS | `negative_joint_coordinate`, `negative_joint_signed` | Complete homogeneous inequalities, not assumed Schmidt data. |
| R17: all-unitary sufficiency | `negativeSpike_absolutelyPPT` | Complete on actual complex matrix orbit. |
| R19: finite density, rank, and purity | `negativeState_density`, `negativeState_appt`, `exists_negative_rank_state` | Complete actual states, finite rank construction and original purity. |
| Finite margin regression | `negative_even_physical_control`, `naiveNegative_not_appt` | Exact positive control and physical failure after deleting the reserve. |
| R3–R5 and R11–R15: arbitrary-order normalization and upper limit | No final endpoint | Complete written argument; not certified by half-order head alone. |
| R16: flat-family entropy lower limit | Companion mathematical Theorem F | Written input, not newly formalized here. |
| R20–R22: negative-outlier entropy lower limits | No final endpoint | Written argument; finite broad family formalized, full limits and negative high hierarchy not yet. |
| R1–R2: unrestricted sharp joint-growth law | No final endpoint | Complete mathematical proof, partial Lean coverage explicitly disclosed. |

All Lean declarations in the eight own modules are listed in `ROOTS.txt`.
The audit checks their actual transitive proof closure and only standard axioms;
it does not transform an unclosed row into a verified final theorem.
