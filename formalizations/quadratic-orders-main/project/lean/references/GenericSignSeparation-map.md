# Generic signed separation: source-to-interface map

Source: `upstream-028/GaussianMoat/SignedGeometry.lean`, OpenAI family 028,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Entry 002 v3 §§2–3.
Implementation: `Entry002/GenericSignSeparation.lean`, namespace
`Entry002.SignSeparation`.

The domain is any additive group `L` with an actual `Basis (Fin 2) ℤ L` and
an actual full linear planar embedding `e`. The arithmetic input is the existing
`ArithmeticInterface data b e`; all selected maps are its genuine maps to `ZMod p`.
`MainTarget`, `FiniteSieveTarget`, `IsPrimitive`, and the arithmetic interface
are unchanged.

| Upstream proof | Generic replacement | Proof inputs |
| --- | --- | --- |
| Primitive signed-factor mean | `lineLog_mean_eq` | A2 paired-kernel exclusion already proved for actual primitive vectors |
| Eligible logarithmic mass | `eligible_log_bound`, `separationConstant_spec` | Actual A4 eligible prime product and monotonicity of real log |
| `lineLog_tail` | `lineLog_tail` | The existing independently proved fair-sign Hoeffding inequality |
| `line_witness_log_lower` | `line_witness_log_lower` | Genuine coefficient-line witness and actual planar length lower bound |
| `line_event_tail` | `exists_uniform_line_event_tail` | One constant from A4; primitive directions; actual bounded-region kernel witnesses |
| Cube/sign equivalence and measure | `cubeSignEquiv_dist`, `cubeSignEquiv_measure` | Finite cube bijection; exact product fair-coin measure |
| Witness-line partition | `badLine_primitive`, `badSign_iff_class` | Integral gcd primitive extraction and genuine coefficient determinant |
| `lineClasses_separated` | `lineClasses_separated` | Actual common-kernel determinant divisibility and prime product |
| `signed_region_bound` | `signed_region_bound`, `signed_region_exp_bound` | Derived line-event tails; separated Boolean-cube packing; explicit scalar inequalities |
| Rectangle geometry | `rectangle_length_bound`, `planarCellDet_orientation` | Actual Euclidean norm; actual lattice cell determinant; linear isometry |
| `signed_rectangle` | `signed_rectangle_scaled`, `signed_rectangle` | Dyadic prime bounds; actual rectangle area and A4 scale; exact scalar exponent/growth lemmas |

The strongest rectangle theorem proves
`Pr[∃ nonzero w in rectangle, all selected kernels kill w] ≤ exp(−d³r/5120)`.
Its assumptions are `5 ≤ T`, `T ≤ p ≤ 2T`, `1 ≤ W ≤ R`, `0 < d < 1/4`,
`1000 ≤ d³r`, and
`max(2/covolume, sqrt(2)*sqrt(A4Constant))*R*W ≤ P^(1−d)`.
The scale is independent of the rectangle orientation; `P` is the exact selected
prime product and `r` is its cardinality. No probability result, fake complex norm,
or Gaussian-specific factorization is assumed. A3 and A5 are retained in the
existing interface but this module uses its A2/A4 fields plus the genuine signed
residue data. Prime supply/A5-to-batch asymptotics and the final entropy synthesis
remain separate work, not conclusions of this module.

Validation: official Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Build and axiom logs:
`logs/GenericSignSeparation-build.log`, `logs/GenericSignSeparation-axioms.log`.
