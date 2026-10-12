import N200EndpointGap
import N200EntryBounds
import ConstantParameters
import N200RationalEntries

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder
open Set

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.N200

/-- The paper's specified rational shift and rational q0, with no negative
endpoint hypothesis or unverified numerical input. -/
theorem explicit_rational_counterexample :
    explicitMatrix.PosDef ∧
      (∃ i j, i ≠ j ∧ explicitMatrix i j ≠ 0) ∧
      (0 : ℝ) < (q0 : ℝ) ∧ (q0 : ℝ) < 1 ∧
      (intervalLength : ℝ) / 8 ≤
        (qPermanent explicitMatrix (q0 : ℂ)).re - (qPermanent explicitMatrix 1).re ∧
      (qPermanent explicitMatrix 1).re < (qPermanent explicitMatrix (q0 : ℂ)).re := by
  let V := twoColumnGram a b
  have hV : V * V.conjTranspose = N200.matrix := twoColumnGram_mul a b
  have hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ (1600 : ℝ) := by
    rw [hV]
    exact matrix_entry_norm_bound
  have hd := BapatBounds.dimension_at_least_three_bounds 200 (by norm_num)
    (1600 : ℝ) (by norm_num)
  have hneg : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ) := by
    rw [hV]
    exact matrix_endpoint_unit_gap
  have h := BapatBounds.gram_explicit_monotonicity_failure V (1600 : ℝ)
    (by norm_num) hA hneg hd.1 hd.2
  dsimp only at h
  rw [hV, ← gamma_cast, ← secondBound_cast, ← epsilon_cast,
    perturb_eq, ← q0_cast, ← intervalLength_cast] at h
  simpa only [explicitMatrix, qPermanent_eq, Complex.ofReal_one, q0_complex_cast] using h

theorem explicit_not_monotone :
    ¬MonotoneOn (fun q : ℝ => (qPermanent explicitMatrix (q : ℂ)).re) (Icc (-1) 1) := by
  obtain ⟨_, _, h0, h1, _, hreverse⟩ := explicit_rational_counterexample
  intro hm
  have hle := hm (show (q0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) h1.le
  have hle' : (qPermanent explicitMatrix (q0 : ℂ)).re ≤
      (qPermanent explicitMatrix 1).re := by
    simpa only [q0_complex_cast, Complex.ofReal_one] using hle
  exact (not_le_of_gt hreverse) hle'

/-- The explicit rational witness refutes the original strict conjecture. -/
theorem original_conjecture_false_from_explicit : ¬ OriginalBapatConjecture := by
  intro h
  have hp := explicit_rational_counterexample.1
  have hn : ¬ explicitMatrix.IsDiag := perturb_matrix_not_isDiag (epsilon : ℝ)
  exact explicit_not_monotone (h 200 explicitMatrix hp hn).monotoneOn

theorem explicit_qPermanent_real (q : ℝ) :
    qPermanent explicitMatrix (q : ℂ) =
      (((realQPolynomial explicitMatrix).eval q : ℝ) : ℂ) :=
  qPermanent_eq_ofReal_eval explicit_rational_counterexample.1.isHermitian q

end BapatExplicit
