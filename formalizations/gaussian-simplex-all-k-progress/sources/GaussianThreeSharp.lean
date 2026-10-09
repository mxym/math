import GaussianThreeGaussianWidth
import GaussianRegularPerimeter
import GaussianMomentEqualityReduction

/-!
An elementary, unconditional three-label Gaussian covariance comparison
independent of Milman--Neeman Gaussian multi-bubble perimeter minimization.

For three jointly centered Gaussian linear scores, the expected maximum is
a constant times the triangle perimeter. The RMS-trace normalization bounds
this perimeter sharply by an equilateral triangle. The optimized equal-mass
score value is bounded by the zero-price expected maximum.
-/

open MeasureTheory ProbabilityTheory Module Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

/-- The exact three-point quadratic identity in every Euclidean dimension. -/
theorem three_point_squared_distance_identity {e : ℕ}
    (a b c : Space e) :
    ‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2 + ‖a+b+c‖^2 =
       3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  rw [norm_sub_sq_real a b, norm_sub_sq_real a c,
    norm_sub_sq_real b c, norm_add_sq_real (a+b) c,
    norm_add_sq_real a b,inner_add_left]
  ring

/-- The trace of a score Gram matrix for three labels. -/
theorem scoreGram_three_trace {e : ℕ} (v : Fin 3 → Space e) :
    (scoreGram v).trace = ‖v 0‖^2+‖v 1‖^2+‖v 2‖^2 := by
  simp [scoreGram, Matrix.trace, Matrix.diag, real_inner_self_eq_norm_sq,
    Fin.sum_univ_succ, Fin.sum_univ_two, add_assoc]

/-- A trace-one three-score family has triangle edge-square sum at most 3.
There is no rank or centering hypothesis here. -/
theorem three_edge_square_sum_le_three {e : ℕ} (v : Fin 3 → Space e)
    (ht : (scoreGram v).trace = 1) :
    ‖v 0-v 1‖^2+‖v 0-v 2‖^2+‖v 1-v 2‖^2 ≤ 3 := by
  rw [scoreGram_three_trace] at ht
  have hh := three_point_squared_distance_identity (v 0) (v 1) (v 2)
  nlinarith [sq_nonneg ‖v 0+v 1+v 2‖]

/-- A dimension-free elementary upper bound on the three edge lengths. -/
theorem three_edge_length_sum_le_three {e : ℕ} (v : Fin 3 → Space e)
    (ht : (scoreGram v).trace = 1) :
    ‖v 0-v 1‖+‖v 0-v 2‖+‖v 1-v 2‖ ≤ 3 := by
  exact three_nonneg_sqrt_sum_le_three _ _ _
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (three_edge_square_sum_le_three v ht)

/-- At equal prescribed masses, zero prices give a valid explicit upper
bound for the genuine Gaussian optimal-price objective. -/
theorem equalMassValue_le_zero_price {e : ℕ} (v : Fin 3 → Space e) :
    equalMassValue v ≤ expectedScore v 0 := by
  have hh := balancedValue_le_objective v (uniformMass 3)
    (0 : Fin 3 → ℝ) uniformMass_pos sum_uniformMass
  simpa only [equalMassValue,priceObjective,Pi.zero_apply,mul_zero,
    Finset.sum_const_zero,add_zero] using hh

/-- The sharp 3-cell constant is three quarters of the first absolute
moment of a true N(0,1). It is derived from the regular model, not
introduced as an assumed numerical value. -/
theorem simplexConstant_three_abs :
    simplexConstant 3 = gaussianAbsOne/4*3 := by
  have hp := canonicalPrices_value (regularRows 3)
  rw [canonicalPrices_regular (k := 3) (by norm_num)] at hp
  simp only [priceObjective,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero] at hp
  have hv : equalMassValue (regularRows 3) = simplexConstant 3 := by
    rw [← covarianceValue_scoreGram]
    exact covarianceValue_regular
  have he (i j : Fin 3) (hij : i ≠ j) :
      ‖regularRows 3 i-regularRows 3 j‖=1 := by
    have hh := regular_gram_edge_squared
      (d := 1) (regularRows 3) (by rfl) i j hij
    norm_num at hh
    rcases hh with hh | hh
    · exact hh
    · have hn := norm_nonneg (regularRows 3 i-regularRows 3 j)
      linarith
  calc
    simplexConstant 3 = expectedScore (regularRows 3) 0 := (hp.trans hv).symm
    _ = gaussianAbsOne/4*
        (‖regularRows 3 0-regularRows 3 1‖+
         ‖regularRows 3 0-regularRows 3 2‖+
         ‖regularRows 3 1-regularRows 3 2‖) :=
      expectedScore_three_width _
    _ = gaussianAbsOne/4*3 := by
       rw [he 0 1 (by decide),he 0 2 (by decide),he 1 2 (by decide)]
       ring

/-- Unconditional sharp equal-mass three-label Gaussian score
comparison, in every ambient finite dimension, for every centered or
uncentered triple with trace-one Gram matrix. -/
theorem equalMassValue_three_trace_bound {e : ℕ} (v : Fin 3 → Space e)
    (ht : (scoreGram v).trace = 1) :
    equalMassValue v ≤ simplexConstant 3 := by
  calc
    equalMassValue v ≤ expectedScore v 0 := equalMassValue_le_zero_price v
    _ = gaussianAbsOne/4*
        (‖v 0-v 1‖+‖v 0-v 2‖+‖v 1-v 2‖) :=
      expectedScore_three_width v
    _ ≤ gaussianAbsOne/4*3 :=
      mul_le_mul_of_nonneg_left (three_edge_length_sum_le_three v ht)
        (div_nonneg gaussianAbsOne_nonneg (by norm_num))
    _ = simplexConstant 3 := simplexConstant_three_abs.symm

/-- The exact pinned normalized Gaussian covariance objective has the
unconditional k=3 sharp bound, including singular matrices. -/
theorem covarianceValue_three_le (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : NormalizedCovariance Q) :
    covarianceValue Q ≤ simplexConstant 3 := by
  rw [covarianceValue_eq_rows Q hQ.1]
  apply equalMassValue_three_trace_bound
  rw [scoreGram_covarianceRows Q hQ.1]
  exact hQ.2.2

/-- Full unconditional k=3 sharp moment-energy bound for actual
fractional equal-mass Gaussian partitions in any ambient dimension. -/
theorem three_cell_momentEnergy_bound {e : ℕ}
    (F : FractionalPartition e 3)
    (hF : ∀ i, F.mass i = uniformMass 3 i) :
    F.momentEnergy ≤ simplexConstant 3 ^ 2 := by
  exact F.momentEnergy_bound_of_normalized_covariance_bound hF
    (simplexConstant 3) simplexConstant_nonneg
    (fun Q hQ => covarianceValue_three_le Q hQ)

#print axioms simplexConstant_three_abs
#print axioms covarianceValue_three_le
#print axioms three_cell_momentEnergy_bound

end GaussianMeasureBridge
