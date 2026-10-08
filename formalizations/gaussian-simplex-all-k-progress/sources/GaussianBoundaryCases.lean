import GaussianRegularValue

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {k : ℕ} [NeZero k]

/-- Explicit identification of a_k with the maximum of k independent standard
normal coordinates under the product probability measure. -/
theorem expectedGaussianMaximum_product : expectedGaussianMaximum k =
    ∫ y : Fin k → ℝ,
      Finset.univ.sup' Finset.univ_nonempty (fun i => y i)
      ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1) := by
  unfold expectedGaussianMaximum gaussian
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (continuous_coordinateMax 0).aestronglyMeasurable]
  congr 1
  funext y
  simp [coordinateMax]

/-- The k=2 trace-one centered covariance domain is a singleton. Thus this
boundary case requires no multi-bubble comparison. -/
theorem normalizedCovariance_two_unique (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : NormalizedCovariance Q) : Q = regularCovariance 2 := by
  have h0 := hQ.2.1 0
  have h1 := hQ.2.1 1
  have ht := hQ.2.2
  have hsym : Q 0 1 = Q 1 0 := by simpa using hQ.1.isHermitian.apply 1 0
  simp only [Fin.sum_univ_two] at h0 h1
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at ht
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [regularCovariance_apply] <;> linarith

/-- Unconditional sharp-constant upper bound for the actual two-label
fractional Gaussian problem in every ambient dimension. -/
theorem two_cell_moment_bound {d : ℕ} (F : FractionalPartition d 2)
    (hF : ∀ i, F.mass i = uniformMass 2 i) :
    F.momentEnergy ≤ (expectedGaussianMaximum 2) ^ 2 := by
  have h := F.momentEnergy_bound_of_normalized_covariance_bound hF (simplexConstant 2)
    simplexConstant_nonneg (fun Q hQ => by
      rw [normalizedCovariance_two_unique Q hQ, covarianceValue_regular])
  simpa [simplexConstant] using h

/-- With one label the actual first moment is the Gaussian mean, hence zero. -/
theorem one_cell_moment_zero {d : ℕ} (F : FractionalPartition d 1) :
    F.moment (0 : Fin 1) = 0 := by simpa using F.sum_moment

theorem one_cell_momentEnergy_zero {d : ℕ} (F : FractionalPartition d 1) :
    F.momentEnergy = 0 := by
  simp [FractionalPartition.momentEnergy, one_cell_moment_zero]

end GaussianMeasureBridge
