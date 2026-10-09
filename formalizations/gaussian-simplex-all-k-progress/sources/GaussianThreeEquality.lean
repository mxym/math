import GaussianThreeSharp
import GaussianRegularFanClassification

/-!
Complete equality and low-dimensional rigidity reductions for the true
three-label Gaussian first-moment problem, independent of the unproved
multi-bubble perimeter comparison. This module uses the direct triangle
Gaussian-width bound and the existing actual primal-dual equality theorem.
-/

open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

/-- Unconditional uniqueness of the regular covariance at equality in
the actual three-label optimized Gaussian value, including singular
centered trace-one covariances. -/
theorem covarianceValue_three_equality_regular
    (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : NormalizedCovariance Q)
    (heq : covarianceValue Q = simplexConstant 3) :
    Q = regularCovariance 3 := by
  let v : Fin 3 → Space 3 := covarianceRows Q
  have hg : scoreGram v = Q := scoreGram_covarianceRows Q hQ.1
  have ht : (scoreGram v).trace = 1 := by rw [hg]; exact hQ.2.2
  have hz : ∑ i, v i = 0 :=
    sum_rows_zero_of_gram_centered v (by simpa only [hg] using hQ.2.1)
  have hsum : v 0+v 1+v 2=0 := by
    have hh := hz
    simp only [Fin.sum_univ_succ,Fin.sum_univ_two] at hh
    simpa [add_assoc] using hh
  have htr : ‖v 0‖^2+‖v 1‖^2+‖v 2‖^2=1 := by
    simpa only [scoreGram_three_trace] using ht
  have hsquare : ‖v 0-v 1‖^2+‖v 0-v 2‖^2+‖v 1-v 2‖^2=3 := by
    have hcore := three_point_squared_distance_identity (v 0) (v 1) (v 2)
    rw [hsum,norm_zero] at hcore
    nlinarith [hcore,htr]
  have hv : equalMassValue v = simplexConstant 3 := by
    rw [← covarianceValue_eq_rows Q hQ.1]
    exact heq
  have hmax_bound : expectedScore v 0 ≤ simplexConstant 3 := by
    rw [expectedScore_three_width,simplexConstant_three_abs]
    exact mul_le_mul_of_nonneg_left
      (three_edge_length_sum_le_three v ht)
      (div_nonneg gaussianAbsOne_nonneg (by norm_num))
  have hmax_eq : expectedScore v 0 = simplexConstant 3 := by
    linarith [equalMassValue_le_zero_price v]
  have hcoeff_pos : 0 < gaussianAbsOne/4 := by
    have hp := simplexConstant_positive (d := 1)
    rw [simplexConstant_three_abs] at hp
    nlinarith
  have hedgesum : ‖v 0-v 1‖+‖v 0-v 2‖+‖v 1-v 2‖ = 3 := by
    apply (mul_left_cancel₀ hcoeff_pos.ne')
    calc
      gaussianAbsOne/4 *
        (‖v 0-v 1‖+‖v 0-v 2‖+‖v 1-v 2‖) =
          expectedScore v 0 := (expectedScore_three_width v).symm
      _ = simplexConstant 3 := hmax_eq
      _ = gaussianAbsOne/4*3 := simplexConstant_three_abs
  obtain ⟨h01,h12⟩ := three_nonneg_sqrt_sum_eq_three
    _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hsquare hedgesum
  have heedges (i j : Fin 3) (hij : i ≠ j) :
      ‖v i-v j‖^2=‖v 0-v 1‖^2 := by
    have hr01 : ‖v 1-v 0‖ = ‖v 0-v 1‖ := norm_sub_rev _ _
    have hr02 : ‖v 2-v 0‖ = ‖v 0-v 2‖ := norm_sub_rev _ _
    have hr12 : ‖v 2-v 1‖ = ‖v 1-v 2‖ := norm_sub_rev _ _
    fin_cases i <;> fin_cases j <;> simp_all [hr01, hr02, hr12]

  have hregular : scoreGram v = regularCovariance 3 :=
    equidistant_centered_gram_regular (by norm_num : 2 ≤ 3) v hz
      (by simpa [Fin.sum_univ_succ, add_assoc] using htr)
      (‖v 0-v 1‖^2) heedges
  exact hg.symm.trans hregular

/-- The actual three-label moment Gram is a positive scaling of the
regular covariance in every equality case. -/
theorem three_cell_moment_equality_regular_gram {e : ℕ}
    (F : FractionalPartition e 3)
    (hF : ∀ i, F.mass i = uniformMass 3 i)
    (he : F.momentEnergy = simplexConstant 3 ^ 2) :
    scoreGram F.moment = simplexConstant 3 ^ 2 • regularCovariance 3 := by
  have hcpos : 0 < simplexConstant 3 := simplexConstant_positive (d := 1)
  have hE : 0 < F.momentEnergy := by rw [he]; exact sq_pos_of_pos hcpos
  have hQ := F.normalizedMomentCovariance_mem hE
  have hb := covarianceValue_three_le F.normalizedMomentCovariance hQ
  have hv := F.momentEnergy_le_equalMassValue hF
  rw [F.equalMassValue_moment_normalize hE,he,Real.sqrt_sq hcpos.le] at hv
  have hvalue : covarianceValue F.normalizedMomentCovariance = simplexConstant 3 := by
    nlinarith [hcpos,hb,hv]
  have hreg := covarianceValue_three_equality_regular _ hQ hvalue
  have hbase : F.momentEnergy • F.normalizedMomentCovariance = scoreGram F.moment := by
    rw [FractionalPartition.normalizedMomentCovariance,smul_smul,
      mul_inv_cancel₀ hE.ne',one_smul]
  rw [he,hreg] at hbase
  exact hbase.symm

/-- The sharp three-cell equality cases are almost-everywhere exactly
the true regular-simplex winning partitions, in every ambient dimension. -/
theorem three_cell_energy_equality_iff_regular_fan {e : ℕ}
    (F : FractionalPartition e 3)
    (hF : ∀ i,F.mass i = uniformMass 3 i) :
    F.momentEnergy = simplexConstant 3 ^ 2 ↔
      IsRegularGaussianFan (d := 1) F := by
  constructor
  · intro he
    have hg := three_cell_moment_equality_regular_gram F hF he
    have hc : 0 < simplexConstant 3 := simplexConstant_positive (d := 1)
    let u : Fin 3 → Space e := (simplexConstant 3)⁻¹ • F.moment
    have hscale : simplexConstant 3 • u = F.moment := by
      simp [u,smul_smul,mul_inv_cancel₀ hc.ne']
    have hgu : scoreGram u = regularCovariance 3 := by
      change scoreGram ((simplexConstant 3)⁻¹ • F.moment) = _
      rw [scoreGram_smul,hg,smul_smul,inv_pow,
        inv_mul_cancel₀ (sq_pos_of_pos hc).ne',one_smul]
    have hu := regular_embedding_injective u hgu
    have hv := scaled_regular_gram_injective (by norm_num : 2 ≤ 3)
      F.moment _ (sq_pos_of_pos hc) hg
    have hp := canonicalPrices_scaled_regular_gram (by norm_num : 2 ≤ 3)
      F.moment hv _ hc.le hg
    have hE : 0 < F.momentEnergy := by rw [he]; exact sq_pos_of_pos hc
    have hQ := F.normalizedMomentCovariance_mem hE
    have hvalue : covarianceValue F.normalizedMomentCovariance = simplexConstant 3 := by
      have hbase : F.normalizedMomentCovariance = regularCovariance 3 := by
        rw [FractionalPartition.normalizedMomentCovariance,hg,he,smul_smul,
          inv_mul_cancel₀ (sq_pos_of_pos hc).ne',one_smul]
      rw [hbase,covarianceValue_regular]
    have hae : ∀ᵐ x ∂gaussian e, ∀ i,
        F.labels i x = (winningPartition F.moment 0 hv).labels i x := by
      apply fractional_dual_equality_ae_winning F.moment 0 hv F
      have heq : partitionValue F.moment F = F.momentEnergy := by
        simp only [partitionValue,FractionalPartition.momentEnergy,
          real_inner_self_eq_norm_sq]
      calc
        partitionValue F.moment F = F.momentEnergy := heq
        _ = equalMassValue F.moment := by
          rw [F.equalMassValue_moment_normalize hE,he,
            Real.sqrt_sq hc.le,hvalue,pow_two]
        _ = priceObjective F.moment (fun i => F.mass i) 0 := by
          simp_rw [hF]
          rw [← hp,canonicalPrices_value]
    refine ⟨u,hu,hgu,?_⟩
    filter_upwards [hae] with x hx
    intro i
    rw [hx i]
    have hcell : winningCell F.moment 0 i = winningCell u 0 i := by
      rw [← hscale,winningCell_positive_smul u _ hc]
    simp only [winningPartition,hcell]
  · exact regular_fan_attains F

/-- The three-label sharp upper bound is strict in ambient dimension 0
or 1, because the regular triangle Gram matrix has rank 2. -/
theorem three_cell_energy_strict_small_dimension {e : ℕ}
    (F : FractionalPartition e 3) (hF : ∀ i,F.mass i = uniformMass 3 i)
    (he : e < 2) :
    F.momentEnergy < simplexConstant 3^2 := by
  apply lt_of_le_of_ne (three_cell_momentEnergy_bound F hF)
  intro heq
  have hg := three_cell_moment_equality_regular_gram F hF heq
  have hd := regular_gram_dimension_lower_bound F.moment _
    (sq_pos_of_pos (simplexConstant_positive (d := 1))) hg
  omega

#print axioms covarianceValue_three_equality_regular
#print axioms three_cell_energy_equality_iff_regular_fan
#print axioms three_cell_energy_strict_small_dimension

end GaussianMeasureBridge
