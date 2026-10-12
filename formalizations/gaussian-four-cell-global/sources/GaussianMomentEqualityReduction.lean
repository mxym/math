import GaussianPerimeterRigidityReduction
import GaussianRegularFlux
import GaussianGramPrices
import GaussianFractionalEquality
import GaussianRegularDimension

/-! Equality and dimensional strictness for actual fractional partitions,
conditional only on the same explicitly named perimeter obligation. The
almost-everywhere classification uses the genuine zero-price winning cells. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e k : ℕ} [NeZero k]

lemma scaled_regular_gram_injective (hk : 2 ≤ k) (v : Fin k → Space e)
    (s : ℝ) (hs : 0 < s) (hg : scoreGram v = s • regularCovariance k) :
    Function.Injective v := by
  intro i j he
  by_contra hij
  have hh : scoreGram v i i = scoreGram v i j := by
    simp only [scoreGram]
    rw [he]
  rw [hg] at hh
  simp only [Matrix.smul_apply,smul_eq_mul,regularCovariance_apply,ite_true,
    if_neg hij] at hh
  have hn : ((k-1:ℕ):ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hf : s*((k-1:ℕ):ℝ)⁻¹ = 0 := by nlinarith [hh]
  exact mul_ne_zero hs.ne' hn hf

theorem moment_equality_regular_gram_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d) (F : FractionalPartition e (d+2))
    (hF : ∀ i,F.mass i = uniformMass (d+2) i)
    (he : F.momentEnergy = simplexConstant (d+2)^2) :
    scoreGram F.moment = simplexConstant (d+2)^2 • regularCovariance (d+2) := by
  have hcpos : 0 < simplexConstant (d+2) := simplexConstant_positive
  have hE : 0 < F.momentEnergy := by rw [he]; exact sq_pos_of_pos hcpos
  have hQ := F.normalizedMomentCovariance_mem hE
  have hb := (covariance_comparison_of_perimeter hper _ hQ).1
  have hv := F.momentEnergy_le_equalMassValue hF
  rw [F.equalMassValue_moment_normalize hE,he,Real.sqrt_sq hcpos.le] at hv
  have hvalue : covarianceValue F.normalizedMomentCovariance = simplexConstant (d+2) := by
    nlinarith [hcpos,hb,hv]
  have hreg := covariance_equality_regular_of_perimeter hper _ hQ hvalue
  have hbase : F.momentEnergy • F.normalizedMomentCovariance = scoreGram F.moment := by
    rw [FractionalPartition.normalizedMomentCovariance,smul_smul,mul_inv_cancel₀ hE.ne',one_smul]
  rw [he,hreg] at hbase
  exact hbase.symm

theorem moment_equality_ae_regular_winning_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d) (F : FractionalPartition e (d+2))
    (hF : ∀ i,F.mass i = uniformMass (d+2) i)
    (he : F.momentEnergy = simplexConstant (d+2)^2) :
    ∃ hv : Function.Injective F.moment,
      scoreGram F.moment = simplexConstant (d+2)^2 • regularCovariance (d+2) ∧
      ∀ᵐ x ∂gaussian e,∀ i,F.labels i x = (winningPartition F.moment 0 hv).labels i x := by
  have hg := moment_equality_regular_gram_of_perimeter hper F hF he
  have hc : 0 < simplexConstant (d+2) := simplexConstant_positive
  have hv := scaled_regular_gram_injective (by omega : 2 ≤ d+2) F.moment _ (sq_pos_of_pos hc) hg
  have hp := canonicalPrices_scaled_regular_gram (by omega : 2 ≤ d+2) F.moment hv _ hc.le hg
  refine ⟨hv,hg,fractional_dual_equality_ae_winning F.moment 0 hv F ?_⟩
  have hE : 0 < F.momentEnergy := by rw [he]; exact sq_pos_of_pos hc
  have hQ := F.normalizedMomentCovariance_mem hE
  have hvalue : covarianceValue F.normalizedMomentCovariance = simplexConstant (d+2) := by
    have hbase : F.normalizedMomentCovariance = regularCovariance (d+2) := by
      rw [FractionalPartition.normalizedMomentCovariance,hg,he,smul_smul,
        inv_mul_cancel₀ (sq_pos_of_pos hc).ne',one_smul]
    rw [hbase,covarianceValue_regular]
  calc
    partitionValue F.moment F = F.momentEnergy := by
      simp only [partitionValue,FractionalPartition.momentEnergy,real_inner_self_eq_norm_sq]
    _ = equalMassValue F.moment := by
      rw [F.equalMassValue_moment_normalize hE,he,Real.sqrt_sq hc.le,hvalue,pow_two]
    _ = priceObjective F.moment (fun i => F.mass i) 0 := by
      simp_rw [hF]
      rw [← hp,canonicalPrices_value]

theorem momentEnergy_strict_of_small_dimension
    (hper : EqualMassSimplicialPerimeterBound d) (F : FractionalPartition e (d+2))
    (hF : ∀ i,F.mass i = uniformMass (d+2) i) (he : e < d+1) :
    F.momentEnergy < simplexConstant (d+2)^2 := by
  apply lt_of_le_of_ne (momentEnergy_bound_of_perimeter hper F hF)
  intro heq
  have hg := moment_equality_regular_gram_of_perimeter hper F hF heq
  have hd := regular_gram_dimension_lower_bound F.moment _
    (sq_pos_of_pos simplexConstant_positive) hg
  omega

end GaussianMeasureBridge
