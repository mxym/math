import GaussianRegularPrincipal
import GaussianPrincipalNondegeneracy
import GaussianCovarianceContinuity

/-! The actual segment from the regular covariance stays normalized, is
nondegenerate before its endpoint, and has the required singular-endpoint
continuity. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology Matrix.Norms.L2Operator
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

noncomputable def covarianceSegment (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (t : ℝ) :=
  (1-t) • regularCovariance (n+1) + t • Q

lemma covarianceSegment_zero (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    covarianceSegment Q 0 = regularCovariance (n+1) := by simp [covarianceSegment]

lemma covarianceSegment_one (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    covarianceSegment Q 1 = Q := by simp [covarianceSegment]

lemma covarianceSegment_posSemidef (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hQ : Q.PosSemidef) {t : ℝ} (ht : t ∈ Icc 0 1) : (covarianceSegment Q t).PosSemidef :=
  ((scoreGram_posSemidef (regularRows (n+1))).smul (sub_nonneg.mpr ht.2)).add (hQ.smul ht.1)

theorem covarianceSegment_principal_posDef (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hQ : Q.PosSemidef) {t : ℝ} (ht : t ∈ Ico 0 1) :
    (principalCovariance (covarianceSegment Q t)).PosDef := by
  have he : principalCovariance (covarianceSegment Q t) =
      (1-t) • principalCovariance (regularCovariance (n+1)) + t • principalCovariance Q := by
    ext i j
    rfl
  rw [he]
  exact (regular_principal_posDef.smul (sub_pos.mpr ht.2)).add_posSemidef
    ((hQ.submatrix Fin.succ).smul ht.1)

theorem covarianceSegment_normalized (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hQ : NormalizedCovariance Q) {t : ℝ} (ht : t ∈ Icc 0 1) :
    NormalizedCovariance (covarianceSegment Q t) := by
  have hk : 2 ≤ n+1 := by have hn := NeZero.pos n; omega
  have hr := regularCovariance_normalized (k := n+1) hk
  refine ⟨covarianceSegment_posSemidef Q hQ.1 ht,?_,?_⟩
  · intro i
    simp only [covarianceSegment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,← Finset.mul_sum,hr.2.1 i,hQ.2.1 i,mul_zero,add_zero]
  · simp only [covarianceSegment,Matrix.trace_add,Matrix.trace_smul,hr.2.2,hQ.2.2,mul_one]
    ring

theorem covarianceSegment_minimal_nondegenerate (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hQ : Q.PosSemidef) {t : ℝ} (ht : t ∈ Ico 0 1) :
    AffineIndependent ℝ (minimalCovarianceRows (covarianceSegment Q t)) :=
  minimalCovarianceRows_affineIndependent _ (covarianceSegment_principal_posDef Q hQ ht)

theorem covarianceSegment_value_endpoint_continuous
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hQ : Q.PosSemidef) :
    ContinuousWithinAt (fun t : ℝ => covarianceValue (covarianceSegment Q t)) (Iio 1) 1 := by
  have hp : Continuous (covarianceSegment Q) := by unfold covarianceSegment; fun_prop
  have hc : ContinuousOn (fun t : ℝ => covarianceValue (covarianceSegment Q t)) (Icc 0 1) :=
    continuousOn_covarianceValue.comp hp.continuousOn (fun t ht => covarianceSegment_posSemidef Q hQ ht)
  have hh := hc 1 (by norm_num : (1:ℝ) ∈ Icc 0 1)
  rw [continuousWithinAt_Icc_iff_Iic (by norm_num : (0:ℝ) < 1)] at hh
  exact hh.mono Iio_subset_Iic_self

end GaussianMeasureBridge
