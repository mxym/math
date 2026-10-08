import GaussianRegularGramMoments
import GaussianCenteredAffineLift
import GaussianRegularPrincipal

/-! Actual first-order covariance stationarity at P/(k-1), in every
centered trace-zero matrix direction. Differentiable realization and the
regular moment formula are proved, not imposed as hypotheses. -/
open Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma sum_rows_zero_of_gram_centered {e k : ℕ} (v : Fin k → Space e)
    (hz : ∀ i, (∑ j,scoreGram v i j) = 0) : ∑ i,v i = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [sum_inner]
  simp only [inner_sum]
  change (∑ i,∑ j,scoreGram v i j) = 0
  simp only [hz,Finset.sum_const_zero]

theorem covarianceValue_regular_stationary
    (D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hD : D.IsHermitian) (hzD : ∀ i,(∑ j,D i j) = 0) (htD : D.trace = 0) :
    HasDerivAt (fun t : ℝ => covarianceValue (regularCovariance (d+2)+t•D)) 0 0 := by
  have hk : 2 ≤ d+2 := by omega
  have hR := regularCovariance_normalized (k := d+2) hk
  obtain ⟨v,h,hd,hv,hg,he⟩ := centered_affine_covariance_score_lift
    (regularCovariance (d+2)) D hR.1.isHermitian hD hR.2.1 hzD regular_principal_posDef
  have hz : ∑ i,v 0 i = 0 := sum_rows_zero_of_gram_centered _ (by simpa only [hg] using hR.2.1)
  have ht : (fun t => (scoreGram (v t)).trace) =ᶠ[𝓝 (0:ℝ)] (fun _ => 1) := by
    filter_upwards [he] with t ht
    rw [ht,Matrix.trace_add,Matrix.trace_smul,hR.2.2,htD]
    simp
  have ht0 := (hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq ht
  have hi := (trace_scoreGram_hasDerivAt v 0 h hd).unique ht0
  have hsum : (∑ i,⟪h i,v 0 i⟫) = 0 := by linarith
  have hc := equalMassValue_path_derivative v 0 h hv.injective hd
  simp_rw [balancedMoment_regular_gram (v 0) hv hz hg,real_inner_smul_right,
    ← Finset.mul_sum,hsum,mul_zero] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  rw [← ht,covarianceValue_scoreGram]

end GaussianMeasureBridge
