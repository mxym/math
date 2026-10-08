import GaussianCovarianceDifferential
import GaussianCovarianceStationarity
import GaussianCovarianceSegment

/-! Actual radial differential identities, including the trace-one regular
starting point and every nonsingular interior covariance. -/
open Module Matrix Set Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d e k : ℕ} [NeZero k]

lemma facetLaplacian_trace_gram (v m : Fin k → Space e)
    (w : Fin k → Fin k → ℝ) (hf : ∀ i,m i = ∑ j,w i j • (v i-v j)) :
    (facetLaplacian w*scoreGram v).trace = ∑ i,⟪v i,m i⟫ := by
  rw [facetLaplacian_trace_mul]
  simp only [hf,inner_sum,real_inner_smul_right,inner_sub_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change w i j*(⟪v i,v i⟫-⟪v j,v i⟫) = w i j*(⟪v i,v i⟫-⟪v i,v j⟫)
  rw [real_inner_comm (v i) (v j)]

lemma facetLaplacian_trace_regular (w : Fin k → Fin k → ℝ)
    (hw : ∀ i,w i i = 0) :
    (facetLaplacian w*regularCovariance k).trace =
      fluxTrace w / ((k-1:ℕ):ℝ) := by
  rw [facetLaplacian_trace_mul]
  have hs (i j : Fin k) :
      w i j*(regularCovariance k i i-regularCovariance k j i) =
        ((k-1:ℕ):ℝ)⁻¹*w i j := by
    by_cases hij : i=j
    · subst j; simp [hw i]
    · rw [regularCovariance_apply,regularCovariance_apply]
      simp only [ite_true,if_neg (Ne.symm hij)]
      ring
  simp only [hs,← Finset.mul_sum,fluxTrace]
  rw [div_eq_mul_inv,mul_comm]

theorem covarianceSegment_stationary
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q) :
    HasDerivAt (fun t : ℝ => covarianceValue (covarianceSegment Q t)) 0 0 := by
  have hR := regularCovariance_normalized (k := d+2) (by omega)
  have hz (i : Fin (d+2)) : (∑ j,(Q-regularCovariance (d+2)) i j) = 0 := by
    simp only [Matrix.sub_apply,Finset.sum_sub_distrib,hQ.2.1 i,hR.2.1 i,sub_self]
  have ht : (Q-regularCovariance (d+2)).trace = 0 := by
    rw [Matrix.trace_sub,hQ.2.2,hR.2.2,sub_self]
  have hc := covarianceValue_regular_stationary (Q-regularCovariance (d+2))
    (hQ.1.isHermitian.sub hR.1.isHermitian) hz ht
  convert hc using 1
  funext t
  congr 1
  ext i j
  simp only [covarianceSegment,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem actual_covarianceSegment_radial_differential
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (t : ℝ) (ht : t ∈ Ioo 0 1) :
    ∃ r : Fin (d+2) → Space (d+1), ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = covarianceSegment Q t ∧
      (∀ i,w i i = 0) ∧ (∀ i j,i ≠ j → 0 < w i j) ∧
      (∀ i j,w i j = w j i) ∧
      (∀ i,balancedMoment r i = ∑ j,w i j • (r i-r j)) ∧
      HasDerivAt (fun s : ℝ => covarianceValue (covarianceSegment Q s))
        ((facetLaplacian w*(Q-regularCovariance (d+2))).trace/2) t ∧
      t*((facetLaplacian w*(Q-regularCovariance (d+2))).trace/2) =
        (covarianceValue (covarianceSegment Q t)-fluxTrace w/(d+1:ℕ))/2 := by
  have hR := regularCovariance_normalized (k := d+2) (by omega)
  have hQt := covarianceSegment_normalized Q hQ ⟨ht.1.le,ht.2.le⟩
  have hz (i : Fin (d+2)) : (∑ j,(Q-regularCovariance (d+2)) i j) = 0 := by
    simp only [Matrix.sub_apply,Finset.sum_sub_distrib,hQ.2.1 i,hR.2.1 i,sub_self]
  obtain ⟨r,w,hr,hg,hw,hp,hs,hf,hc,hd⟩ := actual_centered_covariance_differential
    (covarianceSegment Q t) (Q-regularCovariance (d+2)) hQt.1.isHermitian
    (hQ.1.isHermitian.sub hR.1.isHermitian) hQt.2.1 hz
    (covarianceSegment_principal_posDef Q hQ.1 ⟨ht.1.le,ht.2⟩)
  refine ⟨r,w,hr,hg,hw,hp,hs,hf,?_,?_⟩
  · have hd' : HasDerivAt
        (fun s : ℝ => covarianceValue (covarianceSegment Q t+s•(Q-regularCovariance (d+2))))
        ((facetLaplacian w*(Q-regularCovariance (d+2))).trace/2) (t-t) := by
        simpa only [sub_self] using hd
    have hinner : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
    convert hd'.comp t (h := fun s : ℝ => s-t) hinner using 1
    · funext s
      congr 1
      ext i j
      simp only [covarianceSegment,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      ring
    · ring
  · have he : t • (Q-regularCovariance (d+2)) =
        covarianceSegment Q t-regularCovariance (d+2) := by
      ext i j
      simp only [covarianceSegment,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      ring
    have hvalue : (facetLaplacian w*covarianceSegment Q t).trace =
        covarianceValue (covarianceSegment Q t) := by
      rw [← hg,facetLaplacian_trace_gram r _ w hf,covarianceValue_scoreGram]
      exact balancedMoment_value r hr.injective
    have htr : t*(facetLaplacian w*(Q-regularCovariance (d+2))).trace =
        covarianceValue (covarianceSegment Q t)-fluxTrace w/(d+1:ℕ) := by
      calc
        _ = (facetLaplacian w*(t•(Q-regularCovariance (d+2)))).trace := by
          rw [Matrix.mul_smul,Matrix.trace_smul]; rfl
        _ = (facetLaplacian w*(covarianceSegment Q t-regularCovariance (d+2))).trace := by rw [he]
        _ = _ := by
          rw [Matrix.mul_sub,Matrix.trace_sub,hvalue,facetLaplacian_trace_regular w hw]
          simp only [show d+2-1=d+1 by omega]
    linarith

end GaussianMeasureBridge
