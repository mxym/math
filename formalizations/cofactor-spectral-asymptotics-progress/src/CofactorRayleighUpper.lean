import CofactorScaledBinaryNorm
import CofactorEuclideanGram
import CofactorTargets

/-! Unconditional Rayleigh upper bounds for actual permanental first compounds. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem compound_feature_binary_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (v : Fin n → Fin n → ℂ) (hv : compound A = complexGram v)
    (s : Finset (Fin n)) :
    ‖∑ i ∈ s, gramFeature v i‖^2 ≤ A.permanent.re * s.card := by
  rw [gramFeature_sum_norm_sq,← hv]
  have h := compound_indicator_sum A hA s
  have hreal := (Complex.le_def.mp h).1
  simpa only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,sub_zero,
    mul_comm] using hreal

theorem compound_complex_quadratic_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hp : 0 < A.permanent.re) (w : Fin n → ℂ) :
    (∑ i, ∑ j, star (w i) * compound A i j * w j).re ≤
      4 * binaryNormConstant n * A.permanent.re * vectorNormSq w := by
  obtain ⟨v,hv⟩ := psd_exists_complexGram (compound A) (compound_psd A hA)
  have hs := Real.sq_sqrt hp.le
  have h := complex_scaled_binary_norm_bound (gramFeature v) w (Real.sqrt A.permanent.re)
    (Real.sqrt_pos.mpr hp) ?_
  · rw [gramFeature_weighted_norm_sq,← hv,hs] at h
    exact h
  · intro s
    rw [hs]
    exact compound_feature_binary_bound A hA v hv s

theorem compound_real_quadratic_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hp : 0 < A.permanent.re) (x : Fin n → ℝ) :
    (∑ i, ∑ j, (x i : ℂ) * compound A i j * (x j : ℂ)).re ≤
      2 * binaryNormConstant n * A.permanent.re * ∑ i, x i ^ 2 := by
  obtain ⟨v,hv⟩ := psd_exists_complexGram (compound A) (compound_psd A hA)
  have hs := Real.sq_sqrt hp.le
  have h := real_scaled_binary_norm_bound (gramFeature v) x (Real.sqrt A.permanent.re)
    (Real.sqrt_pos.mpr hp) ?_
  · rw [gramFeature_real_weighted_norm_sq,← hv,hs] at h
    exact h
  · intro s
    rw [hs]
    exact compound_feature_binary_bound A hA v hv s

theorem cofactorRayleighRatio_complex_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : psdAdmissible A) (w : Fin n → ℂ) (hw : 0 < vectorNormSq w) :
    cofactorRayleighRatio A w ≤ 4 * binaryNormConstant n := by
  unfold cofactorRayleighRatio
  rw [div_le_iff₀ (mul_pos hA.2 hw)]
  have h := compound_complex_quadratic_upper A hA.1 hA.2 w
  nlinarith

theorem cofactorRayleighRatio_real_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : psdAdmissible A) (x : Fin n → ℝ)
    (hx : 0 < vectorNormSq (fun i => (x i : ℂ))) :
    cofactorRayleighRatio A (fun i => (x i : ℂ)) ≤ 2 * binaryNormConstant n := by
  unfold cofactorRayleighRatio
  rw [div_le_iff₀ (mul_pos hA.2 hx)]
  have h := compound_real_quadratic_upper A hA.1 hA.2 x
  simpa only [Complex.star_def,Complex.conj_ofReal,vectorNormSq,Complex.normSq_ofReal,
    pow_two,mul_assoc] using h

theorem cofactorRayleighRatio_complex_harmonic_upper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : psdAdmissible A)
    (w : Fin n → ℂ) (hw : 0 < vectorNormSq w) :
    cofactorRayleighRatio A w ≤ 4 + (harmonic (n-1) : ℝ) := by
  have h := cofactorRayleighRatio_complex_upper A hA w hw
  have hc := binaryNormConstant_le_harmonic n
  linarith

theorem cofactorRayleighRatio_real_harmonic_upper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : psdAdmissible A)
    (x : Fin n → ℝ) (hx : 0 < vectorNormSq (fun i => (x i : ℂ))) :
    cofactorRayleighRatio A (fun i => (x i : ℂ)) ≤ 2 + (harmonic (n-1) : ℝ)/2 := by
  have h := cofactorRayleighRatio_real_upper A hA x hx
  have hc := binaryNormConstant_le_harmonic n
  linarith

end
end CofactorSpectral
