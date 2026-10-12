import BapatWedgeContraction

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section

theorem exteriorCoefficient_unit (u w : EuclideanSpace ℂ (Fin 4))
    (hu : ‖u‖=1) (hw : ‖w‖=1) (huw : inner ℂ u w=0) :
    (∑ p ∈ originalPairs (ι := Fin 4), ‖exteriorCoefficient u w p.1 p.2‖^2)=1 := by
  have huu : (∑ a, u a*conj (u a))=1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
    rw [hu] at h
    simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.ofReal_one,Complex.ofReal_one,one_pow,mul_comm] using h
  have hww : (∑ a, w a*conj (w a))=1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
    rw [hw] at h
    simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.ofReal_one,Complex.ofReal_one,one_pow,mul_comm] using h
  have hwu : inner ℂ w u=0 := by rw [← inner_conj_symm,huw]; simp
  have h₁ : (∑ a, u a*conj (w a))=0 := by
    simpa [PiLp.inner_apply,RCLike.inner_apply,mul_comm] using hwu
  have h₂ : (∑ a, w a*conj (u a))=0 := by
    simpa [PiLp.inner_apply,RCLike.inner_apply,mul_comm] using huw
  have h := dot_minor_eq_wedges (fun a => u a) (fun a => w a)
    (fun a => conj (u a)) (fun a => conj (w a))
  rw [huu,hww,h₁,h₂] at h
  apply Complex.ofReal_injective
  push_cast
  simp only [one_mul,zero_mul,sub_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (exteriorCoefficient u w p.1 p.2)*conj (exteriorCoefficient u w p.1 p.2)=
      (‖exteriorCoefficient u w p.1 p.2‖:ℂ)^2 := Complex.mul_conj' _
  rw [← he]
  simp [exteriorCoefficient,map_sub,map_mul]

theorem transverseComplex4_norm : ‖transverseComplex4‖=1 := by
  have h := complex_four_norm_sq transverseComplex4
  simp only [transverseComplex4,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.head_fin_const,norm_zero,norm_mul,Complex.norm_I,
    one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at h
  norm_num only [zero_pow (by omega : 2≠0),Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)] at h
  change ‖transverseComplex4‖^2=1 at h
  nlinarith [norm_nonneg transverseComplex4]

theorem canonical_transverse_inner (t : ℝ) : inner ℂ (canonicalComplex4 t) transverseComplex4=0 := by
  simp [PiLp.inner_apply,RCLike.inner_apply,canonicalComplex4,transverseComplex4,Fin.sum_univ_succ]

theorem canonical_exteriorCoefficient_unit {t : ℝ} (ht : 0≤t) (ht' : t≤1) :
    (∑ p ∈ originalPairs (ι := Fin 4),
      ‖exteriorCoefficient (canonicalComplex4 t) transverseComplex4 p.1 p.2‖^2)=1 :=
  exteriorCoefficient_unit _ _ (canonicalComplex4_norm ht ht') transverseComplex4_norm
    (canonical_transverse_inner t)

end
end BapatRealExistence
