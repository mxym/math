import CofactorRingSubsetTail
import CofactorRingConstructionFin
import CofactorBinaryRayleighLower

/-! A fixed degree threshold gives actual complex and real rank-two Rayleigh lower witnesses. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem exists_ring_lower_threshold (C b δ η : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ : δ < 1) (hη : 0 < η)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ (n r K : ℕ) (d : Fin K → ℕ),
      0 < r → 0 < K → (∀ k, m ≤ d k) →
      (∀ i j, i < j → b*(d i : ℝ) ≤ (d j : ℝ)) →
      r+2*∑ k, d k = n+1 →
      (2*∑ k, d k : ℕ) ≤ δ*(n+1 : ℝ) →
      ∃ z : Fin (n+1) → ℂ,
        rankTwoCorrelationAdmissible (normalizedBinaryGram z) ∧
        0 < vectorNormSq z ∧ 0 < vectorNormSq (fun i => ((z i).im : ℂ)) ∧
        (K : ℝ)/(C*(1+η)) ≤ cofactorRayleighRatio (normalizedBinaryGram z) z ∧
        (K : ℝ)/(2*C*(1+η)) ≤
          cofactorRayleighRatio (normalizedBinaryGram z) (fun i => ((z i).im : ℂ)) := by
  let θ := entropyConstant b/(C*Real.exp 1*(1-δ))
  let q := θ^2
  have hθ0 : 0 < θ := div_pos (entropyConstant_pos b hb)
    (mul_pos (mul_pos hC (Real.exp_pos _)) (sub_pos.mpr hδ))
  have hq0 : 0 ≤ q := sq_nonneg θ
  have hq1 : q < 1 := by dsimp [q]; nlinarith
  obtain ⟨m,hm,hmtail⟩ := exists_small_ringTailBound q hq0 hq1 η hη
  refine ⟨m,hm,?_⟩
  intro n r K d hr hK hmin hsep hsize hfrac
  have hd : ∀ k, 2 ≤ d k := fun k => hm.trans (hmin k)
  have hd0 : ∀ k, 0 < d k := fun k => by have h := hd k; omega
  have hD : 2*∑ k, d k ≤ n+1 := by omega
  have hstrict : StrictMono d := by
    intro i j hij
    have hi : (0 : ℝ) < d i := by exact_mod_cast hd0 i
    have hh := hsep i j hij
    have hlt : (d i : ℝ) < d j := by nlinarith
    exact_mod_cast hlt
  let R := ringRadius (n+1) C d
  have hR : ∀ k, 0 < R k := by
    intro k
    have hk : (0 : ℝ) < d k := by exact_mod_cast hd0 k
    dsimp [R,ringRadius]
    positivity
  obtain ⟨z,hA,hsum,hsq,hNorm,hIm,hper⟩ :=
    exists_rankTwoCorrelation_ring_bound (n+1) r hr d hd hsize R hR ⟨0,hK⟩
  have hterm : ∀ k, ((2*d k : ℕ) : ℝ)*R k = (n+1 : ℝ)/C := by
    intro k
    dsimp [R,ringRadius]
    push_cast
    have hk : (d k : ℝ) ≠ 0 := by exact_mod_cast (hd0 k).ne'
    field_simp [hC.ne',hk]
    <;> ring
  have hiterm : ∀ k, (d k : ℝ)*R k = (n+1 : ℝ)/(2*C) := by
    intro k
    dsimp [R,ringRadius]
    push_cast
    have hk : (d k : ℝ) ≠ 0 := by exact_mod_cast (hd0 k).ne'
    field_simp [hC.ne',hk]
    <;> ring
  have hzn : vectorNormSq z = (n+1 : ℝ)*(K : ℝ)/C := by
    rw [hNorm]
    simp_rw [hterm]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hin : vectorNormSq (fun i => ((z i).im : ℂ)) = (n+1 : ℝ)*(K : ℝ)/(2*C) := by
    rw [hIm]
    simp_rw [hiterm]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hzp : 0 < vectorNormSq z := by rw [hzn]; positivity
  have hip : 0 < vectorNormSq (fun i => ((z i).im : ℂ)) := by rw [hin]; positivity
  have htail := ring_subset_sum_le_one_add_tail (n+1) (by omega) C b δ hC hb hδ hθ
    d hd0 hsep hD (by simpa only [Nat.cast_add,Nat.cast_one] using hfrac) m hmin hstrict.injective
  have hsumBound : (∑ s : Finset (Fin K), (ringAmplitude d R s)^2/
      ((n+1).choose (2*∑ k ∈ s, d k) : ℝ)) ≤ 1+η := by
    apply htail.trans
    change 1+ringTailBound q m ≤ 1+η
    linarith
  have hp : (normalizedBinaryGram z).permanent.re ≤
      ((n+1).factorial : ℝ)*(binaryGamma z)^2*(1+η) :=
    hper.trans (mul_le_mul_of_nonneg_left hsumBound
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have hc := normalizedBinaryGram_complex_test_lower z (1+η) (by linarith) hzp hp
  have hi := normalizedBinaryGram_real_test_lower z (1+η) (by linarith) hsq hip hp
  rw [hzn] at hc
  rw [hin] at hi
  have hNr : (n+1 : ℝ) ≠ 0 := by positivity
  have hcEq : ((n+1 : ℝ)*(K : ℝ)/C)/((n+1 : ℝ)*(1+η)) = (K : ℝ)/(C*(1+η)) := by
    field_simp
  have hiEq : ((n+1 : ℝ)*(K : ℝ)/(2*C))/((n+1 : ℝ)*(1+η)) = (K : ℝ)/(2*C*(1+η)) := by
    field_simp
  rw [hcEq] at hc
  rw [hiEq] at hi
  exact ⟨z,hA,hzp,hip,hc,hi⟩

end
end CofactorSpectral
