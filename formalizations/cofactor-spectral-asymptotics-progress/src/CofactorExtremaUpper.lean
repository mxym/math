import CofactorRayleighUpper

/-! Uniform upper bounds for all six actual variational extrema. -/
set_option autoImplicit false
open scoped ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem real_sSup_le_nonneg (s : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hs : ∀ r ∈ s, r ≤ c) : sSup s ≤ c := by
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he,Real.sSup_empty]
    exact hc
  · exact csSup_le hn hs

theorem complexRayleighValues_bddAbove (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    BddAbove (complexRayleighValues n P) := by
  refine ⟨4 * binaryNormConstant n,?_⟩
  rintro r ⟨A,hA,w,hw,rfl⟩
  exact cofactorRayleighRatio_complex_upper A (hP A hA) w hw

theorem realRayleighValues_bddAbove (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    BddAbove (realRayleighValues n P) := by
  refine ⟨2 * binaryNormConstant n,?_⟩
  rintro r ⟨A,hA,x,hx,rfl⟩
  exact cofactorRayleighRatio_real_upper A (hP A hA) x hx

theorem complex_variational_sSup_upper (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    sSup (complexRayleighValues n P) ≤ 4 + (harmonic (n-1) : ℝ) := by
  have hc : 0 ≤ 4 + (harmonic (n-1) : ℝ) := by
    have h := binaryNormConstant_le_harmonic n
    have hn := binaryNormConstant_nonneg n
    linarith
  apply real_sSup_le_nonneg _ _ hc
  rintro r ⟨A,hA,w,hw,rfl⟩
  exact cofactorRayleighRatio_complex_harmonic_upper A (hP A hA) w hw

theorem real_variational_sSup_upper (n : ℕ)
    (P : Matrix (Fin n) (Fin n) ℂ → Prop) (hP : ∀ A, P A → psdAdmissible A) :
    sSup (realRayleighValues n P) ≤ 2 + (harmonic (n-1) : ℝ)/2 := by
  have hc : 0 ≤ 2 + (harmonic (n-1) : ℝ)/2 := by
    have h := binaryNormConstant_le_harmonic n
    have hn := binaryNormConstant_nonneg n
    linarith
  apply real_sSup_le_nonneg _ _ hc
  rintro r ⟨A,hA,x,hx,rfl⟩
  exact cofactorRayleighRatio_real_harmonic_upper A (hP A hA) x hx

theorem complexExtremum_upper (n : ℕ) :
    complexExtremum n ≤ 4 + (harmonic (n-1) : ℝ) :=
  complex_variational_sSup_upper n psdAdmissible (fun _ h => h)

theorem realExtremum_upper (n : ℕ) :
    realExtremum n ≤ 2 + (harmonic (n-1) : ℝ)/2 :=
  real_variational_sSup_upper n psdAdmissible (fun _ h => h)

theorem rankTwoComplexExtremum_upper (n : ℕ) :
    rankTwoComplexExtremum n ≤ 4 + (harmonic (n-1) : ℝ) :=
  complex_variational_sSup_upper n rankTwoCorrelationAdmissible (fun _ h => h.1)

theorem rankTwoRealExtremum_upper (n : ℕ) :
    rankTwoRealExtremum n ≤ 2 + (harmonic (n-1) : ℝ)/2 :=
  real_variational_sSup_upper n rankTwoCorrelationAdmissible (fun _ h => h.1)

theorem pdComplexExtremum_upper (n : ℕ) :
    pdComplexExtremum n ≤ 4 + (harmonic (n-1) : ℝ) :=
  complex_variational_sSup_upper n pdCorrelationAdmissible
    (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)

theorem pdRealExtremum_upper (n : ℕ) :
    pdRealExtremum n ≤ 2 + (harmonic (n-1) : ℝ)/2 :=
  real_variational_sSup_upper n pdCorrelationAdmissible
    (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)

end
end CofactorSpectral
