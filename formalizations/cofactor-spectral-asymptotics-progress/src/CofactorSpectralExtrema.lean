import CofactorLargestEigenvalue

/-! Cofinality proves equality between the largest-eigenvalue and Rayleigh extrema.
Dimension zero has empty value sets in both formulations. -/
set_option autoImplicit false
open scoped ComplexOrder
namespace CofactorSpectral
noncomputable section

def complexSpectralValues (N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → Prop) : Set ℝ :=
  {r | ∃ hn : 0 < N, ∃ A : Matrix (Fin N) (Fin N) ℂ, ∃ hA : psdAdmissible A,
    P A ∧ r = largestCompoundRatio hn A hA}

def realSpectralValues (N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → Prop) : Set ℝ :=
  {r | ∃ hn : 0 < N, ∃ A : Matrix (Fin N) (Fin N) ℂ, ∃ hA : psdAdmissible A,
    P A ∧ r = largestRealCompoundRatio hn A hA}

theorem vectorNormSq_pos_dimension {N : ℕ} (w : Fin N → ℂ) (hw : 0 < vectorNormSq w) : 0 < N := by
  cases N with
  | zero => simp [vectorNormSq] at hw
  | succ n => omega

theorem complex_spectral_extremum_eq_variational (N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → Prop)
    (hP : ∀ A, P A → psdAdmissible A) :
    sSup (complexSpectralValues N P) = sSup (complexRayleighValues N P) := by
  symm
  apply csSup_eq_csSup_of_forall_exists_le
  · intro r hr
    obtain ⟨A,hPA,w,hw,rfl⟩ := hr
    have hn := vectorNormSq_pos_dimension w hw
    exact ⟨largestCompoundRatio hn A (hP A hPA),⟨hn,A,hP A hPA,hPA,rfl⟩,
      complexRayleigh_le_largestCompoundRatio hn A (hP A hPA) w hw⟩
  · intro r hr
    obtain ⟨hn,A,hA,hPA,rfl⟩ := hr
    obtain ⟨w,hw,he⟩ := largestCompoundRatio_attained hn A hA
    exact ⟨cofactorRayleighRatio A w,⟨A,hPA,w,hw,rfl⟩,he.ge⟩

theorem real_spectral_extremum_eq_variational (N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → Prop)
    (hP : ∀ A, P A → psdAdmissible A) :
    sSup (realSpectralValues N P) = sSup (realRayleighValues N P) := by
  symm
  apply csSup_eq_csSup_of_forall_exists_le
  · intro r hr
    obtain ⟨A,hPA,w,hw,rfl⟩ := hr
    have hn := vectorNormSq_pos_dimension (fun i => (w i : ℂ)) hw
    exact ⟨largestRealCompoundRatio hn A (hP A hPA),⟨hn,A,hP A hPA,hPA,rfl⟩,
      realRayleigh_le_largestRealCompoundRatio hn A (hP A hPA) w hw⟩
  · intro r hr
    obtain ⟨hn,A,hA,hPA,rfl⟩ := hr
    obtain ⟨w,hw,he⟩ := largestRealCompoundRatio_attained hn A hA
    exact ⟨cofactorRayleighRatio A (fun i => (w i : ℂ)),⟨A,hPA,w,hw,rfl⟩,he.ge⟩

def complexSpectralExtremum (N : ℕ) : ℝ := sSup (complexSpectralValues N psdAdmissible)
def realSpectralExtremum (N : ℕ) : ℝ := sSup (realSpectralValues N psdAdmissible)
def rankTwoComplexSpectralExtremum (N : ℕ) : ℝ := sSup (complexSpectralValues N rankTwoCorrelationAdmissible)
def rankTwoRealSpectralExtremum (N : ℕ) : ℝ := sSup (realSpectralValues N rankTwoCorrelationAdmissible)
def pdComplexSpectralExtremum (N : ℕ) : ℝ := sSup (complexSpectralValues N pdCorrelationAdmissible)
def pdRealSpectralExtremum (N : ℕ) : ℝ := sSup (realSpectralValues N pdCorrelationAdmissible)

theorem complexSpectralExtremum_eq (N : ℕ) : complexSpectralExtremum N = complexExtremum N :=
  complex_spectral_extremum_eq_variational N _ (fun _ h => h)
theorem realSpectralExtremum_eq (N : ℕ) : realSpectralExtremum N = realExtremum N :=
  real_spectral_extremum_eq_variational N _ (fun _ h => h)
theorem rankTwoComplexSpectralExtremum_eq (N : ℕ) : rankTwoComplexSpectralExtremum N = rankTwoComplexExtremum N :=
  complex_spectral_extremum_eq_variational N _ (fun _ h => h.1)
theorem rankTwoRealSpectralExtremum_eq (N : ℕ) : rankTwoRealSpectralExtremum N = rankTwoRealExtremum N :=
  real_spectral_extremum_eq_variational N _ (fun _ h => h.1)
theorem pdComplexSpectralExtremum_eq (N : ℕ) : pdComplexSpectralExtremum N = pdComplexExtremum N :=
  complex_spectral_extremum_eq_variational N _ (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)
theorem pdRealSpectralExtremum_eq (N : ℕ) : pdRealSpectralExtremum N = pdRealExtremum N :=
  real_spectral_extremum_eq_variational N _ (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)

end
end CofactorSpectral
