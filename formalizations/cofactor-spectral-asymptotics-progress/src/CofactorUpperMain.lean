import CofactorLogarithmicUpper

/-! Largest eigenvalues and the six asymptotic upper conclusions for the target classes. -/
set_option autoImplicit false
open scoped ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem compound_largest_eigenvalue_upper {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : psdAdmissible A) :
    (compound_psd A hA.1).isHermitian.eigenvalues₀ ⟨0,by simpa using hn⟩ /
      A.permanent.re ≤ 4 + (harmonic (n-1) : ℝ) := by
  let z : Fin (Fintype.card (Fin n)) := ⟨0,by simpa using hn⟩
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := compound_eigenvalue_harmonic_upper A hA (e z)
  simpa only [Matrix.IsHermitian.eigenvalues,e,z,Equiv.symm_apply_apply] using h

theorem realCompound_largest_eigenvalue_upper {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : psdAdmissible A) :
    (realCompound_isHermitian A hA.1).eigenvalues₀ ⟨0,by simpa using hn⟩ /
      A.permanent.re ≤ 2 + (harmonic (n-1) : ℝ)/2 := by
  let z : Fin (Fintype.card (Fin n)) := ⟨0,by simpa using hn⟩
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := realCompound_eigenvalue_harmonic_upper A hA (e z)
  simpa only [Matrix.IsHermitian.eigenvalues,e,z,Equiv.symm_apply_apply] using h

theorem complexExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, complexExtremum n / Real.log n ≤ 1 + ε :=
  complex_variational_eventual_log_upper (fun _ => psdAdmissible) (fun _ _ h => h) ε hε

theorem realExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, realExtremum n / Real.log n ≤ 1/2 + ε :=
  real_variational_eventual_log_upper (fun _ => psdAdmissible) (fun _ _ h => h) ε hε

theorem rankTwoComplexExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, rankTwoComplexExtremum n / Real.log n ≤ 1 + ε :=
  complex_variational_eventual_log_upper (fun _ => rankTwoCorrelationAdmissible)
    (fun _ _ h => h.1) ε hε

theorem rankTwoRealExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, rankTwoRealExtremum n / Real.log n ≤ 1/2 + ε :=
  real_variational_eventual_log_upper (fun _ => rankTwoCorrelationAdmissible)
    (fun _ _ h => h.1) ε hε

theorem pdComplexExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, pdComplexExtremum n / Real.log n ≤ 1 + ε :=
  complex_variational_eventual_log_upper (fun _ => pdCorrelationAdmissible)
    (fun _ _ h => ⟨h.1.posSemidef,h.2.1⟩) ε hε

theorem pdRealExtremum_eventual_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, pdRealExtremum n / Real.log n ≤ 1/2 + ε :=
  real_variational_eventual_log_upper (fun _ => pdCorrelationAdmissible)
    (fun _ _ h => ⟨h.1.posSemidef,h.2.1⟩) ε hε

end
end CofactorSpectral
