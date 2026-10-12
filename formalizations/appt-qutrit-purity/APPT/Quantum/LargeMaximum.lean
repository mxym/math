import APPT.Quantum.SpectralMoments
import APPT.Quantum.Attainment
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

/-- State-level upper bound, with no unresolved A/B or diagonalization hypotheses. -/
theorem appt_purity_upper_large (n : ℕ) (hn : 9 ≤ n)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (hA : IsDensity A) (hAPPT : AbsolutelyPPT A) :
    purity A ≤ 3/(8*(n : ℝ)) := by
  let lam := sortedSpectrum n A hA.1.1
  have hn3 : 3 ≤ n := by omega
  have h := spectrum_bound_large (by omega : 27 ≤ 3*n) lam
    (sortedSpectrum_antitone n A hA.1.1) (sortedSpectrum_nonneg n A hA.1)
    (sortedSpectrum_sum_one n A hA) (sortedSpectrum_cornerConditions n hn3 A hA.1.1 hAPPT)
  have hd : (9 : ℝ)/(8*((3*n : ℕ) : ℝ)) = 3/(8*(n : ℝ)) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    push_cast
    field_simp [hnR]
    <;> ring
  rw [hd] at h
  rw [purity_eq_sortedSpectrum n A hA.1.1]
  exact h

/-- Complete maximal-purity statement for every qutrit–qudit system with n≥9. -/
theorem appt_purity_maximum_large (n : ℕ) (hn : 9 ≤ n) :
    (∀ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A → AbsolutelyPPT A → purity A ≤ 3/(8*(n : ℝ))) ∧
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ AbsolutelyPPT A ∧ purity A = 3/(8*(n : ℝ)) := by
  constructor
  · exact fun A hA h => appt_purity_upper_large n hn A hA h
  · have hn0 : 0 < n := by omega
    exact ⟨longState n, longState_isDensity n hn0, longState_absolutelyPPT n,
      longState_purity n hn0⟩

end APPT.Quantum
