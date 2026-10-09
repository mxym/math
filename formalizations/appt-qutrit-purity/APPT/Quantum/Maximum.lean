import APPT.Quantum.SmallMaximum
import APPT.Quantum.LargeMaximum
import APPT.Quantum.SpectralNecessity

open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

/-- The full upper bound for every actual qutrit-qudit APPT density matrix. -/
theorem appt_purity_upper (n : ℕ) (hn : 3 ≤ n)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (hA : IsDensity A) (hP : AbsolutelyPPT A) :
    purity A ≤ targetPurity n := by
  by_cases h8 : n ≤ 8
  · simpa only [targetPurity, if_pos h8] using appt_purity_upper_small n hn h8 A hA hP
  · have h9 : 9 ≤ n := by omega
    simpa only [targetPurity, if_neg h8] using appt_purity_upper_large n h9 A hA hP

/-- Sharp upper bound and an actual attaining APPT density matrix, for all n >= 3.
There are no unresolved spectral, PSD-corner or quantum-bridge assumptions. -/
theorem appt_purity_maximum (n : ℕ) (hn : 3 ≤ n) :
    (∀ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A → AbsolutelyPPT A → purity A ≤ targetPurity n) ∧
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ AbsolutelyPPT A ∧ purity A = targetPurity n :=
  ⟨fun A hA hP => appt_purity_upper n hn A hA hP, targetPurity_attained n hn⟩

/-- Actual purities of the physical APPT density matrices. -/
def attainablePurities (n : ℕ) : Set ℝ :=
  {p | ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
    IsDensity A ∧ AbsolutelyPPT A ∧ purity A = p}

/-- The displayed piecewise formula is a maximum, not merely a supremum bound. -/
theorem targetPurity_isGreatest (n : ℕ) (hn : 3 ≤ n) :
    IsGreatest (attainablePurities n) (targetPurity n) := by
  constructor
  · exact targetPurity_attained n hn
  · rintro p ⟨A,hA,hP,rfl⟩
    exact appt_purity_upper n hn A hA hP

theorem appt_purity_maximum_formula (n : ℕ) (hn : 3 ≤ n) :
    IsGreatest (attainablePurities n)
      (if n ≤ 8 then (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 else 3/(8*(n : ℝ))) :=
  targetPurity_isGreatest n hn

end APPT.Quantum
