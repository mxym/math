import APPT.Finite24Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

/-- Finite spectral purity for all ordered 24-entry spectra under the actual
nine-corner A and B positive-semidefinite conditions. -/
theorem spectrum_bound_24 (lam : Fin 24 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (32 : ℝ)/676 := by
  let x : Fin 9 → Fin 24 := ![0, 1, 2, 18, 19, 20, 21, 22, 23]
  have hx : Function.Injective x := by decide +kernel
  have hAB := hC x hx
  have he : lam ∘ x = ![lam 0, lam 1, lam 2, lam 18, lam 19,
    lam 20, lam 21, lam 22, lam 23] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hAB
  exact APPT.Finite24.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
