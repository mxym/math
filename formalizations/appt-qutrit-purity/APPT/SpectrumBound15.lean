import APPT.Finite15Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

theorem spectrum_bound_15 (lam : Fin 15 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (23 : ℝ)/289 := by
  let x : Fin 9 → Fin 15 := ![0, 1, 2, 9, 10, 11, 12, 13, 14]
  have hx : Function.Injective x := by decide +kernel
  have hAB := hC x hx
  have he : lam ∘ x = ![lam 0, lam 1, lam 2, lam 9, lam 10, lam 11, lam 12, lam 13, lam 14] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hAB
  exact APPT.Finite15.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
