import APPT.Finite18Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

theorem spectrum_bound_18 (lam : Fin 18 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (26 : ℝ)/400 := by
  let x : Fin 9 → Fin 18 := ![0, 1, 2, 12, 13, 14, 15, 16, 17]
  have hx : Function.Injective x := by decide +kernel
  have hAB := hC x hx
  have he : lam ∘ x = ![lam 0, lam 1, lam 2, lam 12, lam 13, lam 14, lam 15, lam 16, lam 17] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hAB
  exact APPT.Finite18.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
