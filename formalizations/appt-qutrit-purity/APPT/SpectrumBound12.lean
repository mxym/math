import APPT.Finite12Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

theorem spectrum_bound_12 (lam : Fin 12 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (20 : ℝ)/196 := by
  let x : Fin 9 → Fin 12 := ![0, 1, 2, 6, 7, 8, 9, 10, 11]
  have hx : Function.Injective x := by decide +kernel
  have hAB := hC x hx
  have he : lam ∘ x = ![lam 0, lam 1, lam 2, lam 6, lam 7, lam 8, lam 9, lam 10, lam 11] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hAB
  exact APPT.Finite12.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
