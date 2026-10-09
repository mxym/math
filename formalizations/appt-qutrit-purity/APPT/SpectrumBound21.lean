import APPT.Finite21Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

theorem spectrum_bound_21 (lam : Fin 21 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (29 : ℝ)/529 := by
  let x : Fin 9 → Fin 21 := ![0, 1, 2, 15, 16, 17, 18, 19, 20]
  have hx : Function.Injective x := by decide +kernel
  have hAB := hC x hx
  have he : lam ∘ x = ![lam 0, lam 1, lam 2, lam 15, lam 16, lam 17, lam 18, lam 19, lam 20] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hAB
  exact APPT.Finite21.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
