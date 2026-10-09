import APPT.Finite9Bound
import APPT.SpectralConditions
open scoped BigOperators
namespace APPT

theorem spectrum_bound_9 (lam : Fin 9 → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ (17 : ℝ)/121 := by
  have hAB := hC id Function.injective_id
  exact APPT.Finite9.arbitrary_spectrum_bound lam horder hpos hsum hAB.1 hAB.2

end APPT
