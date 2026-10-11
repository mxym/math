import Hydrology.Basic

namespace HydrologyIdentifiability

/-- The normalized residual obtained by substituting
`Q(t) = C (τ+t)^(-α)` into `Q'' + S Q' + P Q = 0` and multiplying by
`(τ+t)^(α+2) / C`. -/
def powerLawResidual (S P α τ t : ℝ) : ℝ :=
  α * (α + 1) - S * α * (τ + t) + P * (τ + t)^2

/-- A positive constant term rules out an exact power-law recession on an
interval: the normalized residual cannot vanish at every nonnegative time.
The proof uses only the three exact rational times `0,1,2`; no floating-point
argument or asymptotic approximation is involved. -/
theorem powerLawResidual_not_all_zero
    {S P α τ : ℝ} (hP : 0 < P) :
    ¬ (∀ t : ℝ, 0 ≤ t → powerLawResidual S P α τ t = 0) := by
  intro h
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  dsimp [powerLawResidual] at h0 h1 h2
  nlinarith

/-- The same obstruction with a nonzero amplitude: multiplying the residual by
the amplitude cannot make it vanish identically. -/
theorem nonzero_amplitude_powerLawResidual_not_all_zero
    {S P α τ C : ℝ} (hP : 0 < P) (hC : C ≠ 0) :
    ¬ (∀ t : ℝ, 0 ≤ t → C * powerLawResidual S P α τ t = 0) := by
  intro h
  apply powerLawResidual_not_all_zero hP
  intro t
  intro hnonneg
  have ht := h t hnonneg
  rcases mul_eq_zero.mp ht with ht | ht
  · exact (hC ht).elim
  · exact ht

end HydrologyIdentifiability
