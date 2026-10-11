import Hydrology.Basic

namespace HydrologyIdentifiability

/-- The first four recession moments of two active parallel linear reservoirs.
The rates `l₁,l₂` are the positive decay rates and `w₁,w₂` are their output
weights. -/
def m0 (w₁ w₂ _l₁ _l₂ : ℝ) : ℝ := w₁ + w₂
def m1 (w₁ w₂ l₁ l₂ : ℝ) : ℝ := w₁ * l₁ + w₂ * l₂
def m2 (w₁ w₂ l₁ l₂ : ℝ) : ℝ := w₁ * l₁^2 + w₂ * l₂^2
def m3 (w₁ w₂ l₁ l₂ : ℝ) : ℝ := w₁ * l₁^3 + w₂ * l₂^3

/-- Two parallel exponentials satisfy the order-two recurrence determined by
the sum and product of their rates. -/
theorem parallel_recurrence (w₁ w₂ l₁ l₂ : ℝ) :
    m2 w₁ w₂ l₁ l₂ = (l₁ + l₂) * m1 w₁ w₂ l₁ l₂ -
      (l₁ * l₂) * m0 w₁ w₂ l₁ l₂ ∧
    m3 w₁ w₂ l₁ l₂ = (l₁ + l₂) * m2 w₁ w₂ l₁ l₂ -
      (l₁ * l₂) * m1 w₁ w₂ l₁ l₂ := by
  constructor <;> dsimp [m0, m1, m2, m3] <;> ring

/-- The Hankel determinant detects whether both rates and both weights are
active and distinct. -/
theorem parallel_hankel_determinant (w₁ w₂ l₁ l₂ : ℝ) :
    m0 w₁ w₂ l₁ l₂ * m2 w₁ w₂ l₁ l₂ -
      (m1 w₁ w₂ l₁ l₂)^2 = w₁ * w₂ * (l₁ - l₂)^2 := by
  dsimp [m0, m1, m2]
  ring

/-- Positive weights and distinct rates make the Hankel determinant nonzero. -/
theorem parallel_hankel_positive
    {w₁ w₂ l₁ l₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hrates : l₁ ≠ l₂) :
    0 < m0 w₁ w₂ l₁ l₂ * m2 w₁ w₂ l₁ l₂ -
      (m1 w₁ w₂ l₁ l₂)^2 := by
  rw [parallel_hankel_determinant]
  have hsq : 0 < (l₁ - l₂)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrates)
  positivity

/-- Each physical rate is a root of the recovered quadratic. -/
theorem parallel_rate_roots (l₁ l₂ : ℝ) :
    l₁^2 - (l₁ + l₂) * l₁ + l₁ * l₂ = 0 ∧
    l₂^2 - (l₁ + l₂) * l₂ + l₁ * l₂ = 0 := by
  constructor <;> ring

/-- Under a nonzero Hankel determinant, the first four moments uniquely recover
the recurrence coefficients `s=l₁+l₂` and `p=l₁l₂`. -/
theorem recurrence_coefficients_unique
    (μ₀ μ₁ μ₂ μ₃ s p s' p' : ℝ)
    (h₂ : μ₂ = s * μ₁ - p * μ₀)
    (h₃ : μ₃ = s * μ₂ - p * μ₁)
    (h₂' : μ₂ = s' * μ₁ - p' * μ₀)
    (h₃' : μ₃ = s' * μ₂ - p' * μ₁)
    (hD : μ₀ * μ₂ - μ₁^2 ≠ 0) :
    s = s' ∧ p = p' := by
  have hA : (s - s') * μ₁ - (p - p') * μ₀ = 0 := by
    linarith
  have hB : (s - s') * μ₂ - (p - p') * μ₁ = 0 := by
    linarith
  have hs : s - s' = 0 := by
    have hA' : (s - s') * μ₁ = (p - p') * μ₀ := by
      linarith [hA]
    have hB' : (s - s') * μ₂ = (p - p') * μ₁ := by
      linarith [hB]
    have hmul : (s - s') * (μ₁^2 - μ₀ * μ₂) = 0 := by
      calc
        (s - s') * (μ₁^2 - μ₀ * μ₂) =
            μ₁ * ((s - s') * μ₁) - μ₀ * ((s - s') * μ₂) := by ring
        _ = μ₁ * ((p - p') * μ₀) - μ₀ * ((p - p') * μ₁) := by rw [hA', hB']
        _ = 0 := by ring
    rcases mul_eq_zero.mp hmul with hs | hdet
    · exact hs
    · exact False.elim (hD (by linarith))
  have hp : p - p' = 0 := by
    by_cases hμ₀ : μ₀ = 0
    · have hμ₁ : μ₁ ≠ 0 := by
        intro hzero
        apply hD
        rw [hμ₀, hzero]
        ring
      have hB' : (s - s') * μ₂ = (p - p') * μ₁ := by
        linarith [hB]
      rw [hs] at hB'
      have hmul : (p - p') * μ₁ = 0 := by linarith [hB']
      exact (mul_eq_zero.mp hmul).resolve_right hμ₁
    · have hA' : (s - s') * μ₁ = (p - p') * μ₀ := by
        linarith [hA]
      rw [hs] at hA'
      have hmul : (p - p') * μ₀ = 0 := by linarith [hA']
      exact (mul_eq_zero.mp hmul).resolve_right hμ₀
  constructor <;> linarith

/-- Two genuinely active two-mode spectra with the same first four moments
have the same recovered sum and product of rates.  Thus the unordered rate
quadratic is identifiable before choosing an ordering of its roots. -/
theorem two_parallel_rate_coefficients_identifiable
    {w₁ w₂ v₁ v₂ l₁ l₂ m₁ m₂ : ℝ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hl : l₁ ≠ l₂) (hm : m₁ ≠ m₂)
    (h₀ : m0 w₁ w₂ l₁ l₂ = m0 v₁ v₂ m₁ m₂)
    (h₁ : m1 w₁ w₂ l₁ l₂ = m1 v₁ v₂ m₁ m₂)
    (h₂ : m2 w₁ w₂ l₁ l₂ = m2 v₁ v₂ m₁ m₂)
    (h₃ : m3 w₁ w₂ l₁ l₂ = m3 v₁ v₂ m₁ m₂) :
    l₁ + l₂ = m₁ + m₂ ∧ l₁ * l₂ = m₁ * m₂ := by
  have hD : m0 w₁ w₂ l₁ l₂ * m2 w₁ w₂ l₁ l₂ -
      (m1 w₁ w₂ l₁ l₂)^2 ≠ 0 := by
    rw [parallel_hankel_determinant]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hw₁) (ne_of_gt hw₂))
      (pow_ne_zero 2 (sub_ne_zero.mpr hl))
  have hrec := parallel_recurrence w₁ w₂ l₁ l₂
  have hrec' := parallel_recurrence v₁ v₂ m₁ m₂
  have hs := recurrence_coefficients_unique
    (m0 w₁ w₂ l₁ l₂) (m1 w₁ w₂ l₁ l₂) (m2 w₁ w₂ l₁ l₂)
    (m3 w₁ w₂ l₁ l₂) (l₁ + l₂) (l₁ * l₂) (m₁ + m₂) (m₁ * m₂)
    hrec.1 hrec.2
    (by simpa [h₀, h₁, h₂, h₃] using hrec'.1)
    (by simpa [h₀, h₁, h₂, h₃] using hrec'.2) hD
  exact hs

end HydrologyIdentifiability
