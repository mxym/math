import Hydrology.Basic

namespace HydrologyIdentifiability

/-- The first six moments of three parallel exponential recession modes. -/
def n0 (w₁ w₂ w₃ _l₁ _l₂ _l₃ : ℝ) : ℝ := w₁ + w₂ + w₃
def n1 (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) : ℝ :=
  w₁ * l₁ + w₂ * l₂ + w₃ * l₃
def n2 (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) : ℝ :=
  w₁ * l₁^2 + w₂ * l₂^2 + w₃ * l₃^2
def n3 (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) : ℝ :=
  w₁ * l₁^3 + w₂ * l₂^3 + w₃ * l₃^3
def n4 (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) : ℝ :=
  w₁ * l₁^4 + w₂ * l₂^4 + w₃ * l₃^4
def n5 (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) : ℝ :=
  w₁ * l₁^5 + w₂ * l₂^5 + w₃ * l₃^5

def e1 (l₁ l₂ l₃ : ℝ) : ℝ := l₁ + l₂ + l₃
def e2 (l₁ l₂ l₃ : ℝ) : ℝ := l₁ * l₂ + l₁ * l₃ + l₂ * l₃
def e3 (l₁ l₂ l₃ : ℝ) : ℝ := l₁ * l₂ * l₃

/-- Three parallel modes satisfy the recurrence of their characteristic cubic. -/
theorem three_parallel_recurrence (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) :
    n3 w₁ w₂ w₃ l₁ l₂ l₃ =
        e1 l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ -
          e2 l₁ l₂ l₃ * n1 w₁ w₂ w₃ l₁ l₂ l₃ +
            e3 l₁ l₂ l₃ * n0 w₁ w₂ w₃ l₁ l₂ l₃ ∧
    n4 w₁ w₂ w₃ l₁ l₂ l₃ =
        e1 l₁ l₂ l₃ * n3 w₁ w₂ w₃ l₁ l₂ l₃ -
          e2 l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ +
            e3 l₁ l₂ l₃ * n1 w₁ w₂ w₃ l₁ l₂ l₃ ∧
    n5 w₁ w₂ w₃ l₁ l₂ l₃ =
        e1 l₁ l₂ l₃ * n4 w₁ w₂ w₃ l₁ l₂ l₃ -
          e2 l₁ l₂ l₃ * n3 w₁ w₂ w₃ l₁ l₂ l₃ +
            e3 l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ := by
  constructor
  · dsimp [n0, n1, n2, n3, e1, e2, e3]
    ring
  constructor
  · dsimp [n1, n2, n3, n4, e1, e2, e3]
    ring
  · dsimp [n2, n3, n4, n5, e1, e2, e3]
    ring

/-- The order-three Hankel determinant is a weighted Vandermonde square. -/
theorem three_parallel_hankel_determinant
    (w₁ w₂ w₃ l₁ l₂ l₃ : ℝ) :
    n0 w₁ w₂ w₃ l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ *
          n4 w₁ w₂ w₃ l₁ l₂ l₃ +
        2 * n1 w₁ w₂ w₃ l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ *
          n3 w₁ w₂ w₃ l₁ l₂ l₃ -
        n0 w₁ w₂ w₃ l₁ l₂ l₃ *
          (n3 w₁ w₂ w₃ l₁ l₂ l₃)^2 -
        (n1 w₁ w₂ w₃ l₁ l₂ l₃)^2 * n4 w₁ w₂ w₃ l₁ l₂ l₃ -
        (n2 w₁ w₂ w₃ l₁ l₂ l₃)^3 =
      w₁ * w₂ * w₃ * (l₁ - l₂)^2 * (l₁ - l₃)^2 * (l₂ - l₃)^2 := by
  dsimp [n0, n1, n2, n3, n4]
  ring

/-- Positive weights and pairwise distinct rates make the order-three Hankel
determinant strictly positive. -/
theorem three_parallel_hankel_positive
    {w₁ w₂ w₃ l₁ l₂ l₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hw₃ : 0 < w₃) (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃)
    (h23 : l₂ ≠ l₃) :
    0 < n0 w₁ w₂ w₃ l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ *
          n4 w₁ w₂ w₃ l₁ l₂ l₃ +
        2 * n1 w₁ w₂ w₃ l₁ l₂ l₃ * n2 w₁ w₂ w₃ l₁ l₂ l₃ *
          n3 w₁ w₂ w₃ l₁ l₂ l₃ -
        n0 w₁ w₂ w₃ l₁ l₂ l₃ *
          (n3 w₁ w₂ w₃ l₁ l₂ l₃)^2 -
        (n1 w₁ w₂ w₃ l₁ l₂ l₃)^2 * n4 w₁ w₂ w₃ l₁ l₂ l₃ -
        (n2 w₁ w₂ w₃ l₁ l₂ l₃)^3 := by
  rw [three_parallel_hankel_determinant]
  have hsq12 : 0 < (l₁ - l₂)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h12)
  have hsq13 : 0 < (l₁ - l₃)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h13)
  have hsq23 : 0 < (l₂ - l₃)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h23)
  positivity

/-- Each of the three physical rates is a root of the characteristic cubic. -/
theorem three_parallel_rate_roots (l₁ l₂ l₃ : ℝ) :
    l₁^3 - e1 l₁ l₂ l₃ * l₁^2 + e2 l₁ l₂ l₃ * l₁ - e3 l₁ l₂ l₃ = 0 ∧
    l₂^3 - e1 l₁ l₂ l₃ * l₂^2 + e2 l₁ l₂ l₃ * l₂ - e3 l₁ l₂ l₃ = 0 ∧
    l₃^3 - e1 l₁ l₂ l₃ * l₃^2 + e2 l₁ l₂ l₃ * l₃ - e3 l₁ l₂ l₃ = 0 := by
  dsimp [e1, e2, e3]
  constructor
  · ring
  constructor <;> ring

end HydrologyIdentifiability
