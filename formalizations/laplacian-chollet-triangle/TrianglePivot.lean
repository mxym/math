import TriangleStieltjes
import Mathlib.Tactic.Linarith

namespace Chollet

/-- Direct singleton permanent pivot bound for the genuine 3x3
Stieltjes scalar permanent. Only the OTHER TWO vertex diagonal
dominance inequalities are needed. -/
theorem stieltjes_three_first_pivot
    (a b c x y z : ℝ)
    (hz : 0 ≤ z) (hb : z ≤ b) (hc : z ≤ c) :
    a*(b*c+z^2) ≤ triP a b c x y z := by
  have hnonneg : 0 ≤ (b-z)*y^2+(c-z)*x^2+z*(x-y)^2 := by
    positivity
  have hid :
      triP a b c x y z - a*(b*c+z^2) =
        (b-z)*y^2+(c-z)*x^2+z*(x-y)^2 := by
    unfold triP
    ring
  rw [← sub_nonneg, hid]
  exact hnonneg

theorem stieltjes_three_all_scalar_pivots
    (a b c x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : x+y ≤ a) (hb : x+z ≤ b) (hc : y+z ≤ c) :
    a*(b*c+z^2) ≤ triP a b c x y z ∧
    b*(a*c+y^2) ≤ triP a b c x y z ∧
    c*(a*b+x^2) ≤ triP a b c x y z := by
  have hp1 := stieltjes_three_first_pivot a b c x y z
    hz (by linarith) (by linarith)
  have hp2 := stieltjes_three_first_pivot b a c x z y
    hy (by linarith) (by linarith)
  have hp3 := stieltjes_three_first_pivot c b a z y x
    hx (by linarith) (by linarith)
  have hs2 : triP b a c x z y = triP a b c x y z := by
    unfold triP
    ring
  have hs3 : triP c b a z y x = triP a b c x y z := by
    unfold triP
    ring
  refine ⟨hp1, by simpa only [hs2] using hp2, ?_⟩
  calc
    c*(a*b+x^2) = c*(b*a+x^2) := by ring
    _ ≤ triP a b c x y z := by rw [← hs3]; exact hp3

end Chollet

#print axioms Chollet.stieltjes_three_first_pivot
#print axioms Chollet.stieltjes_three_all_scalar_pivots
