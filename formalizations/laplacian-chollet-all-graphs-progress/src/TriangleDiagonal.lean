import Triangle
import Mathlib.Tactic.Linarith

namespace Chollet

def triP (a b c x y z : ℝ) : ℝ :=
  a*b*c + a*z^2 + b*y^2 + c*x^2 - 2*x*y*z

def triQ (a b c x y z : ℝ) : ℝ :=
  a^2*b^2*c^2 + a^2*z^4 + b^2*y^4 + c^2*x^4 + 2*x^2*y^2*z^2

def triF (a b c x y z : ℝ) : ℝ :=
  triP a b c x y z * (a*b*c) - triQ a b c x y z

private theorem triF_first_increment
    (a b c x y z t : ℝ) :
    triF (a+t) b c x y z - triF a b c x y z =
      t * (b*c*(b*y^2+c*x^2-2*x*y*z) +
        2*a*z^2*(b*c-z^2)) +
      t^2*z^2*(b*c-z^2) := by
  unfold triF triP triQ
  ring

private theorem triF_first_monotone
    (a b c x y z t : ℝ)
    (ha : 0 ≤ a) (_hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hb : z ≤ b) (hc : z ≤ c) :
    triF a b c x y z ≤ triF (a+t) b c x y z := by
  have hpivot : 0 ≤ b*y^2+c*x^2-2*x*y*z := by
    have hp :
      b*y^2+c*x^2-2*x*y*z =
        (b-z)*y^2+(c-z)*x^2+z*(x-y)^2 := by ring
    rw [hp]
    positivity
  have hminor : 0 ≤ b*c-z^2 := by
    have hh :
      b*c-z^2 =
        (b-z)*(c-z) + z*(b-z)+z*(c-z) := by ring
    rw [hh]
    positivity
  have hbpos : 0 ≤ b := le_trans hz hb
  have hcpos : 0 ≤ c := le_trans hz hc
  rw [← sub_nonneg, triF_first_increment]
  positivity

private theorem triF_swap12 (a b c x y z : ℝ) :
    triF a b c x y z = triF b a c x z y := by
  unfold triF triP triQ
  ring

private theorem triF_swap13 (a b c x y z : ℝ) :
    triF a b c x y z = triF c b a z y x := by
  unfold triF triP triQ
  ring

private theorem triF_second_monotone
    (a b c x y z t : ℝ)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t)
    (ha : y ≤ a) (hc : y ≤ c) :
    triF a b c x y z ≤ triF a (b+t) c x y z := by
  calc
    triF a b c x y z = triF b a c x z y := triF_swap12 _ _ _ _ _ _
    _ ≤ triF (b+t) a c x z y :=
      triF_first_monotone b a c x z y t hb hx hz hy ht ha hc
    _ = triF a (b+t) c x y z :=
      (triF_swap12 _ _ _ _ _ _).symm

private theorem triF_third_monotone
    (a b c x y z t : ℝ)
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (ht : 0 ≤ t)
    (ha : x ≤ a) (hb : x ≤ b) :
    triF a b c x y z ≤ triF a b (c+t) x y z := by
  calc
    triF a b c x y z = triF c b a z y x := triF_swap13 _ _ _ _ _ _
    _ ≤ triF (c+t) b a z y x :=
      triF_first_monotone c b a z y x t hc hz hy hx ht hb ha
    _ = triF a b (c+t) x y z :=
      (triF_swap13 _ _ _ _ _ _).symm

private theorem triF_base (x y z : ℝ) :
    triF (x+y) (x+z) (y+z) x y z =
      2*(x*y+x*z+y*z)*(x^2*y^2+x^2*z^2+y^2*z^2) := by
  unfold triF triP triQ
  ring

/-- Strong-Chollet slack for EVERY weakly diagonally dominant
symmetric three-by-three real matrix with nonpositive offdiagonals. -/
theorem three_diagonal_dominant_slack (a b c x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : x+y ≤ a) (hb : x+z ≤ b) (hc : y+z ≤ c) :
    0 ≤ triF a b c x y z := by
  let p : ℝ := a-(x+y)
  let q : ℝ := b-(x+z)
  let r : ℝ := c-(y+z)
  have hp : 0 ≤ p := sub_nonneg.mpr ha
  have hq : 0 ≤ q := sub_nonneg.mpr hb
  have hr : 0 ≤ r := sub_nonneg.mpr hc
  have hap : a = x+y+p := by dsimp [p]; ring
  have hbq : b = x+z+q := by dsimp [q]; ring
  have hcr : c = y+z+r := by dsimp [r]; ring
  rw [hap,hbq,hcr]
  have h0 : 0 ≤ triF (x+y) (x+z) (y+z) x y z := by
    rw [triF_base]
    positivity
  have h1 : triF (x+y) (x+z) (y+z) x y z ≤
      triF (x+y+p) (x+z) (y+z) x y z :=
    triF_first_monotone (x+y) (x+z) (y+z) x y z p
      (add_nonneg hx hy) hx hy hz hp (by linarith) (by linarith)
  have h2 : triF (x+y+p) (x+z) (y+z) x y z ≤
      triF (x+y+p) (x+z+q) (y+z) x y z :=
    triF_second_monotone (x+y+p) (x+z) (y+z) x y z q
      (add_nonneg hx hz) hx hy hz hq (by linarith) (by linarith)
  have h3 : triF (x+y+p) (x+z+q) (y+z) x y z ≤
      triF (x+y+p) (x+z+q) (y+z+r) x y z :=
    triF_third_monotone (x+y+p) (x+z+q) (y+z) x y z r
      (add_nonneg hy hz) hx hy hz hr (by linarith) (by linarith)
  exact le_trans h0 (le_trans h1 (le_trans h2 h3))

end Chollet

#print axioms Chollet.three_diagonal_dominant_slack
