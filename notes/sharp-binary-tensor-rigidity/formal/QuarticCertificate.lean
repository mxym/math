import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The complete scalar certificate used in the sharp binary-quartic bound.
Tensor geometry, angular maximization and equality classification are proved
in paper.md, not formalized here. No numerical oracle is used. -/

namespace SharpBinaryTensor

noncomputable section

def tau (u v : ℝ) : ℝ := (v-u)/6
def cap (v : ℝ) : ℝ := (4-v^2)/16
def defect (u v s : ℝ) : ℝ :=
  3*s + 12*(tau u v)^2 - 12*u*(tau u v)*s - 48*u*(tau u v)^3 -
  (48+36*u^2)*(tau u v)^2*s - (4+12*u^2)*s^2 - 96*(tau u v)^4

theorem endpoint_zero (u v : ℝ) :
    defect u v 0 = 12*(tau u v)^2 *
      ((4/9 : ℝ)*(u-v/4)^2 + 1-v^2/4) := by
  unfold defect tau
  ring

theorem endpoint_cap (u v : ℝ) :
    1728 * defect u v (cap v) =
      16*(4*u-v)^2*(u-v)^2 +
      27*(1-u^2)*(4-v^2)*(4*u^2-8*u*v+v^2+8) := by
  unfold defect tau cap
  ring

theorem quadratic_factor (u v : ℝ) :
    4*u^2-8*u*v+v^2+8 = (2*u-v)^2 + 4*(2-u*v) := by ring

theorem interpolation (u v s : ℝ) :
    cap v * defect u v s =
      (cap v-s)*defect u v 0 + s*defect u v (cap v) +
      (4+12*u^2)*cap v*s*(cap v-s) := by
  unfold defect tau cap
  ring

theorem quartic_scalar_nonnegative (u v s : ℝ)
    (hu0 : -1 ≤ u) (hu1 : u ≤ 1) (hv0 : -2 ≤ v) (hv1 : v ≤ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ cap v) : 0 ≤ defect u v s := by
  have hu2 : 0 ≤ 1-u^2 := by nlinarith
  have hv2 : 0 ≤ 4-v^2 := by nlinarith
  have huv : u*v ≤ 2 := by
    have h1 := mul_nonneg (show 0 ≤ 1-u by linarith) (show 0 ≤ 2+v by linarith)
    have h2 := mul_nonneg (show 0 ≤ 1+u by linarith) (show 0 ≤ 2-v by linarith)
    nlinarith
  have hq : 0 ≤ 4*u^2-8*u*v+v^2+8 := by
    rw [quadratic_factor]
    nlinarith [sq_nonneg (2*u-v)]
  have hzero : 0 ≤ defect u v 0 := by
    rw [endpoint_zero]
    have hb : 0 ≤ (4/9 : ℝ)*(u-v/4)^2+1-v^2/4 := by
      nlinarith [sq_nonneg (u-v/4)]
    exact mul_nonneg (by positivity) hb
  have htop : 0 ≤ defect u v (cap v) := by
    have ha : 0 ≤ 16*(4*u-v)^2*(u-v)^2 := by positivity
    have hb := mul_nonneg (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 27 by norm_num) hu2) hv2) hq
    have he := endpoint_cap u v
    nlinarith
  have hk : 0 ≤ cap v := by unfold cap; linarith
  by_cases hz : cap v = 0
  · have hs : s = 0 := by linarith
    simpa [hs] using hzero
  · have hkpos : 0 < cap v := by positivity
    have ha := mul_nonneg (sub_nonneg.mpr hs1) hzero
    have hb := mul_nonneg hs0 htop
    have hc := mul_nonneg (mul_nonneg
      (mul_nonneg (show 0 ≤ 4+12*u^2 by positivity) hk) hs0) (sub_nonneg.mpr hs1)
    have hi := interpolation u v s
    have hm : 0 ≤ cap v * defect u v s := by linarith
    exact nonneg_of_mul_nonneg_right hm hkpos

theorem residual_defect_identity (u t s : ℝ) :
    3*((1/2-2*u*t+2*t^2+2*s*(1-u^2))*(2*s+8*t^2)-4*t^2*s*(1-u^2)) -
      4*(2*s+6*t^2)^2 = defect u (u+6*t) s := by
  unfold defect tau
  ring

theorem binary_cubic_trace_bound (a b c d : ℝ) :
    3*((a+c)^2+(b+d)^2) ≤ 4*(a^2+3*b^2+3*c^2+d^2) := by
  nlinarith [sq_nonneg (a-3*c), sq_nonneg (d-3*b)]

theorem gram_trace_identity (a b c : ℝ) :
    (a-c)^2+4*b^2 = 2*(a^2+2*b^2+c^2)-(a+c)^2 := by ring

theorem order_growth_interpolation (E A B p : ℝ)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A)
    (hp : 0 ≤ p) (h1 : E ≤ (3/2 : ℝ)*(A+B)) (h2 : E ≤ p*B/4) :
    E^2 ≤ (3*p/4)*A*B := by
  have hb := mul_nonneg hB (sub_nonneg.mpr hBA)
  have hm := mul_nonneg (sub_nonneg.mpr h2) hE
  have hn := mul_nonneg (mul_nonneg hp hB) (sub_nonneg.mpr h1)
  nlinarith

#print axioms endpoint_zero
#print axioms endpoint_cap
#print axioms quadratic_factor
#print axioms interpolation
#print axioms quartic_scalar_nonnegative
#print axioms residual_defect_identity
#print axioms binary_cubic_trace_bound
#print axioms gram_trace_identity
#print axioms order_growth_interpolation

end
end SharpBinaryTensor
