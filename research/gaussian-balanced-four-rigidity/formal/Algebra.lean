import Mathlib.Tactic

/-! Partial formalization only. No Gaussian integral or geometric assertion
is encoded in the hypotheses below. See paper.md for analytic scope. -/
namespace BalancedFour

theorem radon_obstruction (c a b weight : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b)
    (hweight : weight = 1/4 + c*a*b) : weight ≠ 0 := by
  have hp : 0 ≤ c*a*b := mul_nonneg (mul_nonneg hc (le_of_lt ha)) (le_of_lt hb)
  linarith

theorem projection_bound (t s x y F : ℝ)
    (ht : 0 ≤ t) (hs : t ≤ s) (hsum : x+y = -t-s)
    (hF : t^2+s^2+x^2+y^2 ≤ F) : 4*t^2 ≤ F := by
  nlinarith [sq_nonneg (x-y), mul_nonneg ht (sub_nonneg.mpr hs),
    sq_nonneg (s-t)]

theorem interior_elimination (F T B : ℝ)
    (hmerge : F+2*T ≤ B) (hprojection : 4*T ≤ F) :
    F+4*T ≤ 4*B/3 := by linarith

theorem profile_margin :
    (1 : ℚ) - 9/16 + (9/16)^2/2 - (9/16)^3/6 - 9/16 = 29/8192 := by
  norm_num

theorem linearized_isolation (c h u v s bx by_ bz zx zy zz : ℝ)
    (hc : 0 < c) (hc1 : c < 1)
    (hKx : c*(u-(v+s)/2)-(v+s)/2=0)
    (hKy : c*(v-(u+s)/2)-(u+s)/2=0)
    (hKz : c*(s-(u+v)/2)-(u+v)/2=0)
    (hmx : zx=h*bx) (hmy : zy=h*by_) (hmz : zz=h*bz)
    (hAx : (c-1)*bx-h*zx=0)
    (hAy : (c-1)*by_-h*zy=0)
    (hAz : (c-1)*bz-h*zz=0) :
    u=0 ∧ v=0 ∧ s=0 ∧ bx=0 ∧ by_=0 ∧ bz=0 ∧ zx=0 ∧ zy=0 ∧ zz=0 := by
  have ht : u+v+s=0 := by nlinarith [hKx,hKy,hKz]
  have hd : 3*c+1 ≠ 0 := by linarith
  have hu : (3*c+1)*u=0 := by nlinarith [hKx,ht]
  have hv : (3*c+1)*v=0 := by nlinarith [hKy,ht]
  have hs : (3*c+1)*s=0 := by nlinarith [hKz,ht]
  have hu0 : u=0 := (mul_eq_zero.mp hu).resolve_left hd
  have hv0 : v=0 := (mul_eq_zero.mp hv).resolve_left hd
  have hs0 : s=0 := (mul_eq_zero.mp hs).resolve_left hd
  have hk : c-1-h^2 ≠ 0 := by nlinarith [sq_nonneg h]
  have hx : (c-1-h^2)*bx=0 := by rw [hmx] at hAx; nlinarith [hAx]
  have hy : (c-1-h^2)*by_=0 := by rw [hmy] at hAy; nlinarith [hAy]
  have hz : (c-1-h^2)*bz=0 := by rw [hmz] at hAz; nlinarith [hAz]
  have hx0 : bx=0 := (mul_eq_zero.mp hx).resolve_left hk
  have hy0 : by_=0 := (mul_eq_zero.mp hy).resolve_left hk
  have hz0 : bz=0 := (mul_eq_zero.mp hz).resolve_left hk
  refine ⟨hu0,hv0,hs0,hx0,hy0,hz0,?_,?_,?_⟩ <;> simp_all

#print axioms radon_obstruction
#print axioms projection_bound
#print axioms interior_elimination
#print axioms profile_margin
#print axioms linearized_isolation
end BalancedFour
