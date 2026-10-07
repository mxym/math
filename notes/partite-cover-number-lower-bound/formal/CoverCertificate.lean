import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Selected scalar certificates. No finite hypergraph definitions or
   combinatorial reductions are formalized by this file. -/
namespace PartiteCoverCertificate

theorem incidence_slack (x1 x2 x3 x4 : ℝ) :
    (x1+2*x2+3*x3+4*x4)/2+4*(x3/2+x4)-(x1+x3)/2 =
      x2+3*x3+6*x4 := by ring

theorem residual_interpolation (r q W z : ℝ)
    (hcount : q*(q-1) ≤ q*r+8*W)
    (hcover : 2*r*z ≤ r*q+r-2*W) :
    8*r*z ≤ 4*r*q+4*r-q*(q-r-1) := by nlinarith

theorem peeled_quadratic (r q m t z : ℝ) (hr : 0 ≤ r)
    (hpeel : q+5*(t-z) ≤ m)
    (hres : 8*r*z ≤ 4*r*q+4*r-q*(q-r-1)) :
    40*r*t-17*r*q+5*q*(q-1)-20*r ≤ 8*r*m := by
  have hp := mul_nonneg (show 0 ≤ 8*r by positivity) (sub_nonneg.mpr hpeel)
  nlinarith

theorem completed_square (r q : ℝ) :
    (-340*r*q+100*q*(q-1)-400*r) -
      (-289*r^2-570*r-25) = (10*q-17*r-5)^2 := by ring

theorem elementary_lower_bound (r q m t : ℝ)
    (hB : 40*r*t-17*r*q+5*q*(q-1)-20*r ≤ 8*r*m) :
    800*r*t-289*r^2-570*r-25 ≤ 160*r*m := by
  nlinarith [sq_nonneg (10*q-17*r-5)]

theorem threshold_factorization (r q : ℝ) :
    (-17*r*q+5*q*(q-1)-20*r)-(-14*r^2-30*r) =
      (q-2*r)*(5*q-7*r-5) := by ring

theorem strengthened_lower_bound (r q m t : ℝ) (hr : 2 ≤ r)
    (hA : 20*t-5*r-q-20 ≤ 4*m)
    (hB : 40*r*t-17*r*q+5*q*(q-1)-20*r ≤ 8*r*m) :
    20*t-7*r-20 ≤ 4*m := by
  by_cases hq : q ≤ 2*r
  · linarith
  · have hq0 : 0 ≤ q-2*r := by linarith
    have hq1 : 0 ≤ 5*q-7*r-5 := by linarith
    have hp := mul_nonneg hq0 hq1
    have hc : 0 ≤ 2*r*(4*m-20*t+7*r+20) := by nlinarith
    have hd := nonneg_of_mul_nonneg_right hc (show 0 < 2*r by linarith)
    linarith

theorem degree_three_small_contradiction (u s a : ℝ)
    (hu : 0 < u) (hu8 : u ≤ 8)
    (ha : a ≤ -1) (ht : s ≤ u-3+2*a)
    (hc : 2*u*a ≥ 2*u-(12-u)*s) : False := by
  have hcoef : 0 ≤ 12-u := by linarith
  have hbound : 0 ≤ u-5-s := by linarith
  have hp := mul_nonneg hcoef hbound
  have hn := mul_nonneg (show 0 ≤ 2*u by positivity) (show 0 ≤ -1-a by linarith)
  nlinarith [sq_nonneg (u-13/2)]

theorem degree_three_large_contradiction (u s a : ℝ)
    (hu : 0 < u) (ha : a ≤ -1)
    (ht : s ≤ u-3+2*a) (hc : 2*u*a ≥ 2*u-4*s) : False := by
  have hn := mul_nonneg (show 0 ≤ 2*u by positivity) (show 0 ≤ -1-a by linarith)
  nlinarith

#print axioms incidence_slack
#print axioms residual_interpolation
#print axioms peeled_quadratic
#print axioms completed_square
#print axioms elementary_lower_bound
#print axioms threshold_factorization
#print axioms strengthened_lower_bound
#print axioms degree_three_small_contradiction
#print axioms degree_three_large_contradiction

end PartiteCoverCertificate
