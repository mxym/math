import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Algebraic exports for the written weighted-counting proof.
   Hypergraph incidence, LP duality and equality classification
   are not postulated or formalized by these exports. -/
namespace FractionalCoverEnvelope

theorem peak_rearrangement (r Y b : ℝ) (h : Y ≤ r-(r-1)*b) :
    (r-1)*b ≤ r-Y := by linarith

theorem group_mass (m g c Y b t : ℝ) (hc : c ≤ g) (hbt : t ≤ b)
    (hY : Y ≤ c*b+(m-c)*t) : Y ≤ g*b+(m-g)*t := by
  have hp := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hbt)
  nlinarith

theorem weighted_elimination (r k g m Y b : ℝ) (hr : 1 ≤ r)
    (hA : 0 ≤ (k+1)*g-m) (hStar : Y ≤ r-(r-1)*b)
    (hMass : k*Y ≤ k*g*b+(m-g)*(1-b)) :
    Y*(k*(r-1)+(k+1)*g-m) ≤ g*(k*r+1)-m := by
  have hs := mul_nonneg hA (sub_nonneg.mpr hStar)
  have hm := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hMass)
  nlinarith only [hs, hm]

theorem denominator_positive (r k m : ℝ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hm : m ≤ k*r) : 0 < (k*k+k-1)*r+1-m := by
  have hk2 : 4 ≤ k*k := by nlinarith
  have hp := mul_nonneg (show 0 ≤ k*k-1 by linarith) (show 0 ≤ r by linarith)
  nlinarith

theorem group_coefficient_positive (r k m : ℝ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hm : m ≤ k*r) : 0 < (k+1)*((k-1)*r+1)-m := by
  have hp := mul_nonneg (show 0 ≤ k*k-k-1 by nlinarith) (show 0 ≤ r by linarith)
  nlinarith

theorem finite_numerator (r k m : ℝ) :
    ((k-1)*r+1)*(k*r+1)-m = k*(k-1)*r*r+(2*k-1)*r+1-m := by ring

theorem finite_denominator (r k m : ℝ) :
    k*(r-1)+(k+1)*((k-1)*r+1)-m = (k*k+k-1)*r+1-m := by ring

theorem small_peak_factorization (r k m : ℝ) :
    (k+1)*(k*(k-1)*r*r+(2*k-1)*r+1-m)
      -m*((k*k+k-1)*r+1-m) =
    (m-(k+1)*((k-1)*r+1))*(m-k*r-1) := by ring

theorem forbidden_low_edge (k b : ℝ) (hk : 1 < k) (hb : 1 < (k+1)*b) :
    k < k*k*b+1-b := by
  have hp := mul_pos (sub_pos.mpr hk) (sub_pos.mpr hb)
  nlinarith

theorem interpolation_gap (k t : ℝ) :
    (k*k-1+t)*(k*k-t)-k*k*(k*k-1) = t*(1-t) := by ring

theorem finite_error_identity (r k t p : ℝ) (hp : (k*k-t)*p = k*(k-1)) :
    k*(k-1)*r*r+(k-t)*r+1-r*p*((k*k-t)*r+1)
       = (k-t-p)*r+1 := by
  have hpr := congrArg (fun z : ℝ => z*r*r) hp
  nlinarith only [hpr]

theorem error_budget (r k t p : ℝ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (ht : 0 ≤ t) (hp : k-1 ≤ k*p) :
    k*((k-t-p)*r+1) ≤ (k*k-t)*r+1 := by
  have h1 := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ k-1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ r by linarith) (sub_nonneg.mpr hp)
  have h3 := mul_nonneg (show 0 ≤ r by linarith)
    (mul_nonneg ht (show 0 ≤ k-1 by linarith))
  nlinarith only [h1,h2,h3]

#print axioms peak_rearrangement
#print axioms group_mass
#print axioms weighted_elimination
#print axioms denominator_positive
#print axioms group_coefficient_positive
#print axioms finite_numerator
#print axioms finite_denominator
#print axioms small_peak_factorization
#print axioms forbidden_low_edge
#print axioms interpolation_gap
#print axioms finite_error_identity
#print axioms error_budget
end FractionalCoverEnvelope
