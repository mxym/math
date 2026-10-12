import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Scalar certificates only. The combinatorics and the quoted
   edge-colouring theorem are not formalized here. -/
namespace PartiteLinearization

theorem retained_block_identity (x1 x2 x3 x4 P : ℝ) :
    x4-(x2+3*x3+6*x4-P) =
      P-(x1+2*x2+3*x3+4*x4)/2-3*(x3/2+x4)+x1/2 := by ring

theorem matching_star_product (eta s D e : ℝ)
    (heta : 0 ≤ eta) (hs : 0 ≤ s) (hD : D ≤ 2*s)
    (he : e ≤ (1+eta)*D*s) : e ≤ 2*(1+eta)*s^2 := by
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ 1+eta by linarith) hs)
    (sub_nonneg.mpr hD)
  nlinarith

theorem linearization_cover_coupling (q r W s e eta D0 : ℝ)
    (hblocks : q*(q-1)/2-q*r/2-3*W ≤ e)
    (hpart : W ≤ r*s) (haux : e ≤ 2*(1+eta)*s^2+q*D0/4) :
    q*(q-r)/2-q*(1/2+D0/4) ≤ 2*(1+eta)*s^2+3*r*s := by
  nlinarith

theorem scaling_inequality (r eta s P L : ℝ)
    (hr : 0 ≤ r) (heta : 0 ≤ eta) (hs : 0 ≤ s)
    (h : P-L ≤ 2*(1+eta)*s^2+3*r*s) :
    P-L ≤ 2*((1+eta)*s)^2+3*r*((1+eta)*s) := by
  have h1 := mul_nonneg (mul_nonneg heta (show 0 ≤ 1+eta by linarith))
    (sq_nonneg s)
  have h2 := mul_nonneg (mul_nonneg hr heta) hs
  nlinarith

theorem transition_factorization (q r : ℝ) :
    q*(q-r)/2-(2*(3*q/10-r/3)^2+3*r*(3*q/10-r/3)) =
      (3*q-5*r)*(24*q-35*r)/225 := by ring

theorem transition_lower_bound (r q b E : ℝ) (hr : 0 < r)
    (hq : 5*r ≤ 3*q) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (h : q*(q-r)/2-3*r*E ≤ 2*b^2+3*r*b) :
    3*q/10-r/3 ≤ b+E := by
  let ell := 3*q/10-r/3
  have hell : 0 ≤ ell := by dsimp [ell]; linarith
  have hp := mul_nonneg (show 0 ≤ 3*q-5*r by linarith)
    (show 0 ≤ 24*q-35*r by linarith)
  have hk : 2*ell^2+3*r*ell ≤ q*(q-r)/2 := by
    dsimp [ell]
    nlinarith
  by_contra hn
  have hd : 0 < ell-b-E := by dsimp [ell]; linarith
  have ha := mul_nonneg (show 0 ≤ ell-b by linarith) (show 0 ≤ ell+b by linarith)
  have hc := mul_pos (show 0 < 3*r by positivity) hd
  nlinarith

theorem additive_error_transfer (r eta s E C ell : ℝ)
    (hr : 0 ≤ r) (heta : 0 ≤ eta) (hC : 0 ≤ C)
    (hell : ell ≤ r) (hE : E ≤ C)
    (h : ell ≤ (1+eta)*s+E) : ell-eta*r-C ≤ s := by
  by_cases hs : s ≤ r
  · have hp := mul_nonneg heta (sub_nonneg.mpr hs)
    nlinarith
  · have hp := mul_nonneg heta hr
    linarith

theorem final_cover_bound (r q t s m eta C : ℝ)
    (hpeel : 5*t-3*q/2+5*s-5 ≤ m)
    (hs : 3*q/10-r/3-eta*r-C ≤ s) :
    5*t-(5/3+5*eta)*r-5*C-5 ≤ m := by nlinarith

#print axioms retained_block_identity
#print axioms matching_star_product
#print axioms linearization_cover_coupling
#print axioms scaling_inequality
#print axioms transition_factorization
#print axioms transition_lower_bound
#print axioms additive_error_transfer
#print axioms final_cover_bound

end PartiteLinearization
