import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Only scalar reductions are formalized. No colouring theorem or
   hypergraph assertion is postulated in this partial certificate. -/
namespace PartiteIntersectionDefect

noncomputable section

def quad (d : ℝ) := d^2-27*d/10+19/25
def ell (r q d : ℝ) := 3*q/10-d*r

theorem low_factorization (r q d : ℝ) :
    q*(q-r)/2-(2*(ell r q d)^2+3*q*(ell r q d)/2) =
      (2*r-q)*(13*q/100-d^2*r)-quad d*q*r := by unfold ell quad; ring

theorem high_factorization (r q d : ℝ) :
    q*(q-r)/2-(2*(ell r q d)^2+3*r*(ell r q d)) =
      (q-2*r)*(8*q/25+(6*d/5-19/25)*r)-2*quad d*r^2 := by
  unfold ell quad
  ring

theorem low_comparison (r q d : ℝ) (hr : 0 ≤ r)
    (hq0 : r ≤ q) (hq1 : q ≤ 2*r) (hd0 : 3/10 ≤ d)
    (hd1 : d ≤ 1/3) (hd : quad d = 0) :
    2*(ell r q d)^2+3*q*(ell r q d)/2 ≤ q*(q-r)/2 := by
  have hs := mul_nonneg (show 0 ≤ 1/3-d by linarith)
    (show 0 ≤ 1/3+d by linarith)
  have hd2 : 0 ≤ 13/100-d^2 := by nlinarith
  have hp := mul_nonneg hr hd2
  have hf : 0 ≤ 13*q/100-d^2*r := by nlinarith
  have ht := mul_nonneg (show 0 ≤ 2*r-q by linarith) hf
  have he := low_factorization r q d
  rw [hd] at he
  nlinarith

theorem high_comparison (r q d : ℝ) (hr : 0 ≤ r)
    (hq : 2*r ≤ q) (hd0 : 3/10 ≤ d) (hd : quad d = 0) :
    2*(ell r q d)^2+3*r*(ell r q d) ≤ q*(q-r)/2 := by
  have hp := mul_nonneg hr (show 0 ≤ 6*d/5-3/25 by linarith)
  have hf : 0 ≤ 8*q/25+(6*d/5-19/25)*r := by nlinarith
  have ht := mul_nonneg (show 0 ≤ q-2*r by linarith) hf
  have he := high_factorization r q d
  rw [hd] at he
  nlinarith

theorem defect_error_transfer (r k b E l K : ℝ) (hr : 0 < r)
    (hk : r/2 ≤ k) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (h1 : K-(3*r/2)*E ≤ 2*b^2+3*k*b)
    (h2 : 2*l^2+3*k*l ≤ K) : l ≤ b+E := by
  by_contra hn
  have hd : 0 < l-b-E := by linarith
  have ha := mul_nonneg (show 0 ≤ l-b by linarith) (show 0 ≤ l+b by linarith)
  have hc := mul_pos (show 0 < 3*k by linarith) hd
  have hp := mul_nonneg (show 0 ≤ 3*k-3*r/2 by linarith) hE
  nlinarith

theorem final_defect_bound (r q d eta t s m E : ℝ)
    (hpeel : 5*t-3*q/2+5*s-5 ≤ m)
    (hs : ell r q d-eta*r-E ≤ s) :
    5*t-(5*d+5*eta)*r-5*E-5 ≤ m := by
  unfold ell at hs
  nlinarith

#print axioms low_factorization
#print axioms high_factorization
#print axioms low_comparison
#print axioms high_comparison
#print axioms defect_error_transfer
#print axioms final_defect_bound

end
end PartiteIntersectionDefect
