import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- Scalar certificates. The finite hypergraph arguments and Kahn's
   published colouring theorem are not formalized or postulated here. -/
namespace PartiteReplication

def anum (D q r z : ℝ) := (D-1)*q-(2*D+1-2*z)*r
def nnum (D q r z : ℝ) := 2*D*q-(D+(D-1)*z)*r

theorem tangent_identity (D q r z : ℝ) :
    D*((D+1)^2*q*(q-r)-(anum D q r z)^2-
      3*r*(D+1)*(anum D q r z)) =
    (nnum D q r z)^2-(D+1)^2*r^2*(z^2-2*D) := by
  unfold anum nnum
  ring

theorem tangent_comparison (D q r z ell : ℝ) (hD : 0 < D)
    (hz : z^2 = 2*D) (hell : 2*(D+1)*ell = anum D q r z) :
    2*ell^2+3*r*ell ≤ q*(q-r)/2 := by
  have he := tangent_identity D q r z
  rw [hz] at he
  simp only [sub_self, mul_zero, sub_zero] at he
  have hp : 0 ≤ D*((D+1)^2*q*(q-r)-(anum D q r z)^2-
      3*r*(D+1)*(anum D q r z)) := by
    rw [he]
    exact sq_nonneg _
  have hc := nonneg_of_mul_nonneg_right hp hD
  rw [← hell] at hc
  have hf : (D+1)^2*q*(q-r)-(2*(D+1)*ell)^2-
      3*r*(D+1)*(2*(D+1)*ell) =
      2*(D+1)^2*(q*(q-r)/2-2*ell^2-3*r*ell) := by ring
  rw [hf] at hc
  have hh := nonneg_of_mul_nonneg_right hc (show 0 < 2*(D+1)^2 by positivity)
  linarith

theorem matching_star_bound (eta s a Y : ℝ)
    (heta : 0 ≤ eta) (hs : 0 ≤ s) (ha : a ≤ 2*s)
    (hY : Y ≤ (1+eta)*a*s) : Y ≤ 2*(1+eta)*s^2 := by
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ 1+eta by linarith) hs)
    (sub_nonneg.mpr ha)
  nlinarith

theorem quadratic_error_transfer (r b E ell K : ℝ) (hr : 0 < r)
    (hb : 0 ≤ b) (hE : 0 ≤ E)
    (h1 : K-3*r*E ≤ 2*b^2+3*r*b)
    (h2 : 2*ell^2+3*r*ell ≤ K) : ell ≤ b+E := by
  by_contra hn
  have hd : 0 < ell-b-E := by linarith
  have ha := mul_nonneg (show 0 ≤ ell-b by linarith) (show 0 ≤ ell+b by linarith)
  have hp := mul_pos (show 0 < 3*r by positivity) hd
  nlinarith

theorem scaling_transfer (D r eta s E ell : ℝ)
    (hDr : 0 ≤ D*r) (heta : 0 ≤ eta) (hE : 0 ≤ E)
    (hell : ell ≤ D*r) (h : ell ≤ (1+eta)*s+E) :
    ell-eta*D*r-E ≤ s := by
  by_cases hs : s ≤ D*r
  · have hp := mul_nonneg heta (sub_nonneg.mpr hs)
    nlinarith
  · have hp := mul_nonneg heta hDr
    nlinarith

theorem final_replication_bound (D r q t s m c eta E : ℝ)
    (hpeel : (D+1)*t-((D+1)/2-1)*q+(D+1)*s-(D+1) ≤ m)
    (hs : ((D-1)*q/2-((D+1)-c)*r)-(D+1)*eta*D*r-(D+1)*E ≤
      (D+1)*s) :
    (D+1)*t-((D+1)-c+(D+1)*D*eta)*r-(D+1)*E-(D+1) ≤ m := by
  nlinarith

#print axioms tangent_identity
#print axioms tangent_comparison
#print axioms matching_star_bound
#print axioms quadratic_error_transfer
#print axioms scaling_transfer
#print axioms final_replication_bound

end PartiteReplication
