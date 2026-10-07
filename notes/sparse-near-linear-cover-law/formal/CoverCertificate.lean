import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/- Exact scalar components. Input K, hypergraph covers, asymptotic
   statements and equality classifications are not formalized here. -/
namespace SparseCover

theorem integer_gap (d k : ℤ) : 0 ≤ (d-k)*(d-k-1) := by
  by_cases h : d ≤ k
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem copy_weight (d : ℝ) :
    (d-1)*(d-2)/2 = d*(d-1)/2-d+1 := by ring

theorem integer_count_identity (d k : ℝ) :
    (d-k)*(d-k-1) = d*(d-1)-2*k*d+k*(k+1) := by ring

theorem adjacent_envelopes (x k : ℝ) :
    ((k-1)*k+x)*(k+2)-(k*(k+1)+x)*k = 2*(x-k) := by ring

theorem harmonic_factorization (x k : ℝ) :
    k*(k+1)*x-((k-1)*k+x)*(1+x) = (x-k+1)*(k-x) := by ring

theorem colouring_error (eta q w : ℝ) (he : 0 ≤ eta)
    (hq : 0 ≤ q) (hw : w ≤ q/2) :
    (1+eta)*(w-eta*q/2) ≤ w := by
  have h1 := mul_nonneg he (sub_nonneg.mpr hw)
  have h2 := mul_nonneg (sq_nonneg eta) hq
  nlinarith

theorem peeling_slope (L m q u A Hm Hq : ℝ) (hL : 0 ≤ L)
    (hmq : q ≤ m) (hu : 1 ≤ L*u)
    (hHm : Hm = A+u*m) (hHq : Hq ≤ A+u*q) :
    m-q ≤ L*(Hm-Hq) := by
  have h1 := mul_nonneg hL (sub_nonneg.mpr hHq)
  have h2 := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hmq)
  nlinarith

theorem variance_expansion (a d : ℝ) :
    (d-a-1)^2 = d^2-2*(a+1)*d+(a+1)^2 := by ring

theorem noninteger_gap_identity (c k : ℝ) :
    ((k-1)*k+c)-k*c = (k-1)*(k-c) := by ring

theorem noninteger_gap_positive (c k : ℝ) (hk : 1 < k) (hc : c < k) :
    0 < ((k-1)*k+c)-k*c := by
  rw [noninteger_gap_identity]
  exact mul_pos (by linarith) (by linarith)

theorem upper_bad_degree (d k : ℝ) (hk : 0 ≤ k) (hd : k+2 ≤ d) :
    d*(d-k) ≤ (k+2)*(d-k)*(d-k-1) := by
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ d-k by linarith)
    (show 0 ≤ k+1 by linarith)) (show 0 ≤ d-k-2 by linarith)
  have he : (k+2)*(d-k)*(d-k-1)-d*(d-k) =
    (d-k)*(k+1)*(d-k-2) := by ring
  rw [← he] at hp
  linarith

theorem lower_bad_degree (d k : ℝ) (hk : 0 ≤ k) (hd : d ≤ k-1) :
    d*(k-d) ≤ (k+2)*(d-k)*(d-k-1) := by
  have h1 := mul_nonneg (show 0 ≤ k+3 by linarith)
    (show 0 ≤ k-d-1 by linarith)
  have hp := mul_nonneg (show 0 ≤ k-d by linarith)
    (show 0 ≤ (k+3)*(k-d-1)+k+5 by linarith)
  have he : (k+2)*(d-k)*(d-k-1)-d*(k-d) =
    (k-d)*((k+3)*(k-d-1)+k+5) := by ring
  rw [← he] at hp
  linarith

theorem explicit_gap_transfer (theta A k u gap : ℝ)
    (ht : 0 ≤ theta) (hA : 0 ≤ A) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (h : 2*theta*gap ≤ 2*theta*u^2+k*u+A*u^2+A*(k+1)*u) :
    2*theta*gap ≤ (2*theta+k+A*(k+2))*u := by
  have hs : u^2 ≤ u := by nlinarith
  have hp := mul_nonneg (show 0 ≤ 2*theta+A by linarith)
    (sub_nonneg.mpr hs)
  nlinarith

theorem squared_gap_bound (gap J u delta : ℝ)
    (hgap : 0 ≤ gap) (hJ : 0 ≤ J) (hu : 0 ≤ u)
    (hd : delta = u^2) (h : gap ≤ J*u) : gap^2 ≤ J^2*delta := by
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ J*u+gap by positivity)
  rw [hd]
  nlinarith

#print axioms integer_gap
#print axioms copy_weight
#print axioms integer_count_identity
#print axioms adjacent_envelopes
#print axioms harmonic_factorization
#print axioms colouring_error
#print axioms peeling_slope
#print axioms variance_expansion
#print axioms noninteger_gap_identity
#print axioms noninteger_gap_positive
#print axioms upper_bad_degree
#print axioms lower_bad_degree
#print axioms explicit_gap_transfer
#print axioms squared_gap_bound

end SparseCover
