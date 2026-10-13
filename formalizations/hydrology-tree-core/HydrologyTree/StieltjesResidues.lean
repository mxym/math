import HydrologyTree.StieltjesZeroFactorization
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Positive residues of the reciprocal Stieltjes response, from the actual
polynomial derivative and a proved analytic sign identity. -/
open Polynomial
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HydrologyTree

lemma stieltjesZero_not_original_pole {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (i : Fin n) (j : Fin (n+1)) :
    -stieltjesZeroRates r w hr hw i+r j ≠ 0 := by
  have hb := stieltjesZeroRates_spec r w hr hw i
  by_cases hj : j ≤ i.castSucc
  · have h := hr.monotone hj
    linarith
  · have hj' : i.succ ≤ j := by
      change i.val+1 ≤ j.val
      have hh : ¬j.val ≤ i.val := hj
      omega
    have h := hr.monotone hj'
    linarith

lemma stieltjesResponse_hasDerivAt {I : Type*} [Fintype I]
    (r w : I → ℝ) (s : ℝ) (hs : ∀ i, s+r i ≠ 0) :
    HasDerivAt (fun z => ∑ i, w i/(z+r i)) (-(∑ i, w i/(s+r i)^2)) s := by
  have h (i : I) : HasDerivAt (fun z : ℝ => w i/(z+r i)) (-w i/(s+r i)^2) s := by
    simpa only [zero_mul,zero_sub,mul_one,id_eq] using
      (hasDerivAt_const s (w i)).fun_div ((hasDerivAt_id s).add_const (r i)) (hs i)
  simpa only [div_neg,neg_div,Finset.sum_neg_distrib] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i))

/-- The quotient of the actual numerator and denominator equals the actual
Stieltjes sum on its entire nonpole domain. -/
lemma stieltjes_quotient_eq_sum {I : Type*} [Fintype I] [DecidableEq I]
    (r w : I → ℝ) (s : ℝ) (hs : ∀ i, s+r i ≠ 0) :
    (stieltjesNumerator r w).eval s/(stieltjesDenominator r).eval s =
      ∑ i, w i/(s+r i) := by
  have hd : (stieltjesDenominator r).eval s ≠ 0 := by
    rw [eval_stieltjesDenominator]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  exact (div_eq_iff hd).mpr (stieltjes_sum_mul_denominator r w s hs).symm

/-- At any actual numerator zero away from the poles, the logarithmic quotient
of derivatives is the strictly signed reciprocal-square sum. -/
theorem stieltjes_derivative_ratio_at_zero {I : Type*} [Fintype I] [DecidableEq I]
    (r w : I → ℝ) (s : ℝ) (hs : ∀ i, s+r i ≠ 0)
    (hzero : (stieltjesNumerator r w).eval s=0) :
    (stieltjesNumerator r w).derivative.eval s/(stieltjesDenominator r).eval s =
      -(∑ i, w i/(s+r i)^2) := by
  have hd : (stieltjesDenominator r).eval s ≠ 0 := by
    rw [eval_stieltjesDenominator]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  have hq := (stieltjesNumerator r w).hasDerivAt s |>.fun_div
    ((stieltjesDenominator r).hasDerivAt s) hd
  have hratio : ((stieltjesNumerator r w).derivative.eval s*(stieltjesDenominator r).eval s -
      (stieltjesNumerator r w).eval s*(stieltjesDenominator r).derivative.eval s)/
      (stieltjesDenominator r).eval s^2 =
      (stieltjesNumerator r w).derivative.eval s/(stieltjesDenominator r).eval s := by
    rw [hzero,zero_mul,sub_zero]
    field_simp
  rw [hratio] at hq
  have he : (fun z => ∑ i, w i/(z+r i)) =ᶠ[nhds s]
      (fun z => (stieltjesNumerator r w).eval z/(stieltjesDenominator r).eval z) := by
    filter_upwards [(stieltjesDenominator r).continuousAt.eventually_ne hd] with z hz
    have hi : ∀ i, z+r i ≠ 0 := by
      rw [eval_stieltjesDenominator,Finset.prod_ne_zero_iff] at hz
      exact fun i => hz i (Finset.mem_univ i)
    exact (stieltjes_quotient_eq_sum r w z hi).symm
  exact (hq.congr_of_eventuallyEq he).unique (stieltjesResponse_hasDerivAt r w s hs)

/-- Positive coefficient of the minus-simple-pole term in the reciprocal. -/
def reciprocalResidue {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (i : Fin n) : ℝ :=
  -(stieltjesDenominator r).eval (-stieltjesZeroRates r w hr hw i) /
    (stieltjesNumerator r w).derivative.eval (-stieltjesZeroRates r w hr hw i)

/-- Every reciprocal residue is strictly positive; no sign oracle or
unproved Stieltjes transformation theorem is used. -/
theorem reciprocalResidue_pos {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (i : Fin n) :
    0 < reciprocalResidue r w hr hw i := by
  have hs := stieltjesZero_not_original_pole r w hr hw i
  have hratio := stieltjes_derivative_ratio_at_zero r w _ hs
    (stieltjesZeroRates_spec r w hr hw i).2.2
  have hsum : 0 < ∑ j, w j/(-stieltjesZeroRates r w hr hw i+r j)^2 := by
    apply Finset.sum_pos
    · intro j _
      exact div_pos (hw j) (sq_pos_of_ne_zero (hs j))
    · exact Finset.univ_nonempty
  have hneg : (stieltjesNumerator r w).derivative.eval (-stieltjesZeroRates r w hr hw i) /
      (stieltjesDenominator r).eval (-stieltjesZeroRates r w hr hw i) < 0 := by
    rw [hratio]
    exact neg_lt_zero.mpr hsum
  unfold reciprocalResidue
  rcases div_neg_iff.mp hneg with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact div_pos (neg_pos.mpr h2) h1
  · exact div_pos_of_neg_of_neg (neg_neg_of_pos h2) h1

end HydrologyTree
