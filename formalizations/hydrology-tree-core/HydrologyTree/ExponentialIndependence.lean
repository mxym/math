import HydrologyTree.ScalarForcedODE
import Mathlib.LinearAlgebra.Vandermonde

/-! Independence of distinct real exponentials on EVERY nonempty open interval.
The proof differentiates actual functions and uses the exact Vandermonde matrix. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

variable {n : ℕ}

def exponentialMoment (r c : Fin (n+1) → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i, c i*(r i)^k*Real.exp (r i*s)

theorem exponentialMoment_derivative (r c : Fin (n+1) → ℝ) (k : ℕ) (s : ℝ) :
    HasDerivAt (exponentialMoment r c k) (exponentialMoment r c (k+1) s) s := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id s).const_mul (r i)).exp).const_mul (c i*(r i)^k))
  have hefun : (∑ i : Fin (n+1), fun y : ℝ => c i*(r i)^k*Real.exp (r i*id y)) =
      exponentialMoment r c k := by
    funext y
    simp [exponentialMoment]
  rw [hefun] at h
  apply h.congr_deriv
  simp only [id_eq,mul_one,exponentialMoment]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Vanishing on an open interval forces every coefficient to be zero. -/
theorem exponential_sum_independent (r c : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (a b : ℝ) (hab : a < b) (hzero : ∀ s ∈ Set.Ioo a b, exponentialMoment r c 0 s=0) : c=0 := by
  have hall : ∀ k : ℕ, ∀ s ∈ Set.Ioo a b, exponentialMoment r c k s=0 := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      intro s hs
      have he : exponentialMoment r c k =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with v hv
        exact ih v hv
      exact (exponentialMoment_derivative r c k s).unique
        ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he)
  let s := (a+b)/2
  have hs : s ∈ Set.Ioo a b := by dsimp [s]; constructor <;> linarith
  have hz : (Matrix.vandermonde r)ᵀ *ᵥ(fun i => c i*Real.exp (r i*s))=0 := by
    ext j
    have h := hall j.val s hs
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.vandermonde_apply,
      exponentialMoment,Pi.zero_apply,mul_left_comm,mul_comm,mul_assoc] using h
  have hd : IsUnit (Matrix.vandermonde r)ᵀ.det := by
    rw [Matrix.det_transpose,isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hr
  have hv := congrArg (fun v => ((Matrix.vandermonde r)ᵀ)⁻¹*ᵥv) hz
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hd,Matrix.one_mulVec,Matrix.mulVec_zero] at hv
  funext i
  have hi := congrFun hv i
  exact (mul_eq_zero.mp hi).resolve_right (Real.exp_ne_zero _)

end HydrologyTree
