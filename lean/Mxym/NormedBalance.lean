import Mxym.RademacherEquality
import Mathlib.Analysis.Normed.Module.Basic

/-! Unit-norm linear relations imply the balance condition used in entry005.
Only nonzero coefficients require unit vectors. No geometric norm construction
or balance inequality is assumed. -/
namespace Mxym.NormedBalance
open scoped BigOperators Classical
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficient_balance (c : ι → ℝ) (x : ι → E)
    (hrelation : ∑ j, c j • x j = 0)
    (hunit : ∀ j, c j ≠ 0 → ‖x j‖ = 1) :
    ∀ i, |c i| ≤ (∑ j, |c j|) / 2 := by
  have hnorm (j : ι) : ‖c j • x j‖ = |c j| := by
    by_cases hc : c j = 0
    · rw [hc, zero_smul, norm_zero, abs_zero]
    · rw [norm_smul, Real.norm_eq_abs, hunit j hc, mul_one]
  intro i
  have hs : (∑ j ∈ Finset.univ.erase i, c j • x j) + c i • x i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hrelation
  have heq : c i • x i = -(∑ j ∈ Finset.univ.erase i, c j • x j) := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [add_comm]
    exact hs
  have hle : |c i| ≤ ∑ j ∈ Finset.univ.erase i, |c j| := by
    calc
      |c i| = ‖c i • x i‖ := (hnorm i).symm
      _ = ‖-(∑ j ∈ Finset.univ.erase i, c j • x j)‖ := congrArg norm heq
      _ = ‖∑ j ∈ Finset.univ.erase i, c j • x j‖ := norm_neg _
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖c j • x j‖ :=
        norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, |c j| := by
        apply Finset.sum_congr rfl
        intro j _
        exact hnorm j
  have hsum := Finset.sum_erase_add Finset.univ (fun j => |c j|) (Finset.mem_univ i)
  linarith

theorem rademacher_bound (c : ι → ℝ) (x : ι → E)
    (hrelation : ∑ j, c j • x j = 0)
    (hunit : ∀ j, c j ≠ 0 → ‖x j‖ = 1) :
    Mxym.Rademacher.mean c ≤ (∑ j, |c j|) / 2 := by
  exact Mxym.Rademacher.balanced_bound c (coefficient_balance c x hrelation hunit)

theorem rademacher_equality_iff (c : ι → ℝ) (x : ι → E)
    (hrelation : ∑ j, c j • x j = 0)
    (hunit : ∀ j, c j ≠ 0 → ‖x j‖ = 1) :
    Mxym.Rademacher.mean c = (∑ j, |c j|) / 2 ↔
      Fintype.card {j // c j ≠ 0} ≤ 3 ∨ ∃ j, |c j| = (∑ k, |c k|) / 2 := by
  exact Mxym.Rademacher.balanced_equality_iff c (coefficient_balance c x hrelation hunit)

end Mxym.NormedBalance
