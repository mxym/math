import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
open Equiv

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

def cycleWeight (A : Matrix V V ℝ) (σ : Perm V) : ℝ :=
  ∏ i ∈ σ.support, A (σ i) i

def allCycles : Finset (Perm V) := by
  classical
  exact Finset.univ.filter Perm.IsCycle

theorem support_eq_cycle_union (σ : Perm V) :
    σ.support = σ.cycleFactorsFinset.biUnion Perm.support := by
  ext i
  rw [Finset.mem_biUnion]
  exact Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset

theorem cycle_supports_disjoint (σ : Perm V) :
    (σ.cycleFactorsFinset : Set (Perm V)).PairwiseDisjoint Perm.support := by
  intro a ha b hb hab
  exact (Perm.cycleFactorsFinset_pairwise_disjoint σ ha hb hab).disjoint_support

theorem cycleWeight_factorization (A : Matrix V V ℝ) (σ : Perm V) :
    cycleWeight A σ = ∏ τ ∈ σ.cycleFactorsFinset, cycleWeight A τ := by
  unfold cycleWeight
  rw [support_eq_cycle_union, Finset.prod_biUnion (cycle_supports_disjoint σ)]
  apply Finset.prod_congr rfl
  intro τ hτ
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Perm.mem_cycleFactorsFinset_iff.mp hτ).2 i hi]

theorem permutation_monomial_eq_cycleWeight (A : Matrix V V ℝ)
    (hd : ∀ i, A i i = 1) (σ : Perm V) :
    (∏ i, A (σ i) i) = cycleWeight A σ := by
  apply (Finset.prod_subset (Finset.subset_univ σ.support) ?_).symm
  intro i hi hnot
  have hfix := Perm.notMem_support.mp hnot
  rw [hfix, hd]

theorem permanent_unit_diag_cycle_expansion (A : Matrix V V ℝ)
    (hd : ∀ i, A i i = 1) :
    A.permanent = ∑ σ : Perm V, ∏ τ ∈ σ.cycleFactorsFinset, cycleWeight A τ := by
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [permutation_monomial_eq_cycleWeight A hd, cycleWeight_factorization]

theorem cycleWeight_nonneg (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j) (σ : Perm V) :
    0 ≤ cycleWeight A σ :=
  Finset.prod_nonneg fun i _ => hA (σ i) i

theorem cycleFactors_mem_powerset (σ : Perm V) :
    σ.cycleFactorsFinset ∈ (allCycles (V := V)).powerset := by
  classical
  apply Finset.mem_powerset.mpr
  intro τ hτ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Perm.mem_cycleFactorsFinset_iff.mp hτ).1⟩

/-- A permutation contributes its genuine disjoint simple cycles. Passing to
all subsets of simple cycles adds only nonnegative terms. A two-cycle occurs
once because a cycle is represented by its permutation, not a rooted walk. -/
theorem permanent_le_cycle_product (A : Matrix V V ℝ) (hd : ∀ i, A i i = 1)
    (hA : ∀ i j, 0 ≤ A i j) :
    A.permanent ≤ ∏ σ ∈ allCycles, (1 + cycleWeight A σ) := by
  rw [permanent_unit_diag_cycle_expansion A hd, Finset.prod_one_add]
  have he : (∑ σ : Perm V, ∏ τ ∈ σ.cycleFactorsFinset, cycleWeight A τ) =
      ∑ s ∈ Finset.univ.image Perm.cycleFactorsFinset, ∏ τ ∈ s, cycleWeight A τ := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Perm.cycleFactorsFinset_injective hab
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hs
    exact cycleFactors_mem_powerset σ
  · intro s hs hnot
    exact Finset.prod_nonneg fun σ _ => cycleWeight_nonneg A hA σ

theorem one_le_permanent_unit_diag (A : Matrix V V ℝ) (hd : ∀ i, A i i = 1)
    (hA : ∀ i j, 0 ≤ A i j) : 1 ≤ A.permanent := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := (1 : Perm V))
    (f := fun σ => ∏ i, A (σ i) i)
    (fun σ _ => Finset.prod_nonneg fun i _ => hA (σ i) i) (Finset.mem_univ _)
  simpa [Matrix.permanent, hd] using h

theorem log_permanent_le_cycle_sum (A : Matrix V V ℝ) (hd : ∀ i, A i i = 1)
    (hA : ∀ i j, 0 ≤ A i j) :
    Real.log A.permanent ≤ ∑ σ ∈ allCycles, cycleWeight A σ := by
  have hp : 0 < A.permanent := lt_of_lt_of_le zero_lt_one (one_le_permanent_unit_diag A hd hA)
  have hc (σ : Perm V) : 0 < 1 + cycleWeight A σ := by
    linarith [cycleWeight_nonneg A hA σ]
  calc
    _ ≤ Real.log (∏ σ ∈ allCycles, (1 + cycleWeight A σ)) :=
      Real.log_le_log hp (permanent_le_cycle_product A hd hA)
    _ = ∑ σ ∈ allCycles, Real.log (1 + cycleWeight A σ) :=
      Real.log_prod fun σ _ => (hc σ).ne'
    _ ≤ _ := Finset.sum_le_sum fun σ _ => by
      have h := Real.log_le_sub_one_of_pos (hc σ)
      linarith

end
end Chollet
