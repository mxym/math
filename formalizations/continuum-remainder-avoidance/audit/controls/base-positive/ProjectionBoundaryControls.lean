import ContinuumGeometric
import Mathlib.Topology.Order.DenselyOrdered

open ContinuumGeometric Set

-- A negative coefficient logarithm is retained; the original indices are counted.
example : ∃ tests : Finset ℕ, (4 : ℝ) ≤ tests.card ∧
    ∀ n ∈ tests, 4 ≤ n ∧ (10 : ℝ) < (1 : ℝ) * n - (-2 : ℤ) ∧
      (1 : ℝ) * n - (-2 : ℤ) < 26 := by
  have h := compact_shifted_original_activation 1 2 10 16 1 4 (-2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    1 (by norm_num)
  norm_num at h ⊢
  exact h

-- With no finite routing tests, R is all centers when the parameter rectangle is nonempty.
-- Repair still succeeds using the infinite tail; it cannot insist on a finite witness.
example : ∀ x : ℝ, ∃ n : ℕ, 100 ≤ n ∧
    powerPoint (dyadic n) ((2 : ℝ) ^ (-2 : ℤ))
      (x, ((⟨1, by norm_num⟩ : Icc (1 : ℝ) 2), (⟨1, by norm_num⟩ : Icc (1 : ℝ) 2))) ∈
      (∅ : Set ℝ) ∪ univ := by
  have repair := power_repair_all_centers 1 2 (by norm_num) ∅ (-2)
    (fun e : Fin 0 => Fin.elim0 e) ∅ ∅ univ (by simp) isOpen_univ
    (by simp) 100 (by simp)
  intro x
  exact repair x _

-- The closed error endpoint is admitted by the double-open-buffer proof.
example : (3 / 2 : ℝ) ∈ Metric.thickening 2 ({0} : Set ℝ) := by
  have h := double_buffer_contains_perturbation ({0} : Set ℝ) 1 (1 / 2) 1
    (Metric.mem_thickening_iff.2 ⟨0, by simp, by norm_num [Real.dist_eq]⟩)
    (by norm_num)
  convert h using 1 <;> norm_num

-- Omitting k=-2 would lose this active original index.
example : (9 : ℕ) ∈ activeNaturals (10 + (-2 : ℤ)) 16 1 := by
  rw [mem_activeNaturals_iff _ _ _ (by norm_num) (by norm_num)]
  norm_num

-- A compact-rectangle slice with CLOSED activation has a nonclosed failure set.
-- This is the exact power point at center 0, input 1/2, coefficient 1.
example : ¬ IsClosed ((Icc (1 / 2 : ℝ) 2) ∩
    {s : ℝ | s ∉ Icc 1 2 ∨ (1 / 2 : ℝ) ^ s ∉ Ioo (2 / 5) (3 / 5)}) := by
  let bad : Set ℝ := (Icc (1 / 2 : ℝ) 2) ∩
    {s : ℝ | s ∉ Icc 1 2 ∨ (1 / 2 : ℝ) ^ s ∉ Ioo (2 / 5) (3 / 5)}
  have hsub : Ioo (1 / 2 : ℝ) 1 ⊆ bad := by
    intro s hs
    refine ⟨⟨hs.1.le, by linarith [hs.2]⟩, Or.inl ?_⟩
    intro ha
    linarith [ha.1, hs.2]
  have hlim : (1 : ℝ) ∈ closure bad := by
    apply closure_mono hsub
    rw [closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    norm_num
  intro hclosed
  change IsClosed bad at hclosed
  rw [hclosed.closure_eq] at hlim
  norm_num [bad, Real.rpow_one] at hlim
