import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ErdosSimilarityGrowingGaps

open scoped BigOperators

/-!  A small, self-contained finite routing layer.

The tables below are deliberately finite.  They are the exact finite
probability calculation used by the blocker construction: after all selector
bits have been fixed, distinct terminal addresses give independent terminal
bits.  No limiting or measurable assertion is hidden in this file.
-/

noncomputable def bernoulliWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

noncomputable def bitTableWeight {S : Type*} [Fintype S]
    (p : ℝ) (σ : S → Bool) : ℝ := ∏ s, bernoulliWeight p (σ s)

theorem bernoulliWeight_sum (p : ℝ) :
    (∑ b : Bool, bernoulliWeight p b) = 1 := by
  simp [bernoulliWeight]

theorem bernoulliWeight_nonneg (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (b : Bool) : 0 ≤ bernoulliWeight p b := by
  cases b <;> simp [bernoulliWeight] <;> linarith

theorem bitTableWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    (p : ℝ) : (∑ σ : S → Bool, bitTableWeight p σ) = 1 := by
  classical
  simp only [bitTableWeight]
  rw [← Fintype.prod_sum]
  simp only [bernoulliWeight_sum, Finset.prod_const_one]

theorem bitTableWeight_nonneg {S : Type*} [Fintype S]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (σ : S → Bool) :
    0 ≤ bitTableWeight p σ := by
  apply Finset.prod_nonneg
  intro s _
  exact bernoulliWeight_nonneg p hp₀ hp₁ _

theorem product_reads_by_coordinate
    {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]
    (address : I → S) (f : I → Bool → ℝ) (σ : S → Bool) :
    (∏ i, f i (σ (address i))) =
      ∏ s, ∏ i, if address i = s then f i (σ s) else 1 := by
  classical
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem weighted_distinct_reads
    {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]
    (address : I → S) (hinj : Function.Injective address)
    (w : S → Bool → ℝ) (hw : ∀ s, (∑ b : Bool, w s b) = 1)
    (f : I → Bool → ℝ) :
    (∑ σ : S → Bool, (∏ s, w s (σ s)) *
      ∏ i, f i (σ (address i))) =
      ∏ i, ∑ b : Bool, w (address i) b * f i b := by
  classical
  have hc (σ : S → Bool) := product_reads_by_coordinate address f σ
  simp_rw [hc, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s b => w s b *
    ∏ i, if address i = s then f i b else 1)]
  let g : S → ℝ := fun s => ∑ b : Bool, w s b *
    ∏ i, if address i = s then f i b else 1
  change (∏ s, g s) = _
  have hout (s : S) (hs : s ∉ Finset.univ.image address) : g s = 1 := by
    have hne : ∀ i, address i ≠ s := by
      intro i hi
      exact hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    simpa [g, hne, add_comm] using hw s
  have hat (i : I) : g (address i) =
      ∑ b : Bool, w (address i) b * f i b := by
    have heq : ∀ j, address j = address i ↔ j = i :=
      fun j => hinj.eq_iff
    simp [g, heq]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image address))
    (fun s _ hs => hout s hs)]
  rw [Finset.prod_image hinj.injOn]
  exact Finset.prod_congr rfl (fun i _ => hat i)

theorem distinct_terminal_all_miss
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    (p : ℝ) (address : I → T) (hinj : Function.Injective address) :
    (∑ τ : T → Bool, bitTableWeight p τ *
      ∏ i, if τ (address i) = true then 0 else 1) = (1 - p) ^ Fintype.card I := by
  classical
  simp only [bitTableWeight]
  rw [weighted_distinct_reads address hinj
    (fun _ b => bernoulliWeight p b) (fun _ => bernoulliWeight_sum p)
    (fun _ b => if b = true then 0 else 1)]
  have hi : ∀ i : I, (∑ b : Bool, bernoulliWeight p b *
      if b = true then 0 else 1) = 1 - p := by
    intro i
    simp [bernoulliWeight]
  calc
    (∏ i, ∑ b : Bool, bernoulliWeight p b *
        if b = true then 0 else 1) = ∏ _i : I, (1 - p) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hi i
    _ = (1 - p) ^ Fintype.card I := by simp

theorem fair_selector_default_probability
    (b d : ℕ) (hb : 2 ≤ b) :
    (1 - (2 : ℝ) ^ (1 - (b : ℝ))) ^ d ≤ 1 := by
  have hbase : 0 ≤ (1 - (2 : ℝ) ^ (1 - (b : ℝ))) := by
    have hpow : (2 : ℝ) ^ (1 - (b : ℝ)) ≤ 1 := by
      rw [← Real.rpow_zero 2]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    linarith
  have hbase_le : 1 - (2 : ℝ) ^ (1 - (b : ℝ)) ≤ 1 := by
    have hp : 0 ≤ (2 : ℝ) ^ (1 - (b : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    linarith
  exact pow_le_one₀ hbase hbase_le

end ErdosSimilarityGrowingGaps
