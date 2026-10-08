import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace BapatBounds

theorem product_norm_bound {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i ∈ s, ‖a i‖ ≤ R) :
    ‖∏ i ∈ s, a i‖ ≤ R ^ s.card := by
  calc
    ‖∏ i ∈ s, a i‖ ≤ ∏ i ∈ s, ‖a i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, R := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) ha
    _ = R ^ s.card := by simp

/-- A telescoping bound, including the empty product and zero-radius cases. -/
theorem product_difference_bound {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ R) (hb : ∀ i ∈ s, ‖b i‖ ≤ R)
    (hd : ∀ i ∈ s, ‖a i - b i‖ ≤ t) :
    ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤ (s.card : ℝ) * t * R ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have hbi := hb i (Finset.mem_insert_self i s)
    have hdi := hd i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, ‖a j‖ ≤ R := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, ‖b j‖ ≤ R := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hds : ∀ j ∈ s, ‖a j - b j‖ ≤ t := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    specialize ih has hbs hds
    by_cases hs : s.card = 0
    · have : s = ∅ := Finset.card_eq_zero.mp hs
      subst s
      simpa using hdi
    have hsp : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs
    have hpow : R * R ^ (s.card - 1) = R ^ s.card := by
      rw [← pow_succ']
      congr 1
      omega
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have heq : a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j) =
        (a i - b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) := by ring
    rw [heq]
    calc
      _ ≤ ‖(a i - b i) * (∏ j ∈ s, a j)‖ +
          ‖b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)‖ := norm_add_le _ _
      _ = ‖a i - b i‖ * ‖∏ j ∈ s, a j‖ +
          ‖b i‖ * ‖(∏ j ∈ s, a j) - ∏ j ∈ s, b j‖ := by simp only [norm_mul]
      _ ≤ t * R ^ s.card + R * ((s.card : ℝ) * t * R ^ (s.card - 1)) :=
        add_le_add (mul_le_mul hdi (product_norm_bound s a R hR has) (norm_nonneg _) ht)
          (mul_le_mul hbi ih (norm_nonneg _) hR)
      _ = ((s.card + 1 : ℕ) : ℝ) * t * R ^ (s.card + 1 - 1) := by
        rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        calc
          _ = t * R ^ s.card + (s.card : ℝ) * t * (R * R ^ (s.card - 1)) := by ring
          _ = _ := by rw [hpow]; ring

/-- The actual matrix product along any permutation has the same bound. -/
theorem permutation_product_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n))
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (hB : ∀ i j, ‖B i j‖ ≤ R)
    (hd : ∀ i j, ‖A i j - B i j‖ ≤ t) :
    ‖(∏ i, A i (σ i)) - ∏ i, B i (σ i)‖ ≤ (n : ℝ) * t * R ^ (n - 1) := by
  simpa using product_difference_bound Finset.univ (fun i => A i (σ i))
    (fun i => B i (σ i)) R t hR ht (fun i _ => hA i (σ i))
    (fun i _ => hB i (σ i)) (fun i _ => hd i (σ i))

end BapatBounds
