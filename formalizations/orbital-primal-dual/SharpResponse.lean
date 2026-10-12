import FiniteMarginals

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

def SignedBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ v, Kernel A v → |v i| ≤ C * TV v

def PairBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ p q, Probability p → Probability q → Match A p q → p i - q i ≤ C

theorem signedBound_iff_pairBound (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) : SignedBound A i C ↔ PairBound A i C := by
  constructor
  · intro h p q hp hq hm
    calc
      p i - q i ≤ |p i - q i| := le_abs_self _
      _ ≤ C * TV (fun j => p j - q j) := h _ (kernel_of_match A p q hp hq hm)
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (tv_probability_difference_le_one p q hp hq) hC
      _ = C := mul_one _
  · intro h v hv
    by_cases hz : v = 0
    · subst v
      simp [TV]
    have hd := tv_pos v hz
    have hpq := jordan_probabilities A v hv hz
    have hm := jordan_match A v hv
    have hpos := h (jordanP v) (jordanQ v) hpq.1 hpq.2 hm
    have hneg := h (jordanQ v) (jordanP v) hpq.2 hpq.1 (fun j => (hm j).symm)
    rw [jordan_difference] at hpos
    have hneg' : -(v i / TV v) ≤ C := by
      rw [← jordan_difference v i]
      linarith
    have hab : |v i / TV v| ≤ C := abs_le.mpr ⟨by linarith, hpos⟩
    rwa [abs_div, abs_of_pos hd, div_le_iff₀ hd] at hab

variable [Nonempty I]

def uniform (_i : I) : ℝ := (Fintype.card I : ℝ)⁻¹

theorem uniform_pos (i : I) : 0 < uniform i := by
  dsimp [uniform]
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem uniform_probability : Probability (uniform : I → ℝ) := by
  constructor
  · intro i
    exact (uniform_pos i).le
  · simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def UniformLawBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ p, Probability p → Match A p uniform →
    |p i - uniform i| ≤ C * TV (fun j => p j - uniform j)

theorem kernel_small_perturbation (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) :
    ∃ ε : ℝ, 0 < ε ∧ Probability (fun i => uniform i + ε * v i) ∧
      Match A (fun i => uniform i + ε * v i) uniform := by
  classical
  let S : ℝ := ∑ i, |v i|
  let a : ℝ := (Fintype.card I : ℝ)⁻¹
  let ε : ℝ := a / (1 + S)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : 0 < a := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hden : 0 < 1 + S := by linarith
  have hε : 0 < ε := div_pos ha hden
  have hid : ε * (1 + S) = a := by
    dsimp [ε]
    exact div_mul_cancel₀ _ hden.ne'
  refine ⟨ε, hε, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hab : |v i| ≤ S := Finset.single_le_sum
      (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
    have hl : -S ≤ v i := by linarith [neg_abs_le (v i)]
    have hmul := mul_le_mul_of_nonneg_left hl hε.le
    change 0 ≤ a + ε * v i
    nlinarith
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv.1, mul_zero, add_zero]
    exact uniform_probability.2
  · intro j
    simp only [mul_add, mul_left_comm (A j _) ε, Finset.sum_add_distrib,
      ← Finset.mul_sum, hv.2 j, mul_zero, add_zero]

theorem uniformLawBound_iff_signedBound (A : J → I → ℝ) (i : I) (C : ℝ) :
    UniformLawBound A i C ↔ SignedBound A i C := by
  constructor
  · intro h v hv
    obtain ⟨ε, hε, hp, hm⟩ := kernel_small_perturbation A v hv
    have hb := h _ hp hm
    simp only [add_sub_cancel_left] at hb
    rw [abs_mul, abs_of_pos hε, tv_smul, abs_of_pos hε] at hb
    have : ε * |v i| ≤ ε * (C * TV v) := by nlinarith [hb]
    exact le_of_mul_le_mul_left this hε
  · intro h p hp hm
    exact h _ (kernel_of_match A p uniform hp uniform_probability hm)

theorem uniformLawBound_iff_pairBound (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) : UniformLawBound A i C ↔ PairBound A i C :=
  (uniformLawBound_iff_signedBound A i C).trans (signedBound_iff_pairBound A i C hC)

end
end OrbitalMarginals
