import Mxym.RademacherEquality

/-! Quantitative extension of entry005 v4, Lemma 2.1.
This is a finite coefficient theorem. No geometric identity is assumed.
The four-coordinate witness formulation avoids choosing order statistics. -/
namespace Mxym.Rademacher
open scoped BigOperators Classical
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Four coefficients at least `t` and a cap gap of at least `g` force the
Rademacher defect to be at least `min (t / 2) (g / 4)`. -/
theorem normalized_defect_lower_bound (a : ι → ℝ)
    (ha : a ∈ balancedPolytope) (t g : ℝ) (ht : 0 ≤ t) (hg : 0 ≤ g)
    (e : Fin 4 ↪ ι) (het : ∀ k, t ≤ a (e k))
    (hgap : ∀ i, a i ≤ 1 / 2 - g) :
    min (t / 2) (g / 4) ≤ 1 / 2 - mean a := by
  let α : ℝ := min (4 * t) (2 * g)
  have hα0 : 0 ≤ α := le_min (by linarith) (by linarith)
  have hαt : α ≤ 4 * t := min_le_left _ _
  have hαg : α ≤ 2 * g := min_le_right _ _
  have hmin : min (t / 2) (g / 4) = α / 8 := by
    rcases le_total (4 * t) (2 * g) with h | h
    · have h' : t / 2 ≤ g / 4 := by linarith
      rw [min_eq_left h']
      dsimp [α]
      rw [min_eq_left h]
      ring
    · have h' : g / 4 ≤ t / 2 := by linarith
      rw [min_eq_right h']
      dsimp [α]
      rw [min_eq_right h]
      ring
  rw [hmin]
  by_cases hzero : α = 0
  · rw [hzero]
    have hb := normalized_bound a ha
    linarith
  have hα : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hzero)
  obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have hsum := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hn i)
    linarith [ha.2]
  have hα1 : α < 1 := by linarith [hgap i]
  have hβ : 0 < 1 - α := by linarith
  let y : ι → ℝ := fun i => if i ∈ Set.range e then 1 / 4 else 0
  have hy0 (i : ι) : 0 ≤ y i := by dsimp [y]; split_ifs <;> norm_num
  let : Fintype (Set.range e) := Subtype.fintype _
  have hyin (i : Set.range e) : y i = 1 / 4 := ite_eq_left i.2
  have hyout (i : {i // i ∉ Set.range e}) : y i = 0 := ite_eq_right i.2
  have hys : (∑ i, y i) = 1 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range e) y]
    have he : Fintype.card (Set.range e) = 4 := by simpa using Fintype.card_range e
    simp only [hyin, hyout, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, he]
    norm_num
  have hym : mean y = 3 / 8 := by
    rw [mean_restrict y (fun i => i ∈ Set.range e) (by intro i hi; exact ite_eq_right hi)]
    let E := Equiv.ofInjective e e.injective
    have hf : (fun j => y (E j)) = (fun _ : Fin 4 => (1 / 4 : ℝ)) := by
      funext j
      exact ite_eq_left (E j).2
    have h := mean_reindex E (fun i : Set.range e => y i)
    rw [hf, mean_four_quarters] at h
    exact h.symm
  let z : ι → ℝ := fun i => (a i - α * y i) / (1 - α)
  have hz : z ∈ balancedPolytope (ι := ι) := by
    constructor
    · intro i
      constructor
      · apply div_nonneg _ hβ.le
        by_cases hi : i ∈ Set.range e
        · obtain ⟨k, hk⟩ := hi
          have hy : y i = 1 / 4 := ite_eq_left (by exact ⟨k, hk⟩)
          have hai : t ≤ a i := hk ▸ het k
          rw [hy]
          linarith
        · have hy : y i = 0 := ite_eq_right hi
          rw [hy, mul_zero, sub_zero]
          exact (ha.1 i).1
      · apply (div_le_iff₀ hβ).2
        nlinarith [hgap i, mul_nonneg hα0 (hy0 i)]
    · simp only [z, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ha.2, hys, mul_one]
      exact mul_inv_cancel₀ (ne_of_gt hβ)
  have hmix : α • y + (1 - α) • z = a := by
    funext i
    change α * y i + (1 - α) * ((a i - α * y i) / (1 - α)) = a i
    field_simp
    ring
  have hconv := (convex_mean (ι := ι)).2 (mem_univ y) (mem_univ z) hα0 hβ.le
    (show α + (1 - α) = 1 by ring)
  rw [hmix] at hconv
  change mean a ≤ α * mean y + (1 - α) * mean z at hconv
  rw [hym] at hconv
  have hb := normalized_bound z hz
  have hh := mul_le_mul_of_nonneg_left hb hβ.le
  nlinarith

/-- Zero `t` needs no four-coordinate witness, so this form also covers
index types with fewer than four elements and the zero order-statistic case. -/
theorem normalized_defect_lower_bound_or_zero (a : ι → ℝ)
    (ha : a ∈ balancedPolytope) (t g : ℝ) (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hgap : ∀ i, a i ≤ 1 / 2 - g)
    (hwitness : t = 0 ∨ ∃ e : Fin 4 ↪ ι, ∀ k, t ≤ a (e k)) :
    min (t / 2) (g / 4) ≤ 1 / 2 - mean a := by
  rcases hwitness with hzero | ⟨e, he⟩
  · subst t
    have hmin : min (0 / 2 : ℝ) (g / 4) = 0 := by
      rw [zero_div, min_eq_left (by positivity)]
    rw [hmin]
    have hb := normalized_bound a ha
    linarith
  · exact normalized_defect_lower_bound a ha t g ht hg e he hgap

end Mxym.Rademacher
