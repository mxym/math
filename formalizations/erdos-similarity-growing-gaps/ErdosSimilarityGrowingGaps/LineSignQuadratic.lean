import ErdosSimilarityGrowingGaps.ParameterStrata
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ErdosSimilarityGrowingGaps


noncomputable def realizedLinePatterns (n : ℕ) (a b : Fin n → ℝ) :
    Finset (Fin n → CutSign) := by
  classical
  exact Finset.univ.filter (fun s => ∃ t : ℝ, ∀ i, cutSign (a i * t + b i) = s i)

noncomputable def lineRoots (n : ℕ) (a b : Fin n → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun i => a i ≠ 0)).image (fun i => -b i / a i)

noncomputable def rootCode (S : Finset ℝ) (x : ℝ) : ℕ := by
  classical
  exact 2 * (S.filter (fun r => r < x)).card + if x ∈ S then 1 else 0

lemma rootCode_le (S : Finset ℝ) (x : ℝ) : rootCode S x ≤ 2 * S.card := by
  classical
  have hc := Finset.card_le_card (Finset.filter_subset (fun r => r < x) S)
  by_cases hx : x ∈ S
  · have hlt : (S.filter (fun r => r < x)).card < S.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : x ∈ S.filter (fun r => r < x) := heq.symm ▸ hx
      simpa using this
    simp only [rootCode, if_pos hx]
    omega
  · simp only [rootCode, if_neg hx]
    omega

lemma rootCode_equal_parts {S : Finset ℝ} {x y : ℝ}
    (h : rootCode S x = rootCode S y) :
    (S.filter (fun r => r < x)).card = (S.filter (fun r => r < y)).card ∧
      (x ∈ S ↔ y ∈ S) := by
  classical
  unfold rootCode at h
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy] at h ⊢ <;> omega

lemma rootCode_lt_iff {S : Finset ℝ} {x y r : ℝ}
    (h : rootCode S x = rootCode S y) (hr : r ∈ S) : r < x ↔ r < y := by
  classical
  have hc := (rootCode_equal_parts h).1
  rcases le_total x y with hxy | hyx
  · have heq : S.filter (fun r => r < x) = S.filter (fun r => r < y) := by
      apply Finset.eq_of_subset_of_card_le
      · intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, lt_of_lt_of_le hs.2 hxy⟩
      · omega
    have hm : r ∈ S.filter (fun r => r < x) ↔ r ∈ S.filter (fun r => r < y) := by rw [heq]
    simpa [hr] using hm
  · have heq : S.filter (fun r => r < y) = S.filter (fun r => r < x) := by
      apply Finset.eq_of_subset_of_card_le
      · intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, lt_of_lt_of_le hs.2 hyx⟩
      · omega
    have hm : r ∈ S.filter (fun r => r < x) ↔ r ∈ S.filter (fun r => r < y) := by rw [heq]
    simpa [hr] using hm

lemma rootCode_eq_iff {S : Finset ℝ} {x y r : ℝ}
    (h : rootCode S x = rootCode S y) (hr : r ∈ S) : r = x ↔ r = y := by
  classical
  have hm := (rootCode_equal_parts h).2
  have hlt := rootCode_lt_iff h hr
  constructor
  · intro hrex
    subst x
    have hry : r ≤ y := le_of_not_gt (by intro hyr; have := (rootCode_lt_iff h.symm (hm.mp hr)).mpr hyr; exact lt_irrefl y this)
    by_contra hne
    have := hlt.mpr (lt_of_le_of_ne hry hne)
    exact lt_irrefl r this
  · intro hrey
    subst y
    have hrx : r ≤ x := le_of_not_gt (by intro hxr; have := (rootCode_lt_iff h (hm.mpr hr)).mpr hxr; exact lt_irrefl x this)
    by_contra hne
    have := hlt.mp (lt_of_le_of_ne hrx hne)
    exact lt_irrefl r this

lemma rootCode_gt_iff {S : Finset ℝ} {x y r : ℝ}
    (h : rootCode S x = rootCode S y) (hr : r ∈ S) : x < r ↔ y < r := by
  have hlt := rootCode_lt_iff h hr
  have heq := rootCode_eq_iff h hr
  constructor
  · intro hxr
    by_contra hnyr
    rcases eq_or_lt_of_le (le_of_not_gt hnyr) with hry | hry
    · have := heq.mpr hry; linarith
    · have := hlt.mpr hry; linarith
  · intro hyr
    by_contra hnxr
    rcases eq_or_lt_of_le (le_of_not_gt hnxr) with hrx | hrx
    · have := heq.mp hrx; linarith
    · have := hlt.mp hrx; linarith

lemma cutSign_of_neg {z : ℝ} (hz : z < 0) : cutSign z = .negative := by
  simp [cutSign, hz]

lemma cutSign_of_zero : cutSign 0 = .zero := by simp [cutSign]

lemma cutSign_of_pos {z : ℝ} (hz : 0 < z) : cutSign z = .positive := by
  simp [cutSign, not_lt_of_gt hz, ne_of_gt hz]

lemma affine_sign_equal_of_rootCode {S : Finset ℝ} {x y a b : ℝ}
    (h : rootCode S x = rootCode S y) (ha : a ≠ 0)
    (hr : -b / a ∈ S) : cutSign (a * x + b) = cutSign (a * y + b) := by
  let r : ℝ := -b / a
  have hrS : r ∈ S := hr
  have har : a * r + b = 0 := by dsimp [r]; field_simp; ring
  have hex : a * x + b = a * (x - r) := by nlinarith [har]
  have hey : a * y + b = a * (y - r) := by nlinarith [har]
  rw [hex, hey]
  rcases lt_or_gt_of_ne ha with ha | ha
  · rcases lt_trichotomy x r with hxr | hxr | hxr
    · have hyr := (rootCode_gt_iff h hrS).mp hxr
      rw [cutSign_of_pos (mul_pos_of_neg_of_neg ha (sub_neg.mpr hxr)),
        cutSign_of_pos (mul_pos_of_neg_of_neg ha (sub_neg.mpr hyr))]
    · have hyr : y = r := ((rootCode_eq_iff h hrS).mp hxr.symm).symm
      simp [hxr, hyr]
    · have hyr := (rootCode_lt_iff h hrS).mp hxr
      rw [cutSign_of_neg (mul_neg_of_neg_of_pos ha (sub_pos.mpr hxr)),
        cutSign_of_neg (mul_neg_of_neg_of_pos ha (sub_pos.mpr hyr))]
  · rcases lt_trichotomy x r with hxr | hxr | hxr
    · have hyr := (rootCode_gt_iff h hrS).mp hxr
      rw [cutSign_of_neg (mul_neg_of_pos_of_neg ha (sub_neg.mpr hxr)),
        cutSign_of_neg (mul_neg_of_pos_of_neg ha (sub_neg.mpr hyr))]
    · have hyr : y = r := ((rootCode_eq_iff h hrS).mp hxr.symm).symm
      simp [hxr, hyr]
    · have hyr := (rootCode_lt_iff h hrS).mp hxr
      rw [cutSign_of_pos (mul_pos ha (sub_pos.mpr hxr)),
        cutSign_of_pos (mul_pos ha (sub_pos.mpr hyr))]

lemma line_signs_equal_of_rootCode {n : ℕ} (a b : Fin n → ℝ) {x y : ℝ}
    (h : rootCode (lineRoots n a b) x = rootCode (lineRoots n a b) y) :
    (fun i => cutSign (a i * x + b i)) = (fun i => cutSign (a i * y + b i)) := by
  classical
  funext i
  by_cases ha : a i = 0
  · simp [ha]
  · apply affine_sign_equal_of_rootCode h ha
    apply Finset.mem_image.mpr
    exact ⟨i, by simp [lineRoots, ha], rfl⟩

noncomputable def rootSample (S : Finset ℝ) (k : ℕ) : ℝ := by
  classical
  exact if h : ∃ x : ℝ, rootCode S x = k then Classical.choose h else 0

lemma rootSample_spec (S : Finset ℝ) (k : ℕ) (h : ∃ x : ℝ, rootCode S x = k) :
    rootCode S (rootSample S k) = k := by
  classical
  simpa only [rootSample, dif_pos h] using Classical.choose_spec h

lemma lineRoots_card_le {n : ℕ} (a b : Fin n → ℝ) : (lineRoots n a b).card ≤ n := by
  classical
  unfold lineRoots
  calc
    _ ≤ (Finset.univ.filter (fun i => a i ≠ 0)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Every realized pattern is represented by one of at most `2*n+1` root-order cells.
No assumptions on slopes or distinctness of roots are needed. -/
theorem realizedLinePatterns_card_le (n : ℕ) (a b : Fin n → ℝ) :
    (realizedLinePatterns n a b).card ≤ 2 * n + 1 := by
  classical
  let S := lineRoots n a b
  let P : ℕ → (Fin n → CutSign) := fun k i => cutSign (a i * rootSample S k + b i)
  have hsub : realizedLinePatterns n a b ⊆ (Finset.range (2 * S.card + 1)).image P := by
    intro s hs
    simp only [realizedLinePatterns, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨t, ht⟩ := hs
    have hk : rootCode S t < 2 * S.card + 1 := by have := rootCode_le S t; omega
    refine Finset.mem_image.mpr ⟨rootCode S t, Finset.mem_range.mpr hk, ?_⟩
    have hcode : rootCode S (rootSample S (rootCode S t)) = rootCode S t :=
      rootSample_spec S (rootCode S t) ⟨t, rfl⟩
    have heq := line_signs_equal_of_rootCode a b hcode
    funext i
    exact (congrFun heq i).trans (ht i)
  have hS : S.card ≤ n := lineRoots_card_le a b
  calc
    (realizedLinePatterns n a b).card ≤ ((Finset.range (2 * S.card + 1)).image P).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (2 * S.card + 1)).card := Finset.card_image_le
    _ = 2 * S.card + 1 := Finset.card_range _
    _ ≤ 2 * n + 1 := by omega

lemma mem_realizedLinePatterns {n : ℕ} (a b : Fin n → ℝ) (t : ℝ) :
    (fun i => cutSign (a i * t + b i)) ∈ realizedLinePatterns n a b := by
  classical
  simp only [realizedLinePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t, fun i => rfl⟩

end ErdosSimilarityGrowingGaps
