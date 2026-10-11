import ErdosSimilarityGrowingGaps.Sampling
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

open Filter

/-- The first index whose logarithm reaches a prescribed threshold. -/
noncomputable def firstGeIndex (Z : LogScale) (v : ℝ) : ℕ :=
  Classical.choose (exists_first_ge Z v)

theorem firstGeIndex_spec (Z : LogScale) (v : ℝ) :
    v ≤ Z.z (firstGeIndex Z v) ∧
      ∀ m : ℕ, m < firstGeIndex Z v → Z.z m < v := by
  exact Classical.choose_spec (exists_first_ge Z v)

theorem firstGeIndex_le_of_mem
    (Z : LogScale) (v : ℝ) (n : ℕ) (hn : v ≤ Z.z n) :
    firstGeIndex Z v ≤ n := by
  by_contra h
  have hlt : n < firstGeIndex Z v := Nat.lt_of_not_ge h
  exact (not_lt_of_ge hn) ((firstGeIndex_spec Z v).2 n hlt)

theorem firstGeIndex_value_le_of_mem
    (Z : LogScale) (v D : ℝ) (n : ℕ)
    (hn : v ≤ Z.z n ∧ Z.z n ≤ v + D) :
    Z.z (firstGeIndex Z v) ≤ v + D := by
  have hi := firstGeIndex_le_of_mem Z v n hn.1
  exact (Z.strictMono.monotone hi).trans hn.2

/-- Greedy logarithmic samples: the first sample reaches the annulus anchor,
    and each later sample starts after the preceding selected logarithm plus
    the prescribed separation. -/
noncomputable def greedyIndex (Z : LogScale) (v δ : ℝ) : ℕ → ℕ
  | 0 => firstGeIndex Z v
  | i + 1 => firstGeIndex Z (Z.z (greedyIndex Z v δ i) + δ)

theorem greedyIndex_zero (Z : LogScale) (v δ : ℝ) :
    greedyIndex Z v δ 0 = firstGeIndex Z v := rfl

theorem greedyIndex_succ (Z : LogScale) (v δ : ℝ) (i : ℕ) :
    greedyIndex Z v δ (i + 1) =
      firstGeIndex Z (Z.z (greedyIndex Z v δ i) + δ) := rfl

theorem greedyIndex_log_gap_ge
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) (i : ℕ) :
    Z.z (greedyIndex Z v δ i) + δ ≤
      Z.z (greedyIndex Z v δ (i + 1)) := by
  rw [greedyIndex_succ]
  exact (firstGeIndex_spec Z (Z.z (greedyIndex Z v δ i) + δ)).1

theorem greedyIndex_strictMono
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) :
    StrictMono (greedyIndex Z v δ) := by
  intro i j hij
  have hlog : Z.z (greedyIndex Z v δ i) < Z.z (greedyIndex Z v δ j) := by
    induction hij with
    | refl => linarith [greedyIndex_log_gap_ge Z v δ hδ i]
    | @step j hij ih =>
      exact lt_of_lt_of_le ih (by linarith [greedyIndex_log_gap_ge Z v δ hδ j])
  exact (Z.strictMono.lt_iff_lt).mp hlog

theorem greedyIndex_first_log_ge
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) (i : ℕ) :
    v ≤ Z.z (greedyIndex Z v δ i) := by
  induction i with
  | zero => exact (firstGeIndex_spec Z v).1
  | succ i ih =>
      exact le_trans ih (by linarith [greedyIndex_log_gap_ge Z v δ hδ i])

theorem greedyIndex_log_gap_between
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) {i j : ℕ} (hij : i < j) :
    Z.z (greedyIndex Z v δ i) + δ ≤ Z.z (greedyIndex Z v δ j) := by
  have hsucc : i + 1 ≤ j := Nat.succ_le_of_lt hij
  exact (greedyIndex_log_gap_ge Z v δ hδ i).trans
    (Z.strictMono.monotone ((greedyIndex_strictMono Z v δ hδ).monotone hsucc))

theorem greedyIndex_injective
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) :
    Function.Injective (greedyIndex Z v δ) :=
  (greedyIndex_strictMono Z v δ hδ).injective

theorem greedyIndex_anchor_of_filling
    {Z : LogScale} {U R D v δ : ℝ}
    (hfill : FillsAnnulus Z U R D) (hδ : 0 < δ)
    (hanchor_lo : U / R ≤ v) (hanchor_hi : v + D ≤ R * U) :
    U / R ≤ Z.z (greedyIndex Z v δ 0) ∧
      Z.z (greedyIndex Z v δ 0) ≤ v + D := by
  rw [greedyIndex_zero]
  obtain ⟨n, hnlo, hnhi⟩ := hfill.sample_mem hanchor_lo hanchor_hi
  refine ⟨hanchor_lo.trans (firstGeIndex_spec Z v).1, ?_⟩
  exact firstGeIndex_value_le_of_mem Z v D n ⟨hnlo, hnhi⟩

theorem greedyIndex_log_gap_le_of_filling
    {Z : LogScale} {U R D v δ : ℝ}
    (hfill : FillsAnnulus Z U R D)
    (hδ : 0 < δ) (i : ℕ)
    (hlo : U / R ≤ Z.z (greedyIndex Z v δ i))
    (hhi : Z.z (greedyIndex Z v δ i) + δ + D ≤ R * U) :
    Z.z (greedyIndex Z v δ (i + 1)) ≤
      Z.z (greedyIndex Z v δ i) + δ + D := by
  let w := Z.z (greedyIndex Z v δ i) + δ
  have hwlo : U / R ≤ w := by linarith
  have hwhi : w + D ≤ R * U := by simpa [w] using hhi
  obtain ⟨n, hnlo, hnhi⟩ := hfill.sample_mem hwlo hwhi
  exact firstGeIndex_value_le_of_mem Z w D n ⟨hnlo, hnhi⟩

theorem greedyIndex_log_gap_lt_of_filling
    {Z : LogScale} {U R D v δ : ℝ}
    (hfill : FillsAnnulus Z U R D)
    (hδ : 0 < δ) (i : ℕ)
    (hlo : U / R ≤ Z.z (greedyIndex Z v δ i))
    (hhi : Z.z (greedyIndex Z v δ i) + δ + D ≤ R * U) :
    δ ≤ Z.z (greedyIndex Z v δ (i + 1)) -
      Z.z (greedyIndex Z v δ i) ∧
    Z.z (greedyIndex Z v δ (i + 1)) -
      Z.z (greedyIndex Z v δ i) ≤ δ + D := by
  constructor
  · linarith [greedyIndex_log_gap_ge Z v δ hδ i]
  · linarith [greedyIndex_log_gap_le_of_filling hfill hδ i hlo hhi]

end ErdosSimilarityGrowingGaps
