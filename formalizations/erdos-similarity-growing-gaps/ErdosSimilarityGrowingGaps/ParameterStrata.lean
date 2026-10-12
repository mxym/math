import Mathlib.Data.Finset.Card
import ErdosSimilarityGrowingGaps.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

namespace ErdosSimilarityGrowingGaps

/-! A finite, boundary-complete parameter cover.  The cover keeps the zero
    stratum, so activation and grid-boundary equalities are represented rather
    than silently discarded.  The quadratic refinement used by the paper can
    be added on top of this exact finite cover. -/

inductive CutSign where
  | negative
  | zero
  | positive
  deriving DecidableEq

instance : Fintype CutSign where
  elems := {.negative, .zero, .positive}
  complete := by intro s; cases s <;> simp

abbrev AffineCut := ℝ × ℝ × ℝ

def evalCut (c : AffineCut) (p : ℝ × ℝ) : ℝ :=
  c.1 * p.1 + c.2.1 * p.2 + c.2.2

noncomputable def cutSign (x : ℝ) : CutSign :=
  if x < 0 then .negative else if x = 0 then .zero else .positive

def inRectangle (lo hi p : ℝ × ℝ) : Prop :=
  lo.1 ≤ p.1 ∧ p.1 ≤ hi.1 ∧ lo.2 ≤ p.2 ∧ p.2 ≤ hi.2

theorem finite_parameter_representatives (m : ℕ)
    (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ) :
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧
      reps.card ≤ 3 ^ m ∧
      ∀ p : ℝ × ℝ, inRectangle lo hi p →
        ∃ r ∈ reps, ∀ i : Fin m,
          cutSign (evalCut (cuts i) r) = cutSign (evalCut (cuts i) p) := by
  classical
  let patterns : Finset (Fin m → CutSign) := Finset.univ.filter (fun s =>
    ∃ p : ℝ × ℝ, inRectangle lo hi p ∧
      ∀ i, cutSign (evalCut (cuts i) p) = s i)
  have hpatterns : ∀ s ∈ patterns, ∃ p : ℝ × ℝ,
      inRectangle lo hi p ∧ ∀ i, cutSign (evalCut (cuts i) p) = s i := by
    intro s hs
    simpa only [patterns, Finset.mem_filter, Finset.mem_univ, true_and] using hs
  let pick : {s // s ∈ patterns} → ℝ × ℝ := fun s =>
    Classical.choose (hpatterns s.1 s.2)
  have hpick : ∀ s : {s // s ∈ patterns},
      inRectangle lo hi (pick s) ∧
        ∀ i, cutSign (evalCut (cuts i) (pick s)) = s.1 i := fun s =>
    Classical.choose_spec (hpatterns s.1 s.2)
  let reps : Finset (ℝ × ℝ) := patterns.attach.image pick
  have hsub : patterns ⊆ (Finset.univ : Finset (Fin m → CutSign)) := by
    exact Finset.subset_univ patterns
  refine ⟨reps, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hpick s).1
  · calc
      reps.card ≤ patterns.attach.card := Finset.card_image_le
      _ = patterns.card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (Fin m → CutSign)).card :=
        Finset.card_le_card hsub
      _ = 3 ^ m := by
        have hc : Fintype.card CutSign = 3 := by decide
        simp [hc]
  · intro p hp
    let s : Fin m → CutSign := fun i => cutSign (evalCut (cuts i) p)
    have hs : s ∈ patterns := by
      simp only [patterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, fun _ => rfl⟩
    refine ⟨pick ⟨s, hs⟩, Finset.mem_image.mpr
      ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    intro i
    exact (hpick ⟨s, hs⟩).2 i

theorem finite_parameter_representatives_nonempty
    (m : ℕ) (_cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ)
    (hlo : lo.1 ≤ hi.1) (hhi : lo.2 ≤ hi.2) :
    ∃ r : ℝ × ℝ, inRectangle lo hi r := by
  exact ⟨lo, le_rfl, hlo, le_rfl, hhi⟩

end ErdosSimilarityGrowingGaps
