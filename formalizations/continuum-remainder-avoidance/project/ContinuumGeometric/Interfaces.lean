import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card

/-!
Precise independent parallel task: quadratic, boundary-complete sign
representatives for finitely many affine cuts on a closed rectangle.
Only the specification is defined; no unproved theorem or axiom is declared.
-/
namespace ContinuumGeometric

/-- All three signs must be retained, in particular exact zero strata. -/
inductive CutSign where
  | negative | zero | positive
  deriving DecidableEq

noncomputable def cutSign (x : ℝ) : CutSign :=
  if x < 0 then .negative else if x = 0 then .zero else .positive

abbrev AffineCut := ℝ × ℝ × ℝ

def evalCut (c : AffineCut) (p : ℝ × ℝ) : ℝ :=
  c.1 * p.1 + c.2.1 * p.2 + c.2.2

def inRectangle (lo hi p : ℝ × ℝ) : Prop :=
  lo.1 ≤ p.1 ∧ p.1 ≤ hi.1 ∧ lo.2 ≤ p.2 ∧ p.2 ≤ hi.2

/-- OPEN obligation, proposed for a separate Lean task.
Identically zero, coincident and parallel cuts, degenerate rectangles,
boundary vertices and all lower-dimensional strata are included.
The polynomial cardinal bound is essential; the trivial `3^m` bound is
insufficient for the continuum probability budget.
-/
def ArrangementRepresentativeBound : Prop :=
  ∀ (m : ℕ) (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ),
    lo.1 ≤ hi.1 → lo.2 ≤ hi.2 →
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧
      reps.card ≤ 20 * (m + 5) ^ 2 ∧
      ∀ p : ℝ × ℝ, inRectangle lo hi p →
        ∃ r ∈ reps, ∀ i : Fin m,
          cutSign (evalCut (cuts i) r) = cutSign (evalCut (cuts i) p)

end ContinuumGeometric
