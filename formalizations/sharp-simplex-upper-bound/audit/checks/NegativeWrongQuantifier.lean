import Entry005.SharpUpperMain
open Entry005
noncomputable def WrongExistsGoal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
    (interior (K : Set (Space d))).Nonempty →
      ∃ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S ∧
        excess (K : Set (Space d)) S ≤
          gSharp d * (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ))
example (h : WrongExistsGoal) : sharpMainGoal := h
