import Entry005.TruncationFormalization
open Entry005
example : truncationSharpnessGoal := truncationSharpness
example {d : ℕ} (hd : 3 ≤ d) (α : ℝ) (hα : 1 / ((d - 1 : ℕ) : ℝ) < α)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < min ε 1 ∧
      ∃ K : ConvexBody (Space d), (K : Set (Space d)) = truncationSet d t ∧
        (interior (K : Set (Space d))).Nonempty ∧
        ∃ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S ∧
          0 < entryDefect (K : Set (Space d)) ∧
          entryDefect (K : Set (Space d)) < ε ∧
          C * (entryDefect (K : Set (Space d))) ^ α < excess (K : Set (Space d)) S :=
  truncationSharpness d hd α hα C ε hC hε
example {d : ℕ} (hd : 0 < d) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : Fin d)
    (T : Affine.Simplex ℝ (Space d) d)
    (hT : simplexSet T ⊆ truncationSet d t) :
    MeasureTheory.volume (simplexSet T) ≤
      MeasureTheory.volume (simplexSet (truncationSimplex t i (ne_of_lt ht1))) :=
  (truncationSimplex_maximumInscribed hd t ht0 ht1 i).2 T hT
