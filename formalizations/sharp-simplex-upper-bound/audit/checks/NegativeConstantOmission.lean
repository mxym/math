import Entry005.SharpUpperMain
open Entry005
example (d : ℕ) (hd : 3 ≤ d) (K : ConvexBody (Space d))
    (hK : (interior (K : Set (Space d))).Nonempty)
    (S : Affine.Simplex ℝ (Space d) d) (hS : maximumInscribed K S) :
    excess (K : Set (Space d)) S ≤ (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ)) :=
  sharpMain d hd K hK S hS
