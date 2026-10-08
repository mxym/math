import Entry005.SharpUpperMain
import Entry005.MainTarget
open Entry005 MeasureTheory
example : sharpMainGoal := sharpMain
example : MainTarget := sharpMain
example : sharpLocalGoal := sharpLocal
example : ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
    (interior (K : Set (Space d))).Nonempty →
    ∀ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S →
      excess (K : Set (Space d)) S ≤
        gSharp d * (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ)) := sharpMain
example : ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
    (interior (K : Set (Space d))).Nonempty →
    ∀ S : Affine.Simplex ℝ (Space d) d,
      (convexHull ℝ (Set.range S.points) ⊆ K ∧
       ∀ T : Affine.Simplex ℝ (Space d) d,
         convexHull ℝ (Set.range T.points) ⊆ K →
         volume (convexHull ℝ (Set.range T.points)) ≤ volume (convexHull ℝ (Set.range S.points))) →
      sInf {t : ℝ | 0 ≤ t ∧ (K : Set (Space d)) ⊆
        (fun x => S.centroid + (1 + t) • (x - S.centroid)) ''
          convexHull ℝ (Set.range S.points)} ≤
        gSharp d * (entryA (K : Set (Space d)) - 1 / (Module.finrank ℝ (Space d) + 1)) ^
          (1 / ((d - 1 : ℕ) : ℝ)) := sharpMain
example (d : ℕ) (hd : 3 ≤ d) (K : ConvexBody (Space d))
    (hK : (interior (K : Set (Space d))).Nonempty)
    (S : Affine.Simplex ℝ (Space d) d) (hS : maximumInscribed K S) :
    excess (K : Set (Space d)) S ≤ gSharp d *
      ((((d : ℝ) / ((d : ℝ) + 1)) ^ d *
          projectionRatio (pyramidSet (K : Set (Space d))) /
            projectionRatio (K : Set (Space d)) - 1 - 1 / ((d : ℝ) + 1)) ^
        (1 / ((d - 1 : ℕ) : ℝ))) := by
  simpa only [entryDefect, entryA, Space, finrank_euclideanSpace_fin] using
    sharpMain d hd K hK S hS
example (d : ℕ) : gSharp d = max (aSharp d)
    ((R0 d - 1) * (eSharp d) ^ (-(1 / ((d - 1 : ℕ) : ℝ)))) := rfl
example (d : ℕ) : Q d = (d + 1) * (d + 2) * (8 : ℝ)^d * M d ^ (4*d) := rfl
example (d : ℕ) : J d = (d : ℝ) / 2 * (2 * R0 d)^d *
    (1 + M d + (d : ℝ) * 2^(d-1) * M d) := rfl
