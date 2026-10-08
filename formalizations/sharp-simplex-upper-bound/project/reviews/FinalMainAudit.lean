import Entry005.SharpUpperMain
import Entry005.MainTarget

noncomputable section
open Metric MeasureTheory

#check Entry005.original_cap_radius_retention_gate
#print axioms Entry005.original_cap_radius_retention_gate
#check Entry005.normalized_maximum_simplex_excess_of_original_cap
#print axioms Entry005.normalized_maximum_simplex_excess_of_original_cap
#check Entry005.normalized_sharp_upper_local
#print axioms Entry005.normalized_sharp_upper_local
#check Entry005.sharpLocal
#print axioms Entry005.sharpLocal
#check Entry005.actual_entryDefect_nonnegative_of_prescribed_maximum
#print axioms Entry005.actual_entryDefect_nonnegative_of_prescribed_maximum
#check Entry005.sharpMain
#print axioms Entry005.sharpMain
#check Entry005.MainTarget
#print axioms Entry005.MainTarget

namespace Entry005.FinalMainIndependentReview

theorem original_goal : sharpMainGoal := sharpMain
theorem named_target : MainTarget := sharpMain
theorem original_local_goal : sharpLocalGoal := sharpLocal

theorem literal_original_centroid
    (d : ℕ) (hd : 3 ≤ d) (K : ConvexBody (Space d))
    (hK : (interior (K : Set (Space d))).Nonempty)
    (S : Affine.Simplex ℝ (Space d) d) (hS : maximumInscribed K S) :
    sInf {t : ℝ | 0 ≤ t ∧ (K : Set (Space d)) ⊆
      (fun x => S.centroid + (1 + t) • (x - S.centroid)) ''
        convexHull ℝ (Set.range S.points)} ≤
      gSharp d * (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  simpa only [excess, centeredDilation, simplexSet] using sharpMain d hd K hK S hS

theorem literal_actual_defect
    (d : ℕ) (hd : 3 ≤ d) (K : ConvexBody (Space d))
    (hK : (interior (K : Set (Space d))).Nonempty)
    (S : Affine.Simplex ℝ (Space d) d) (hS : maximumInscribed K S) :
    excess (K : Set (Space d)) S ≤ gSharp d *
      ((((d : ℝ) / ((d : ℝ) + 1)) ^ d *
          projectionRatio (pyramidSet (K : Set (Space d))) /
            projectionRatio (K : Set (Space d)) - 1 - 1 / ((d : ℝ) + 1)) ^
        (1 / ((d - 1 : ℕ) : ℝ))) := by
  simpa only [entryDefect, entryA, Space, finrank_euclideanSpace_fin] using
    sharpMain d hd K hK S hS

end Entry005.FinalMainIndependentReview

#check Entry005.FinalMainIndependentReview.original_goal
#print axioms Entry005.FinalMainIndependentReview.original_goal
#check Entry005.FinalMainIndependentReview.named_target
#print axioms Entry005.FinalMainIndependentReview.named_target
#check Entry005.FinalMainIndependentReview.original_local_goal
#print axioms Entry005.FinalMainIndependentReview.original_local_goal
#check Entry005.FinalMainIndependentReview.literal_original_centroid
#print axioms Entry005.FinalMainIndependentReview.literal_original_centroid
#check Entry005.FinalMainIndependentReview.literal_actual_defect
#print axioms Entry005.FinalMainIndependentReview.literal_actual_defect
