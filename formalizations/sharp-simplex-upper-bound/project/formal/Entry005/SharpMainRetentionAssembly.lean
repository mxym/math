import Entry005.ActualFiniteEnclosingRadialCap
import Entry005.HausdorffRetention

noncomputable section
open Metric MeasureTheory
namespace Entry005

theorem original_cap_radius_retention_gate {d : ℕ} (hd : 2 ≤ d)
    (e : ℝ) (he : 0 ≤ e) (hsmall : e ≤ eSharp d) :
    (d : ℝ) * (L d * (J d * (Q d * (d + 1) * e)) ^
      (1 / ((d - 1 : ℕ) : ℝ))) ≤ 1 / 8 := by
  let rho : ℝ := L d * (J d * (Q d * (d + 1) * e)) ^
    (1 / ((d - 1 : ℕ) : ℝ))
  have hd1 : 1 ≤ d := by omega
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    have := L_pos hd
    have := J_pos hd1
    have := Q_pos hd1
    positivity
  have hlocal := original_local_cap_to_excess_scalar hd (4 * M d * d * rho) rho e he
    (by rfl) le_rfl
  have hpow := Real.rpow_le_rpow he hsmall
    (show 0 ≤ 1 / ((d - 1 : ℕ) : ℝ) by positivity)
  have hscaled : 4 * M d * d * rho ≤ 1 / 2 :=
    hlocal.trans ((mul_le_mul_of_nonneg_left hpow (aSharp_pos hd).le).trans
      (original_sharp_threshold hd))
  have hM := original_one_le_M hd1
  have hdR : 0 ≤ (d : ℝ) := by positivity
  nlinarith

/-- The actual cap bound retains every supplied maximum simplex and its
centroid. This consumes an enclosing genuine simplex, not a preferred maximum. -/
theorem normalized_maximum_simplex_excess_of_original_cap {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hPM : simplexSet P ⊆ closedBall (0 : Space d) (M d))
    (hcentroid : S.centroid = 0) (hbS : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (e : ℝ) (he : 0 ≤ e) (hsmall : e ≤ eSharp d)
    (hcap : hausdorffDist (K : Set (Space d)) (simplexSet P) ≤
      L d * (J d * (Q d * (d + 1) * e)) ^ (1 / ((d - 1 : ℕ) : ℝ))) :
    excess (K : Set (Space d)) S ≤ aSharp d * e ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  let rho : ℝ := L d * (J d * (Q d * (d + 1) * e)) ^
    (1 / ((d - 1 : ℕ) : ℝ))
  have hd1 : 1 ≤ d := by omega
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    have := L_pos hd
    have := J_pos hd1
    have := Q_pos hd1
    positivity
  have hvertices : ∀ i, ‖P.points i - S.centroid‖ ≤ M d := by
    intro i
    have hx := hPM (subset_convexHull ℝ (Set.range P.points) ⟨i, rfl⟩)
    simpa only [hcentroid, sub_zero, mem_closedBall, dist_zero_right] using hx
  have hball : closedBall S.centroid 1 ⊆ simplexSet S := by rwa [hcentroid]
  have hretain := excess_of_hausdorff_at_centroid hd1 K P S (M d) rho hmax hKP
    hvertices hball hrho (original_cap_radius_retention_gate hd e he hsmall) hcap
  have hnonneg : 0 ≤ M d * d * rho := by have := M_pos hd1; positivity
  have hretain4 : excess (K : Set (Space d)) S ≤ 4 * M d * d * rho := by nlinarith
  exact original_local_cap_to_excess_scalar hd _ rho e he (by rfl) hretain4

end Entry005
