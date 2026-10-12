import GaussianFour.RankOne
import GaussianNoTies

/-! Actual Gaussian pushforward and Bochner-moment transport for collinear scores. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianFour
open GaussianMeasureBridge

lemma measurableSet_scalarWinning (a p : Fin 4 → ℝ) (i : Fin 4) :
    MeasurableSet (scalarWinning a p i) := by
  unfold scalarWinning
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (by unfold scalarScore; fun_prop) (by unfold scalarScore; fun_prop)

lemma collinear_winning_preimage {d : ℕ} (u : Space d) (a p : Fin 4 → ℝ) (i : Fin 4) :
    winningCell (fun j => a j • u) p i = (fun x => ⟪u, x⟫) ⁻¹' scalarWinning a p i := by
  ext x
  simp [winningCell, scalarWinning, scalarScore, real_inner_smul_left]

/-- Actual ambient winning masses equal actual one-dimensional Gaussian masses. -/
theorem collinear_winning_mass {d : ℕ} (u : Space d) (hu : ‖u‖ = 1)
    (a p : Fin 4 → ℝ) (i : Fin 4) :
    ((gaussian d) (winningCell (fun j => a j • u) p i)).toReal =
      scalarMass (scalarWinning a p i) := by
  rw [scalarMass, ← gaussian_unit_inner_law u hu,
    Measure.map_apply (by fun_prop) (measurableSet_scalarWinning a p i),
    collinear_winning_preimage]

/-- Projection of the actual ambient Bochner moment equals the scalar moment. -/
theorem collinear_winning_moment {d : ℕ} (u : Space d) (hu : ‖u‖ = 1)
    (a p : Fin 4 → ℝ) (i : Fin 4) :
    ⟪u, ∫ x in winningCell (fun j => a j • u) p i, x ∂gaussian d⟫ =
      scalarMoment (scalarWinning a p i) := by
  have hi : IntegrableOn (fun x : Space d => x)
      (winningCell (fun j => a j • u) p i) (gaussian d) :=
    (IsGaussian.integrable_id (μ := gaussian d)).integrableOn
  rw [show ⟪u, ∫ x in winningCell (fun j => a j • u) p i, x ∂gaussian d⟫ =
      ∫ x in winningCell (fun j => a j • u) p i, ⟪u, x⟫ ∂gaussian d from
      ((innerSL ℝ u).integral_comp_comm hi).symm]
  have hs := measurableSet_scalarWinning a p i
  unfold scalarMoment
  rw [← integral_indicator hs, ← gaussian_unit_inner_law u hu]
  have hmeas : AEStronglyMeasurable ((scalarWinning a p i).indicator (fun t : ℝ => t))
      ((gaussian d).map (fun x => ⟪u, x⟫)) :=
    (show Measurable (fun t : ℝ => t) from measurable_id).indicator hs |>.aestronglyMeasurable
  rw [integral_map (by fun_prop) hmeas]
  rw [collinear_winning_preimage]
  have he : (fun x : Space d => (scalarWinning a p i).indicator (fun t : ℝ => t) ⟪u, x⟫) =
      ((fun x : Space d => ⟪u, x⟫) ⁻¹' scalarWinning a p i).indicator (fun x => ⟪u, x⟫) := by
    funext x
    by_cases hx : ⟪u, x⟫ ∈ scalarWinning a p i <;> simp [hx]
  rw [he, integral_indicator (hs.preimage (by fun_prop))]

/-- In every dimension, an ordered collinear balanced self-moment diagram violates
the centered spectral bound. Masses and moments are actual ambient Gaussian data. -/
theorem no_ordered_collinear_selfMoment_spectral_bound {d : ℕ}
    (u : Space d) (hu : ‖u‖ = 1) (a p : Fin 4 → ℝ) (ha : StrictMono a)
    (hm : ∀ i, ((gaussian d) (winningCell (fun j => a j • u) p i)).toReal = 1 / 4)
    (hself : ∀ i, a i • u = ∫ x in winningCell (fun j => a j • u) p i, x ∂gaussian d) :
    ¬ (∀ z : Fin 4 → ℝ, (∑ i, z i) = 0 → scalarFacetForm a p z ≤ ∑ i, z i ^ 2) := by
  apply no_ordered_scalar_selfMoment_spectral_bound ha
  · intro i
    rw [← collinear_winning_mass u hu a p i]
    exact hm i
  · intro i
    have hi := congrArg (fun v : Space d => ⟪u, v⟫) (hself i)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu] at hi
    norm_num only [one_pow, mul_one] at hi
    exact hi.trans (collinear_winning_moment u hu a p i)

end GaussianFour
