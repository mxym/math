import GaussianFour.OrderedWinning

/-! The ordered rank-one obstruction uses actual Gaussian cell masses and moments.
The facet weights are the one-dimensional Gaussian boundary density divided
by the difference of adjacent inducing slopes. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianFour
open GaussianMeasureBridge

/-- Balanced affine winning cells have these exact actual first moments. -/
theorem balanced_scalar_moments {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (hm : ∀ i, scalarMass (scalarWinning a p i) = 1 / 4) :
    (fun i => scalarMoment (scalarWinning a p i)) =
    ![-quarterDensity, quarterDensity - standardDensity 0,
      standardDensity 0 - quarterDensity, quarterDensity] := by
  obtain ⟨h01, h12⟩ := balanced_adjacentCuts_strict ha hm
  obtain ⟨h0, h1, h2⟩ := balanced_scalar_cut_quartiles ha hm
  funext i
  rw [scalarWinning_eq_intervals ha h01 h12, h0, h1, h2, openIntervalCells_moment]
  exact congrFun quartile_interval_moments i

noncomputable def scalarFacetWeight (a p : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  standardDensity (adjacentCut a p i) / (a i.succ - a i.castSucc)

noncomputable def scalarFacetForm (a p z : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, scalarFacetWeight a p i * (z i.succ - z i.castSucc) ^ 2

lemma scalarFacetWeight_pos {a p : Fin 4 → ℝ} (ha : StrictMono a) (i : Fin 3) :
    0 < scalarFacetWeight a p i := by
  apply div_pos (standardDensity_pos _)
  exact sub_pos.mpr (ha (by change i.val < i.val + 1; omega))

/-- The middle interface of a balanced self-moment diagram has weight greater than two. -/
theorem balanced_selfMoment_middle_weight_gt_two {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (hm : ∀ i, scalarMass (scalarWinning a p i) = 1 / 4)
    (hself : ∀ i, a i = scalarMoment (scalarWinning a p i)) :
    2 < scalarFacetWeight a p 1 := by
  have hs := (funext hself).trans (balanced_scalar_moments ha hm)
  have hs1 : a 1 = quarterDensity - standardDensity 0 := congrFun hs 1
  have hs2 : a 2 = standardDensity 0 - quarterDensity := congrFun hs 2
  have hc := (balanced_scalar_cut_quartiles ha hm).2.1
  unfold scalarFacetWeight
  rw [hc]
  change 2 < standardDensity 0 / (a 2 - a 1)
  rw [hs1, hs2]
  have hd : 0 < standardDensity 0 - quarterDensity - (quarterDensity - standardDensity 0) := by
    linarith [quarterDensity_lt_center]
  apply (lt_div_iff₀ hd).2
  nlinarith [quarterDensity_gt_three_quarters]

/-- No ordered balanced Gaussian self-moment diagram satisfies the required
L ≤ P spectral quadratic-form inequality on the centered score subspace. -/
theorem no_ordered_scalar_selfMoment_spectral_bound {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (hm : ∀ i, scalarMass (scalarWinning a p i) = 1 / 4)
    (hself : ∀ i, a i = scalarMoment (scalarWinning a p i)) :
    ¬ (∀ z : Fin 4 → ℝ, (∑ i, z i) = 0 → scalarFacetForm a p z ≤ ∑ i, z i ^ 2) := by
  intro hbound
  let z : Fin 4 → ℝ := ![0, 1, -1, 0]
  have hz : (∑ i, z i) = 0 := by norm_num [z, Fin.sum_univ_succ]
  have hb := hbound z hz
  norm_num [scalarFacetForm, z, Fin.sum_univ_succ] at hb
  have hm1 := balanced_selfMoment_middle_weight_gt_two ha hm hself
  have hw0 := scalarFacetWeight_pos (p := p) ha 0
  have hw2 := scalarFacetWeight_pos (p := p) ha 2
  nlinarith

end GaussianFour
