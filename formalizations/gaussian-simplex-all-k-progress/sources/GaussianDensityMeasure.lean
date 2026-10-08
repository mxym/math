import GaussianLebesgueDensity

/-! The actual Euclidean standard Gaussian is Lebesgue measure with the
explicit positive density. The identities here concern the actual measure,
including the zero-dimensional case; no density representation is assumed. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped ENNReal RealInnerProductSpace
namespace GaussianMeasureBridge

lemma map_withDensity_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable), withDensity_apply _ hs,
    e.restrict_map, e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]

lemma gaussian_pi_density (d : ℕ) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, standardDensity (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : Fin d → ℝ => ∏ i, standardDensity (x i))
      (volume.restrict (univ.pi s)) := by
    exact (Integrable.fintype_prod (fun _ : Fin d =>
      (integrable_gaussianPDFReal 0 1))).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => (standardDensity_pos (x i)).le)))]
  change ENNReal.ofReal (∫ x, ∏ i, standardDensity (x i)
    ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg (fun x => (standardDensity_pos x).le))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num) (s i)).symm

theorem gaussian_eq_volume_withDensity (d : ℕ) :
    gaussian d = (volume : Measure (Space d)).withDensity
      (fun x => ENNReal.ofReal (gaussianLebesgueDensity d x)) := by
  rw [← (gaussian_toLp_preserving d).map_eq, gaussian_pi_density]
  change Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) _ = _
  rw [map_withDensity_measurableEquiv (MeasurableEquiv.toLp 2 (Fin d → ℝ))]
  simp only [MeasurableEquiv.coe_toLp]
  rw [(PiLp.volume_preserving_toLp (Fin d)).map_eq]
  congr 1
  funext x
  congr 1
  exact gaussianLebesgueDensity_product x

theorem gaussian_integral_density {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space d → E) :
    (∫ x, f x ∂gaussian d) = ∫ x, gaussianLebesgueDensity d x • f x := by
  rw [gaussian_eq_volume_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      (gaussianLebesgueDensity_contDiff d).continuous.measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianLebesgueDensity_pos _).le]

theorem gaussian_integrable_density_iff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space d → E) :
    Integrable f (gaussian d) ↔ Integrable (fun x => gaussianLebesgueDensity d x • f x) := by
  rw [gaussian_eq_volume_withDensity,
    integrable_withDensity_iff_integrable_smul'
      (gaussianLebesgueDensity_contDiff d).continuous.measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianLebesgueDensity_pos _).le]

end GaussianMeasureBridge
