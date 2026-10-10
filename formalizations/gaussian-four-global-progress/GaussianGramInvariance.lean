import GaussianHomogeneity

/-! Actual Gaussian score laws depend only on the Gram matrix, including
singular matrices and different ambient dimensions. This also proves score-
value invariance under isometric embeddings (cylindrical extension). -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianFourGlobal
open GaussianMeasureBridge

noncomputable def scoreMap {d : ℕ} (v : Fin 4 → Space d) : Space d →L[ℝ] Space 4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (v i)))

@[simp] lemma scoreMap_apply {d : ℕ} (v : Fin 4 → Space d) (x : Space d) (i : Fin 4) :
    scoreMap v x i = ⟪v i, x⟫ := rfl

noncomputable def scoreLaw {d : ℕ} (v : Fin 4 → Space d) : Measure (Space 4) :=
  (gaussian d).map (scoreMap v)

lemma scoreMap_inner {d : ℕ} (v : Fin 4 → Space d) (x : Space d) (t : Space 4) :
    ⟪scoreMap v x, t⟫ = ⟪∑ i, t i • v i, x⟫ := by
  rw [sum_inner, PiLp.inner_apply]
  simp only [scoreMap_apply, Real.inner_apply, real_inner_smul_left, mul_comm]

lemma gaussian_inner_law {d : ℕ} (u : Space d) :
    (gaussian d).map (fun x => ⟪u, x⟫) = gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
  change (gaussian d).map (innerSL ℝ u) = _
  rw [IsGaussian.map_eq_gaussianReal, gaussian, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

lemma norm_sum_smul_sq_of_gram_eq {d e : ℕ} (v : Fin 4 → Space d) (w : Fin 4 → Space e)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (c : Fin 4 → ℝ) :
    ‖∑ i, c i • v i‖ ^ 2 = ‖∑ i, c i • w i‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, hgram]

/-- Equality of actual Gaussian score distributions from equality of Gram
matrices. No nonsingularity or distinctness hypothesis is required. -/
theorem scoreLaw_eq_of_gram_eq {d e : ℕ} (v : Fin 4 → Space d) (w : Fin 4 → Space e)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) : scoreLaw v = scoreLaw w := by
  haveI : IsFiniteMeasure (scoreLaw v) := by unfold scoreLaw; infer_instance
  haveI : IsFiniteMeasure (scoreLaw w) := by unfold scoreLaw; infer_instance
  apply Measure.ext_of_charFun
  ext t
  unfold scoreLaw
  rw [charFun_map_eq_charFun_map_inner_one (show AEMeasurable (scoreMap v) (gaussian d) from by fun_prop) t,
    charFun_map_eq_charFun_map_inner_one (show AEMeasurable (scoreMap w) (gaussian e) from by fun_prop) t]
  simp only [scoreMap_inner]
  rw [gaussian_inner_law, gaussian_inner_law, norm_sum_smul_sq_of_gram_eq v w hgram]

noncomputable def coordinateMax (b : Fin 4 → ℝ) (y : Space 4) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => y i - b i)

lemma continuous_coordinateMax (b : Fin 4 → ℝ) : Continuous (coordinateMax b) :=
  Continuous.finset_sup'_apply _ (fun i _ => by fun_prop)

lemma expectedScore_eq_scoreLaw_integral {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ) :
    expectedScore v b = ∫ y, coordinateMax b y ∂scoreLaw v := by
  rw [scoreLaw, integral_map (by fun_prop) (continuous_coordinateMax b).measurable.aestronglyMeasurable]
  rfl

theorem expectedScore_eq_of_gram_eq {d e : ℕ} (v : Fin 4 → Space d) (w : Fin 4 → Space e)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (b : Fin 4 → ℝ) :
    expectedScore v b = expectedScore w b := by
  rw [expectedScore_eq_scoreLaw_integral, expectedScore_eq_scoreLaw_integral,
    scoreLaw_eq_of_gram_eq v w hgram]

theorem priceObjective_eq_of_gram_eq {d e : ℕ} (v : Fin 4 → Space d) (w : Fin 4 → Space e)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (p b : Fin 4 → ℝ) :
    priceObjective v p b = priceObjective w p b := by
  simp only [priceObjective, expectedScore_eq_of_gram_eq v w hgram b]

/-- The actual optimized assignment value is a Gram-matrix invariant. -/
theorem balancedValue_eq_of_gram_eq {d e : ℕ} (v : Fin 4 → Space d) (w : Fin 4 → Space e)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) : balancedValue v = balancedValue w := by
  unfold balancedValue
  have he : priceObjective v (fun _ => 1 / 4) = priceObjective w (fun _ => 1 / 4) := by
    funext b
    exact priceObjective_eq_of_gram_eq v w hgram _ b
  rw [he]

/-- Orthogonal transformations and cylindrical extension leave the actual
balanced assignment value unchanged. The embedding need not be surjective. -/
theorem balancedValue_isometric_embedding {d e : ℕ} (v : Fin 4 → Space d)
    (u : Space d →ₗᵢ[ℝ] Space e) : balancedValue (fun i => u (v i)) = balancedValue v := by
  apply balancedValue_eq_of_gram_eq
  intro i j
  exact u.inner_map_map (v i) (v j)

end GaussianFourGlobal