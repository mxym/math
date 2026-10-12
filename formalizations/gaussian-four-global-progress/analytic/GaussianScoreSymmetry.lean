import GaussianCovarianceValue

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma expectedScore_eq_of_gram_eq {e : ℕ} (v : Fin k → Space d) (w : Fin k → Space e)
    (h : scoreGram v = scoreGram w) (b : Fin k → ℝ) :
    expectedScore v b = expectedScore w b := by
  have he (v : Fin k → Space d) : expectedScore v b =
      ∫ y, coordinateMax b y ∂multivariateGaussian 0 (scoreGram v) := by
    rw [← scoreMap_gaussian_law v, integral_map
      (scoreMap v).continuous.measurable.aemeasurable
      (continuous_coordinateMax b).aestronglyMeasurable]
    rfl
  rw [he v, h, ← scoreMap_gaussian_law w, integral_map
    (scoreMap w).continuous.measurable.aemeasurable
    (continuous_coordinateMax b).aestronglyMeasurable]
  rfl

lemma scoreMax_reindex (v : Fin k → Space d) (b : Fin k → ℝ)
    (e : Equiv.Perm (Fin k)) (x : Space d) :
    scoreMax (v ∘ e) (b ∘ e) x = scoreMax v b x := by
  apply le_antisymm
  · unfold scoreMax
    exact Finset.sup'_le _ _ fun i _ => le_scoreMax v b x (e i)
  · unfold scoreMax
    refine Finset.sup'_le _ _ fun i _ => ?_
    change ⟪v i, x⟫ - b i ≤ scoreMax (v ∘ e) (b ∘ e) x
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      le_scoreMax (v ∘ e) (b ∘ e) x (e.symm i)

lemma priceObjective_reindex (v : Fin k → Space d) (b : Fin k → ℝ)
    (e : Equiv.Perm (Fin k)) :
    priceObjective (v ∘ e) (uniformMass k) (b ∘ e) =
      priceObjective v (uniformMass k) b := by
  unfold priceObjective expectedScore
  simp_rw [scoreMax_reindex, uniformMass, Function.comp_apply, ← Finset.mul_sum]
  rw [Equiv.sum_comp e b]

noncomputable def standardRows (k : ℕ) : Fin k → Space k := EuclideanSpace.basisFun (Fin k) ℝ

lemma standardRows_injective : Function.Injective (standardRows k) :=
  (EuclideanSpace.basisFun (Fin k) ℝ).orthonormal.linearIndependent.injective

lemma scoreGram_standardRows : scoreGram (standardRows k) = 1 := by
  ext i j
  change ⟪EuclideanSpace.basisFun (Fin k) ℝ i, EuclideanSpace.basisFun (Fin k) ℝ j⟫ = _
  rw [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin k) ℝ).orthonormal]
  rfl

lemma scoreGram_standardRows_reindex (e : Equiv.Perm (Fin k)) :
    scoreGram (standardRows k ∘ e) = scoreGram (standardRows k) := by
  ext i j
  change scoreGram (standardRows k) (e i) (e j) = scoreGram (standardRows k) i j
  rw [scoreGram_standardRows]
  simp [Matrix.one_apply]

lemma standard_priceObjective_reindex (b : Fin k → ℝ) (e : Equiv.Perm (Fin k)) :
    priceObjective (standardRows k) (uniformMass k) (b ∘ e) =
      priceObjective (standardRows k) (uniformMass k) b := by
  rw [← priceObjective_reindex (standardRows k) b e]
  unfold priceObjective
  rw [expectedScore_eq_of_gram_eq (standardRows k) (standardRows k ∘ e)
    (scoreGram_standardRows_reindex e).symm]

/-- Any minimizing prices agree up to a constant with balancing prices of
strictly positive cells. Only the second price vector needs an optimality
hypothesis; its balancing property is not assumed. -/
lemma minimizing_prices_eq_balancing_mod_const (v : Fin k → Space d) (p b c : Fin k → ℝ)
    (hv : Function.Injective v) (hp : ∀ i, 0 < p i)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = p i)
    (hc : ∀ a, priceObjective v p c ≤ priceObjective v p a) :
    ∃ a : ℝ, ∀ i, c i = b i + a := by
  have hbmin := balanced_price_is_minimizer v p b hv hb
  obtain ⟨a, ha⟩ := minimizers_score_difference_constant v p b c hbmin hc
  refine ⟨a, fun i => ?_⟩
  have hne : (winningCell v b i).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hm := hb i
    rw [he, measureReal_empty] at hm
    exact (ne_of_gt (hp i)) hm.symm
  obtain ⟨x, hxi⟩ := hne
  obtain ⟨r, hbr, hcr⟩ := common_maximizer_of_jensen_zero v b c x
    (minimizers_jensen_gap_zero v p b c hbmin hc x)
  have hri : r = i := by
    by_contra h
    have hlt := hxi r h
    have hle := le_scoreMax v b x i
    rw [hbr] at hle
    linarith
  subst r
  have heq := ha x
  rw [hbr, hcr] at heq
  linarith

/-- Permutation symmetry forces the minimizing iid-normal prices to be
constant; hence zero prices attain the equal-mass value for every k. -/
theorem standard_zero_price_minimizer : ∀ b : Fin k → ℝ,
    priceObjective (standardRows k) (uniformMass k) 0 ≤
      priceObjective (standardRows k) (uniformMass k) b := by
  obtain ⟨b, hb⟩ := exists_balancing_prices (standardRows k) (uniformMass k)
    standardRows_injective uniformMass_pos sum_uniformMass
  have hbmin := balanced_price_is_minimizer (standardRows k) (uniformMass k) b
    standardRows_injective hb
  have hconst : ∀ i j, b i = b j := by
    intro i j
    let e := Equiv.swap i j
    have hemin : ∀ c, priceObjective (standardRows k) (uniformMass k) (b ∘ e) ≤
        priceObjective (standardRows k) (uniformMass k) c := by
      intro c
      rw [standard_priceObjective_reindex]
      exact hbmin c
    obtain ⟨a, ha⟩ := minimizing_prices_eq_balancing_mod_const (standardRows k)
      (uniformMass k) b (b ∘ e) standardRows_injective uniformMass_pos hb hemin
    have hi := ha i
    have hj := ha j
    simp only [Function.comp_apply, e, Equiv.swap_apply_left, Equiv.swap_apply_right] at hi hj
    linarith
  let i : Fin k := ⟨0, NeZero.pos k⟩
  have he : (fun j => b j - b i) = 0 := by ext j; exact sub_eq_zero.mpr (hconst j i)
  have hz := priceObjective_sub_const (standardRows k) (uniformMass k) b sum_uniformMass (b i)
  rw [he] at hz
  intro c
  rw [hz]
  exact hbmin c

noncomputable def expectedGaussianMaximum (k : ℕ) [NeZero k] : ℝ :=
  ∫ y : Space k, coordinateMax 0 y ∂gaussian k

/-- The normalization constant is an integral over actual independent standard
normal coordinates, rather than a free scalar satisfying assumed identities. -/
theorem equalMassValue_standardRows :
    equalMassValue (standardRows k) = expectedGaussianMaximum k := by
  rw [equalMassValue, balancedValue_eq_of_minimizer _ _ 0 standard_zero_price_minimizer]
  simp only [priceObjective, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  unfold expectedScore expectedGaussianMaximum
  congr 1
  funext x
  unfold scoreMax coordinateMax
  congr 1
  funext i
  simp [standardRows, PiLp.inner_apply]

end GaussianMeasureBridge
