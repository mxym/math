import GaussianSimplicialMassFlux
import GaussianWinningContinuity

/-! Frechet differentiability in all price parameters under the actual Gaussian
integral. Null ties and a uniform integrable Lipschitz bound justify Leibniz. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

lemma scoreMax_price_lipschitz (v : Fin k → Space d) (x : Space d) :
    LipschitzWith 1 (fun b : Fin k → ℝ => scoreMax v b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] using
    scoreMax_abs_sub_le v b c x

lemma scoreMax_price_hasFDerivAt_of_winning (v : Fin k → Space d)
    (b : Fin k → ℝ) (x : Space d) (i : Fin k) (hi : x ∈ winningCell v b i) :
    HasFDerivAt (fun c : Fin k → ℝ => scoreMax v c x)
      (-(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) b := by
  have ht : Tendsto (fun c : Fin k → ℝ => (v,c)) (𝓝 b) (𝓝 (v,b)) :=
    (show ContinuousAt (fun c : Fin k → ℝ => (v,c)) b by fun_prop).tendsto
  have he := ht.eventually (eventually_winning_parameters v b x i hi)
  have heq : (fun c : Fin k → ℝ => scoreMax v c x) =ᶠ[𝓝 b]
      (fun c : Fin k → ℝ => ⟪v i,x⟫-c i) := by
    filter_upwards [he] with c hc
    exact scoreMax_eq_winning_score v c x i hc
  exact ((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_sub
    ⟪v i,x⟫).congr_of_eventuallyEq heq

lemma winning_indicator_sum_eq {E : Type*} [AddCommMonoid E]
    (v : Fin k → Space d) (b : Fin k → ℝ) (x : Space d) (r : Fin k)
    (hr : x ∈ winningCell v b r) (a : Fin k → E) :
    (∑ i, (winningCell v b i).indicator (fun _ => a i) x) = a r := by
  classical
  rw [Finset.sum_eq_single r]
  · exact Set.indicator_of_mem hr _
  · intro i _ hir
    have hnot : x ∉ winningCell v b i := fun hxi =>
      Set.disjoint_left.mp (winningCell_disjoint v b i r hir) hxi hr
    exact Set.indicator_of_notMem hnot _
  · simp

noncomputable def scorePriceDifferential (v : Fin k → Space d)
    (b : Fin k → ℝ) (x : Space d) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, (winningCell v b i).indicator
    (fun _ => -(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) x

lemma aestronglyMeasurable_scorePriceDifferential (v : Fin k → Space d) (b : Fin k → ℝ) :
    AEStronglyMeasurable (scorePriceDifferential v b) (gaussian d) := by
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (stronglyMeasurable_const.indicator (measurableSet_winningCell v b i)).aestronglyMeasurable)

lemma ae_scoreMax_price_hasFDerivAt (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    ∀ᵐ x ∂gaussian d, HasFDerivAt (fun c : Fin k → ℝ => scoreMax v c x)
      (scorePriceDifferential v b x) b := by
  filter_upwards [ae_unique_winner v b hv] with x hx
  obtain ⟨r,hr⟩ := hx
  have he : scorePriceDifferential v b x =
      -(ContinuousLinearMap.proj r : (Fin k → ℝ) →L[ℝ] ℝ) :=
    winning_indicator_sum_eq v b x r hr _
  rw [he]
  exact scoreMax_price_hasFDerivAt_of_winning v b x r hr

/-- Frechet, not merely directional, differentiability of the original
expected maximum in its finite vector of price parameters. -/
theorem expectedScore_price_differentiableAt (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) : DifferentiableAt ℝ (expectedScore v) b := by
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip
    (𝕜 := ℝ) (μ := gaussian d) (F := fun c x => scoreMax v c x)
    (F' := scorePriceDifferential v b) (s := Set.univ) (x₀ := b)
    (bound := fun _ : Space d => (1 : ℝ)) (by simp)
    (Eventually.of_forall fun c => (continuous_scoreMax v c).aestronglyMeasurable)
    (integrable_scoreMax v b) (aestronglyMeasurable_scorePriceDifferential v b)
    (ae_of_all _ fun x => by
      change LipschitzOnWith 1 (fun c : Fin k → ℝ => scoreMax v c x) Set.univ
      exact (scoreMax_price_lipschitz v x).lipschitzOnWith)
    (integrable_const 1) (ae_scoreMax_price_hasFDerivAt v b hv)
  exact h.2.differentiableAt

/-- Frechet differentiability of an actual Gaussian epigraph mass. A uniform
Gaussian-density bound controls every price direction simultaneously. -/
theorem graphMass_price_differentiableAt (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) : DifferentiableAt ℝ (graphMass v) b := by
  let F' : Space d → (Fin k → ℝ) →L[ℝ] ℝ := fun x =>
    (-standardDensity (scoreMax v b x)) • scorePriceDifferential v b x
  have hm : AEStronglyMeasurable F' (gaussian d) :=
    ((continuous_standardDensity.comp (continuous_scoreMax v b)).neg.aestronglyMeasurable).smul
      (aestronglyMeasurable_scorePriceDifferential v b)
  have hd : ∀ᵐ x ∂gaussian d,
      HasFDerivAt (fun c : Fin k → ℝ => standardTail (scoreMax v c x)) (F' x) b := by
    filter_upwards [ae_scoreMax_price_hasFDerivAt v b hv] with x hx
    exact (standardTail_hasDerivAt (scoreMax v b x)).comp_hasFDerivAt b hx
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip
    (𝕜 := ℝ) (μ := gaussian d) (F := fun c x => standardTail (scoreMax v c x))
    (F' := F') (s := Set.univ) (x₀ := b) (bound := fun _ : Space d => standardDensity 0)
    (by simp)
    (Eventually.of_forall fun c =>
      (standardTail_lipschitz.continuous.comp (continuous_scoreMax v c)).aestronglyMeasurable)
    (integrable_tail_score v b) hm
    (ae_of_all _ fun x => by
      have hb : Real.nnabs (standardDensity 0) =
          (⟨standardDensity 0, (standardDensity_pos 0).le⟩ : NNReal) := by
        apply NNReal.coe_injective
        change |standardDensity 0| = standardDensity 0
        exact abs_of_pos (standardDensity_pos 0)
      rw [hb]
      have hl : LipschitzWith
          (⟨standardDensity 0, (standardDensity_pos 0).le⟩ : NNReal)
          (fun c : Fin k → ℝ => standardTail (scoreMax v c x)) := by
        simpa only [mul_one, Function.comp_def] using
          standardTail_lipschitz.comp (scoreMax_price_lipschitz v x)
      exact hl.lipschitzOnWith)
    (integrable_const _) hd
  have he : graphMass v = fun c => ∫ x, standardTail (scoreMax v c x) ∂gaussian d :=
    funext (graphMass_eq_tail v)
  rw [he]
  exact h.2.differentiableAt

end GaussianFour
