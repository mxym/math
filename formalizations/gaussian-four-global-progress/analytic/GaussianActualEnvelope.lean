import GaussianWinningContinuity
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Genuine Frechet derivative of the minimized Gaussian value. The proof uses
actual optimal partitions and their continuous moments, not a postulated envelope
identity or a differentiable choice of prices. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma eventually_injective_scores (v : Fin k → Space d) (hv : Function.Injective v) :
    ∀ᶠ w in 𝓝 v, Function.Injective w := by
  have he : ∀ᶠ w in 𝓝 v, ∀ i j : Fin k, i ≠ j → w i ≠ w j := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    · have hc : ContinuousAt (fun w : Fin k → Space d => w i - w j) v := by fun_prop
      have h : ∀ᶠ w : Fin k → Space d in 𝓝 v, w i - w j ≠ 0 :=
        hc.eventually_ne (sub_ne_zero.mpr (fun h => hij (hv h)))
      exact h.mono fun w hw _ => sub_ne_zero.mp hw
  exact he.mono fun w hw i j hij => by
    by_contra hne
    exact hw i j hne hij

noncomputable def momentDifferential (v : Fin k → Space d) : (Fin k → Space d) →L[ℝ] ℝ :=
  ∑ i : Fin k, (innerSL ℝ (balancedMoment v i)).comp (ContinuousLinearMap.proj i)

lemma momentDifferential_apply (v h : Fin k → Space d) :
    momentDifferential v h = ∑ i, ⟪h i, balancedMoment v i⟫ := by
  simp [momentDifferential, real_inner_comm]

lemma envelope_remainder_bounds (v w : Fin k → Space d)
    (hv : Function.Injective v) (hw : Function.Injective w) :
    0 ≤ equalMassValue w - equalMassValue v - momentDifferential v (w-v) ∧
    equalMassValue w - equalMassValue v - momentDifferential v (w-v) ≤
      ‖w-v‖ * ∑ i, ‖balancedMoment w i - balancedMoment v i‖ := by
  have hlow := balancedMoment_support v hv w
  have hhigh := balancedMoment_support w hw v
  have hvv := balancedMoment_value v hv
  have hww := balancedMoment_value w hw
  rw [momentDifferential_apply]
  have hdiff : (∑ i, ⟪(w-v) i, balancedMoment v i⟫) =
      (∑ i, ⟪w i, balancedMoment v i⟫) - ∑ i, ⟪v i, balancedMoment v i⟫ := by
    simp only [Pi.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  rw [hdiff]
  refine ⟨by linarith, ?_⟩
  have hstep : equalMassValue w - equalMassValue v -
      ((∑ i, ⟪w i, balancedMoment v i⟫) - ∑ i, ⟪v i, balancedMoment v i⟫) ≤
      ∑ i, ⟪w i - v i, balancedMoment w i - balancedMoment v i⟫ := by
    simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
    linarith
  refine hstep.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_le_pi_norm (w-v) i) (norm_nonneg _))

/-- The actual equal-mass infimum value is Frechet differentiable at every
finite family of distinct score vectors. Its derivative is the vector of
actual optimal winning-cell first moments. -/
theorem equalMassValue_hasFDerivAt (v : Fin k → Space d) (hv : Function.Injective v) :
    HasFDerivAt equalMassValue (momentDifferential v) v := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hcont : ContinuousAt (fun w : Fin k → Space d =>
      ∑ i, ‖balancedMoment w i - balancedMoment v i‖) v := by
    have hc (i : Fin k) : ContinuousAt
        (fun w : Fin k → Space d => ‖balancedMoment w i - balancedMoment v i‖) v :=
      ((continuousAt_balancedMoment v hv i).sub continuousAt_const).norm
    fun_prop
  have hsmall : ∀ᶠ w in 𝓝 v, (∑ i, ‖balancedMoment w i - balancedMoment v i‖) < ε :=
    hcont.eventually_lt continuousAt_const (by simpa using hε)
  filter_upwards [eventually_injective_scores v hv, hsmall] with w hw hws
  have hb := envelope_remainder_bounds v w hv hw
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hws.le (norm_nonneg (w-v)))

/-- Along any differentiable actual score path, the minimized value has the
expected winning-moment derivative. No price-path differentiability is needed. -/
theorem equalMassValue_path_derivative (v : ℝ → Fin k → Space d)
    (t : ℝ) (h : Fin k → Space d) (hv : Function.Injective (v t))
    (hd : HasDerivAt v h t) :
    HasDerivAt (fun s => equalMassValue (v s))
      (∑ i, ⟪h i, balancedMoment (v t) i⟫) t := by
  convert (equalMassValue_hasFDerivAt (v t) hv).comp_hasDerivAt t hd using 1
  · rfl
  · exact (momentDifferential_apply (v t) h).symm

end GaussianMeasureBridge
