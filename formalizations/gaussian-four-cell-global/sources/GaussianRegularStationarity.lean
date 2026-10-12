import GaussianRegularMoments
import GaussianActualEnvelope
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! First-order stationarity at the actual regular Gaussian partition. This
follows from the proved moment formula and envelope derivative, without any
perimeter theorem or covariance-concavity assumption. -/
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma canonicalPrices_regular (hk : 2 ≤ k) : canonicalPrices (regularRows k) = 0 := by
  apply Eq.symm
  apply canonicalPrices_unique _ (regularRows_injective hk) 0 _ rfl
  apply balanced_price_is_minimizer _ _ _ (regularRows_injective hk)
  intro i
  simpa only [regularWinningPartition, winningPartition_mass] using
    regularWinningPartition_balanced hk i

theorem balancedMoment_regular (hk : 2 ≤ k) (i : Fin k) :
    balancedMoment (regularRows k) i = simplexConstant k • regularRows k i := by
  rw [balancedMoment, canonicalPrices_regular hk,
    rawWinningMoment_eq _ _ (regularRows_injective hk)]
  exact regularWinningPartition_moment hk i

theorem equalMassValue_regular_hasFDerivAt (hk : 2 ≤ k) :
    HasFDerivAt equalMassValue (momentDifferential (regularRows k)) (regularRows k) :=
  equalMassValue_hasFDerivAt _ (regularRows_injective hk)

lemma momentDifferential_regular_apply (hk : 2 ≤ k) (h : Fin k → Space k) :
    momentDifferential (regularRows k) h =
      simplexConstant k * ∑ i, ⟪h i, regularRows k i⟫ := by
  rw [momentDifferential_apply]
  simp_rw [balancedMoment_regular hk, real_inner_smul_right, ← Finset.mul_sum]

lemma trace_scoreGram_hasDerivAt (v : ℝ → Fin k → Space d) (t : ℝ)
    (h : Fin k → Space d) (hd : HasDerivAt v h t) :
    HasDerivAt (fun s => (scoreGram (v s)).trace)
      (2 * ∑ i, ⟪h i, v t i⟫) t := by
  have hi (i : Fin k) : HasDerivAt (fun s => ⟪v s i, v s i⟫)
      (⟪v t i, h i⟫ + ⟪h i, v t i⟫) t :=
    (hasDerivAt_pi.mp hd i).inner ℝ (hasDerivAt_pi.mp hd i)
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i) using 1
  · rfl
  · simp_rw [real_inner_comm (v t _), ← two_mul, ← Finset.mul_sum]

/-- Along every differentiable score path through the regular point whose
Gram trace is locally one, the genuine optimized Gaussian value has derivative
zero. The trace normalization is the actual geometric constraint. -/
theorem regular_stationarity_on_trace_one_path (hk : 2 ≤ k)
    (v : ℝ → Fin k → Space k) (t : ℝ) (h : Fin k → Space k)
    (hv : v t = regularRows k) (hd : HasDerivAt v h t)
    (htrace : (fun s => (scoreGram (v s)).trace) =ᶠ[𝓝 t] (fun _ => 1)) :
    HasDerivAt (fun s => equalMassValue (v s)) 0 t := by
  have ht0 : HasDerivAt (fun s => (scoreGram (v s)).trace) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq htrace
  have he := (trace_scoreGram_hasDerivAt v t h hd).unique ht0
  rw [hv] at he
  have hz : (∑ i, ⟪h i, regularRows k i⟫) = 0 := by linarith
  have hc := equalMassValue_path_derivative v t h (by rw [hv]; exact regularRows_injective hk) hd
  rw [hv] at hc
  simp_rw [balancedMoment_regular hk, real_inner_smul_right, ← Finset.mul_sum, hz, mul_zero] at hc
  exact hc

end GaussianMeasureBridge
