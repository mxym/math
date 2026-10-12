import GaussianFluxEnergy
import GaussianActualEnvelope
import GaussianDiagonalCovarianceDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The true optimized Gaussian covariance value has the facet differential
along every differentiable full-dimensional score lift. Both the derivative
and the positive symmetric coefficients are proved from actual integrals. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def scoreGramVelocity (v h : Fin k → Space d) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ⟪v i,h j⟫ + ⟪h i,v j⟫

noncomputable def fluxCovarianceDifferential (w : Fin k → Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (∑ i, ∑ j, w i j * (D i i + D j j - D i j - D j i)) / 4

lemma scoreGram_path_hasDerivAt (v : ℝ → Fin k → Space d) (t : ℝ)
    (h : Fin k → Space d) (hd : HasDerivAt v h t) :
    HasDerivAt (fun s => scoreGram (v s)) (scoreGramVelocity (v t) h) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp hd i).inner ℝ (hasDerivAt_pi.mp hd j)

lemma symmetric_flux_differential (v h m : Fin k → Space d)
    (w : Fin k → Fin k → ℝ) (hs : ∀ i j, w i j = w j i)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) :
    (∑ i, ⟪h i,m i⟫) = fluxCovarianceDifferential w (scoreGramVelocity v h) := by
  have he : (∑ i, ⟪h i,m i⟫) = ∑ i, ∑ j, w i j * ⟪h i,v i - v j⟫ := by
    simp only [hf,inner_sum,real_inner_smul_right]
  have hn (i j : Fin k) : scoreGramVelocity v h i i + scoreGramVelocity v h j j -
      scoreGramVelocity v h i j - scoreGramVelocity v h j i =
        2 * (⟪h i,v i - v j⟫ + ⟪h j,v j - v i⟫) := by
    simp only [scoreGramVelocity,inner_sub_right]
    rw [real_inner_comm (v i) (h i), real_inner_comm (v j) (h j),
      real_inner_comm (v i) (h j),real_inner_comm (v j) (h i)]
    ring
  have hswap : (∑ i, ∑ j, w i j * ⟪h j,v j - v i⟫) =
      ∑ i, ∑ j, w i j * ⟪h i,v i - v j⟫ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  unfold fluxCovarianceDifferential
  simp_rw [hn,show ∀ a b c : ℝ, a * (2 * (b+c)) = 2 * (a*b+a*c) by intros; ring,
    ← Finset.mul_sum,Finset.sum_add_distrib]
  rw [hswap,he]
  ring

theorem actual_covariance_score_path_derivative
    (v : ℝ → Fin (d+2) → Space (d+1)) (t : ℝ) (h : Fin (d+2) → Space (d+1))
    (hv : AffineIndependent ℝ (v t)) (hd : HasDerivAt v h t) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment (v t) i = ∑ j, w i j • (v t i - v t j)) ∧
      HasDerivAt (fun s => covarianceValue (scoreGram (v s)))
        (fluxCovarianceDifferential w (scoreGramVelocity (v t) h)) t := by
  obtain ⟨w,hw,hp,hs,hf,he⟩ := actual_balanced_flux_energy (v t) hv
  refine ⟨w,hw,hp,hs,hf,?_⟩
  have hh := equalMassValue_path_derivative v t h hv.injective hd
  rw [symmetric_flux_differential (v t) h _ w hs hf] at hh
  simpa only [covarianceValue_scoreGram] using hh

end GaussianMeasureBridge
