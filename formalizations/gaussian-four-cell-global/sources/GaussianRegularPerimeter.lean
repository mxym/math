import GaussianRegularFlux

/-! Exact value of the intrinsic Gaussian perimeter of the regular model.
This proves the comparison target and its normalization independently of the
remaining universal perimeter inequality. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e : ℕ}

lemma regular_gram_edge_squared (v : Fin (d+2) → Space e)
    (hg : scoreGram v = regularCovariance (d+2)) (i j : Fin (d+2)) (hij : i ≠ j) :
    ‖v i-v j‖^2 = 2/(d+1:ℕ) := by
  rw [norm_sub_sq_real,← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  change scoreGram v i i-2*scoreGram v i j+scoreGram v j j = _
  rw [hg,regularCovariance_apply,regularCovariance_apply,regularCovariance_apply]
  simp only [ite_true,if_neg hij,show d+2-1=d+1 by omega]
  ring

theorem regular_intrinsic_cluster_perimeter_squared
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i = 0) (hg : scoreGram v = regularCovariance (d+2)) :
    ((∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)^2 =
      (d+1:ℕ)*simplexConstant (d+2)^2/2 := by
  obtain ⟨w,hw,hp,hs,hf,hc⟩ := actual_balanced_flux_energy v hv
  let a : ℝ := Real.sqrt (2/(d+1:ℕ))
  have ha : a^2 = 2/(d+1:ℕ) := Real.sq_sqrt (by positivity)
  have hedge (i j : Fin (d+2)) (hij : i ≠ j) : ‖v i-v j‖ = a := by
    rw [← Real.sqrt_sq (norm_nonneg (v i-v j)),regular_gram_edge_squared v hg i j hij]
  have hS : fluxPerimeter v w = fluxTrace w*a/2 := by
    have he (i j : Fin (d+2)) : w i j*‖v i-v j‖ = w i j*a := by
      by_cases hij : i=j
      · subst j; simp [hw i]
      · rw [hedge i j hij]
    simp only [fluxPerimeter,he,← Finset.sum_mul,fluxTrace]
  have hE : (∑ i,∑ j,w i j*‖v i-v j‖^2)/2 = fluxTrace w*a^2/2 := by
    have he (i j : Fin (d+2)) : w i j*‖v i-v j‖^2 = w i j*a^2 := by
      by_cases hij : i=j
      · subst j; simp [hw i]
      · rw [hedge i j hij]
    simp only [he,← Finset.sum_mul,fluxTrace]
  have hvalue : equalMassValue v = simplexConstant (d+2) := by
    rw [← covarianceValue_scoreGram,hg,covarianceValue_regular]
  rw [hvalue,hE,ha] at hc
  have hn : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
  have hT : fluxTrace w = (d+1:ℕ)*simplexConstant (d+2) := by
    field_simp at hc
    nlinarith
  have hraw (i : Fin (d+2)) : rawWinningMoment v (canonicalPrices v) i =
      ∑ j,w i j • (v i-v j) := hf i
  rw [actual_simplicial_cluster_inner_perimeter v _ hv w hraw,hS,hT]
  rw [div_pow,mul_pow,ha]
  field_simp

end GaussianMeasureBridge
