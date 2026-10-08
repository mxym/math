import GaussianProductGradientBound

/-! Every explicit smooth winning-cell approximant has an actual globally
bounded derivative, hence an integrable Gaussian derivative norm. The bound
is not uniform in the approximation index; its sharp boundary limit remains
the next separate analytic obligation. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

lemma transition_affine_gradient_bound (n : Space d) (a c M : ℝ)
    (hM : ∀ t,‖deriv Real.smoothTransition t‖ ≤ M) (x : Space d) :
    ‖fderiv ℝ (fun y => Real.smoothTransition (c*(⟪n,y⟫-a))) x‖ ≤ M * |c| * ‖n‖ := by
  have hi : HasFDerivAt (fun y : Space d => c*(⟪n,y⟫-a)) (c • innerSL ℝ n) x := by
    convert ((innerSL ℝ n).hasFDerivAt.sub_const a).const_smul c using 1
    rfl
  have hh : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (c*(⟪n,x⟫-a)))
      (c*(⟪n,x⟫-a)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have he : fderiv ℝ (fun y => Real.smoothTransition (c*(⟪n,y⟫-a))) x =
      deriv Real.smoothTransition (c*(⟪n,x⟫-a)) • (c • innerSL ℝ n) :=
    by
      convert (hh.comp_hasFDerivAt (h₂ := Real.smoothTransition) x hi).fderiv using 1
      rfl
  rw [he,norm_smul,norm_smul,innerSL_apply_norm]
  calc
    _ ≤ M*(‖c‖*‖n‖) := mul_le_mul_of_nonneg_right (hM _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [Real.norm_eq_abs]; ring

lemma smoothWinningApprox_gradient_bound (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ x,‖fderiv ℝ (smoothWinningApprox v b i N) x‖ ≤ B := by
  obtain ⟨M,hM0,hM⟩ := smoothTransition_deriv_bounded
  let B : ℝ := ∑ j ∈ Finset.univ.erase i,M*((N : ℝ)+1)*‖v i-v j‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨B,hB,fun x => ?_⟩
  let f : Fin k → Space d → ℝ := fun j y => Real.smoothTransition (((N : ℝ)+1)*
    (⟪v i-v j,y⟫-(b i-b j)))
  have hd (j : Fin k) : DifferentiableAt ℝ (f j) x := by
    have hinner : ContDiff ℝ 1 (fun y : Space d => ⟪v i-v j,y⟫) :=
      (innerSL ℝ (v i-v j)).contDiff
    have hfun : ContDiff ℝ 1 (f j) := by
      apply Real.smoothTransition.contDiff.comp
      fun_prop
    exact hfun.differentiable one_ne_zero x
  have hb (j : Fin k) : 0 ≤ f j x ∧ f j x ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  have hp := scalar_product_gradient_bound (Finset.univ.erase i) f x
    (fun j _ => hd j) (fun j _ => hb j)
  apply hp.trans
  apply Finset.sum_le_sum
  intro j _
  have he := transition_affine_gradient_bound (v i-v j) (b i-b j) ((N : ℝ)+1) M hM x
  simpa only [abs_of_nonneg (show 0 ≤ (N : ℝ)+1 by positivity)] using he

theorem smoothWinningApprox_gradient_integrable (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) :
    Integrable (fun x => ‖fderiv ℝ (smoothWinningApprox v b i N) x‖) (gaussian d) := by
  obtain ⟨B,hB,hbound⟩ := smoothWinningApprox_gradient_bound v b i N
  have hc := (smoothWinningApprox_contDiff v b i N).continuous_fderiv (by simp)
  apply (integrable_const B).mono' hc.norm.aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa only [norm_norm] using hbound x

end GaussianMeasureBridge
