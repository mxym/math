import GaussianSmoothWinningGradient

/-! Exact nonnegative normal coefficients of the actual smooth winning-cell
gradients. The norm estimate retains these coefficients instead of replacing
them by a coarse approximation-index-dependent constant. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

lemma transition_affine_fderiv (n : Space d) (a c : ℝ) (x : Space d) :
    fderiv ℝ (fun y => Real.smoothTransition (c*(⟪n,y⟫-a))) x =
      (c*deriv Real.smoothTransition (c*(⟪n,x⟫-a))) • innerSL ℝ n := by
  have hi : HasFDerivAt (fun y : Space d => c*(⟪n,y⟫-a)) (c • innerSL ℝ n) x := by
    convert ((innerSL ℝ n).hasFDerivAt.sub_const a).const_smul c using 1
    rfl
  have hh := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (c*(⟪n,x⟫-a))).hasDerivAt
  have he : fderiv ℝ (fun y => Real.smoothTransition (c*(⟪n,y⟫-a))) x =
      deriv Real.smoothTransition (c*(⟪n,x⟫-a)) • (c • innerSL ℝ n) := by
    convert (hh.comp_hasFDerivAt (h₂ := Real.smoothTransition) x hi).fderiv using 1
    rfl
  rw [he,smul_smul,mul_comm]

noncomputable def smoothWinningCoefficient (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) (j : Fin k) (x : Space d) : ℝ :=
  ((N : ℝ)+1)*deriv Real.smoothTransition (((N : ℝ)+1)*(⟪v i-v j,x⟫-(b i-b j)))*
    ∏ l ∈ (Finset.univ.erase i).erase j,
      Real.smoothTransition (((N : ℝ)+1)*(⟪v i-v l,x⟫-(b i-b l)))

lemma smoothWinningCoefficient_nonneg (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) (j : Fin k) (x : Space d) :
    0 ≤ smoothWinningCoefficient v b i N j x := by
  apply mul_nonneg
  · exact mul_nonneg (by positivity) (smoothTransition_deriv_nonneg _)
  · exact Finset.prod_nonneg (fun _ _ => Real.smoothTransition.nonneg _)

theorem smoothWinningApprox_fderiv (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) (x : Space d) :
    fderiv ℝ (smoothWinningApprox v b i N) x =
      ∑ j ∈ Finset.univ.erase i,smoothWinningCoefficient v b i N j x • innerSL ℝ (v i-v j) := by
  classical
  let f : Fin k → Space d → ℝ := fun j y =>
    Real.smoothTransition (((N : ℝ)+1)*(⟪v i-v j,y⟫-(b i-b j)))
  have hd (j : Fin k) : DifferentiableAt ℝ (f j) x := by
    have hinner : ContDiff ℝ 1 (fun y : Space d => ⟪v i-v j,y⟫) :=
      (innerSL ℝ (v i-v j)).contDiff
    have hc : ContDiff ℝ 1 (f j) := by
      apply Real.smoothTransition.contDiff.comp
      fun_prop
    exact hc.differentiable one_ne_zero x
  change fderiv ℝ (fun y => ∏ j ∈ Finset.univ.erase i,f j y) x = _
  rw [fderiv_finsetProd (fun j _ => hd j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show f j = (fun y => Real.smoothTransition (((N : ℝ)+1)*
      (⟪v i-v j,y⟫-(b i-b j)))) from rfl,transition_affine_fderiv,smul_smul]
  congr 1
  unfold smoothWinningCoefficient
  dsimp only [f]
  ring

theorem smoothWinningApprox_coefficient_gradient_bound
    (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) (N : ℕ) (x : Space d) :
    ‖fderiv ℝ (smoothWinningApprox v b i N) x‖ ≤
      ∑ j ∈ Finset.univ.erase i,smoothWinningCoefficient v b i N j x*‖v i-v j‖ := by
  rw [smoothWinningApprox_fderiv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (smoothWinningCoefficient_nonneg v b i N j x),
    innerSL_apply_norm]

end GaussianMeasureBridge
