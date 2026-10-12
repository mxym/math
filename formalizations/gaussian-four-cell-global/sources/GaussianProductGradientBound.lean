import GaussianSmoothTransitionKernel

/-! A finite product of scalar functions in [0,1] has derivative norm at
most the sum of the individual derivative norms. This is the pointwise
estimate needed by the actual winning-cell approximants. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma scalar_product_gradient_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Space d → ℝ) (x : Space d)
    (hd : ∀ i ∈ s,DifferentiableAt ℝ (f i) x)
    (hb : ∀ i ∈ s,0 ≤ f i x ∧ f i x ≤ 1) :
    ‖fderiv ℝ (fun y => ∏ i ∈ s,f i y) x‖ ≤ ∑ i ∈ s,‖fderiv ℝ (f i) x‖ := by
  rw [fderiv_finsetProd hd]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hp0 : 0 ≤ ∏ j ∈ s.erase i,f j x :=
    Finset.prod_nonneg (fun j hj => (hb j (Finset.mem_of_mem_erase hj)).1)
  have hp1 : (∏ j ∈ s.erase i,f j x) ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj => (hb j (Finset.mem_of_mem_erase hj)).1)
      (fun j hj => (hb j (Finset.mem_of_mem_erase hj)).2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

end GaussianMeasureBridge
