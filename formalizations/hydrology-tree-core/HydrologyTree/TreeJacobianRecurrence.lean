import HydrologyTree.TreePipeline

/-! Actual all-rate branching-tree derivative induction step. Every local map,
physical child, and normalization was proved before applying this chain rule. -/
open Module Polynomial Matrix
noncomputable section
namespace HydrologyTree

lemma treePipeline_differentiableAt {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hc : ∀ c : RootChild t, DifferentiableAt ℝ (physicalCoefficientMap (childTree t c)) (childRates t c x)) :
    DifferentiableAt ℝ (treePipeline t) (originalWorkEquiv t x) := by
  have hz : (rootCoupling (childLeakMap t) (originalWorkEquiv t x)).1 = fun c => childRates t c x := by
    rw [originalWorkEquiv_originalCoupling,rootCoupling_physical_coordinates]
  have hn : ∀ c : RootChild t,
      DifferentiableAt ℝ (normalizedPhysicalTree (childTree t c))
        ((rootCoupling (childLeakMap t) (originalWorkEquiv t x)).1 c) := by
    intro c
    rw [hz]
    exact (coefficientArrayEquiv (childEdgeCount t c)).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp _ (hc c)
  exact (differentiable_treeLocalStep t _).comp _
    ((differentiableAt_treeChildStep t _ hn).comp _ (hasFDerivAt_rootCoupling (childLeakMap t) _).differentiableAt)

/-- The actual parent coefficient map is differentiable whenever the strictly
smaller actual child coefficient maps are. The later strong induction discharges this. -/
theorem physicalCoefficientMap_differentiableAt_of_children {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hc : ∀ c : RootChild t, DifferentiableAt ℝ (physicalCoefficientMap (childTree t c)) (childRates t c x)) :
    DifferentiableAt ℝ (physicalCoefficientMap t) x := by
  have h := (parentCoefficientWorkEquiv t).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp x
    ((treePipeline_differentiableAt t x hc).comp x
      (originalWorkEquiv t).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt)
  have he : (fun y : TreeRates n => (parentCoefficientWorkEquiv t).symm
      (treePipeline t (originalWorkEquiv t y))) = physicalCoefficientMap t := by
    funext y
    rw [treePipeline_actual,LinearEquiv.symm_apply_apply]
  exact he ▸ h

/-- The fixed coefficient-return map contributes its actual determinant, not a
numerically fitted or unspecified nonzero factor. -/
lemma treeCoordinateReturn_jacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : DifferentiableAt ℝ (physicalCoefficientMap t) x) :
    endJacobian (fun y => treeCoordinateReturn t (physicalCoefficientMap t y)) x =
      treeCoordinateDet t * treeCanonicalJacobian t x := by
  have h := (treeCoordinateReturn t).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hx.hasFDerivAt
  calc
    _ = LinearMap.det ((treeCoordinateReturn t).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (physicalCoefficientMap t) x)).toLinearMap := endJacobian_of_hasFDerivAt h
    _ = _ := by
      rw [← LinearMap.det_toMatrix (catenaryArrayInputBasis n)]
      change (LinearMap.toMatrix _ _ ((treeCoordinateReturn t).toLinearMap.comp
        (fderiv ℝ (physicalCoefficientMap t) x).toLinearMap)).det = _
      rw [LinearMap.toMatrix_comp (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
        (catenaryArrayInputBasis n),Matrix.det_mul]
      rfl

lemma treePipeline_jacobian_transport {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : DifferentiableAt ℝ (physicalCoefficientMap t) x) :
    endJacobian (treePipeline t) (originalWorkEquiv t x) =
      treeCoordinateDet t * treeCanonicalJacobian t x := by
  have hf : DifferentiableAt ℝ (fun y => treeCoordinateReturn t (physicalCoefficientMap t y)) x :=
    (treeCoordinateReturn t).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp x hx
  have h := endJacobian_linear_conjugate (originalWorkEquiv t).symm
    (fun y => treeCoordinateReturn t (physicalCoefficientMap t y)) (originalWorkEquiv t x)
    (by simpa only [LinearEquiv.symm_apply_apply] using hf)
  have he : (fun z : TreeWork t => originalWorkEquiv t
      (treeCoordinateReturn t (physicalCoefficientMap t ((originalWorkEquiv t).symm z)))) = treePipeline t := by
    funext z
    have hh := treePipeline_actual t ((originalWorkEquiv t).symm z)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact (originalWorkEquiv t).apply_symm_apply _ |>.trans hh.symm
  change endJacobian (fun z : TreeWork t => originalWorkEquiv t
      (treeCoordinateReturn t (physicalCoefficientMap t ((originalWorkEquiv t).symm z)))) _ = _ at h
  rw [he,LinearEquiv.symm_apply_apply,treeCoordinateReturn_jacobian t x hx] at h
  exact h

/-- Exact local physical factors a_c^(m_c+1) f_c^m_c for all root connectors. -/
def treeRootRateFactor {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  ∏ c : RootChild t, x.1 c.val ^ (childEdgeCount t c+1) *
    outwardByVertex x.2 c.val ^ childEdgeCount t c

lemma treeRootRateFactor_eq {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (∏ c : RootChild t, (x.1 c.val*outwardByVertex x.2 c.val)^childEdgeCount t c) *
      (∏ c : RootChild t, x.1 c.val) = treeRootRateFactor t x := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  rw [mul_pow,pow_succ]
  ring

/-- The complete actual parent Jacobian recurrence, including singular rate
vectors. The only induction premises concern strictly smaller physical children. -/
theorem treeCanonicalJacobian_recurrence_of_children {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hc : ∀ c : RootChild t, DifferentiableAt ℝ (physicalCoefficientMap (childTree t c)) (childRates t c x)) :
    treeCoordinateDet t * treeCanonicalJacobian t x =
      (-1 : ℝ)^n * treeSiblingResultant t x ^ 2 * treeRootRateFactor t x *
        ∏ c : RootChild t, treeCanonicalJacobian (childTree t c) (childRates t c x) := by
  have hp := physicalCoefficientMap_differentiableAt_of_children t x hc
  rw [← treePipeline_jacobian_transport t x hp]
  have hCouple := (hasFDerivAt_rootCoupling (childLeakMap t) (originalWorkEquiv t x)).differentiableAt
  have hz : (rootCoupling (childLeakMap t) (originalWorkEquiv t x)).1 = fun c => childRates t c x := by
    rw [originalWorkEquiv_originalCoupling,rootCoupling_physical_coordinates]
  have hChild : DifferentiableAt ℝ (treeChildStep t)
      (rootCoupling (childLeakMap t) (originalWorkEquiv t x)) := by
    apply differentiableAt_treeChildStep
    intro c
    rw [hz]
    exact (coefficientArrayEquiv (childEdgeCount t c)).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp _ (hc c)
  rw [treePipeline,endJacobian_comp (differentiable_treeLocalStep t _) (hChild.comp _ hCouple),
    endJacobian_comp hChild hCouple,Function.comp_apply,treeLocalStep_actual_jacobian,
    treeChildStep_jacobian t _ (by simpa only [hz] using hc),rootCoupling_endJacobian]
  rw [hz,originalWorkEquiv_apply]
  simp only [childRates_leak]
  have hfac := treeRootRateFactor_eq t x
  rw [← hfac]
  ring

/-- UNCONDITIONAL all-size differentiability of the actual tree coefficient map. -/
theorem differentiable_physicalCoefficientMap {n : ℕ} (t : OrderedTree n) :
    Differentiable ℝ (physicalCoefficientMap t) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    apply physicalCoefficientMap_differentiableAt_of_children
    intro c
    exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) (childRates t c x)

/-- UNCONDITIONAL all-size, all-rate canonical physical Jacobian recurrence. -/
theorem treeCanonicalJacobian_recurrence {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeCoordinateDet t * treeCanonicalJacobian t x =
      (-1 : ℝ)^n * treeSiblingResultant t x ^ 2 * treeRootRateFactor t x *
        ∏ c : RootChild t, treeCanonicalJacobian (childTree t c) (childRates t c x) :=
  treeCanonicalJacobian_recurrence_of_children t x
    (fun c => differentiable_physicalCoefficientMap (childTree t c) (childRates t c x))

end HydrologyTree
