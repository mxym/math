import HydrologyTree.FamilyScaling
import HydrologyTree.FamilyGluing
import HydrologyTree.PathPolynomial

/-! Exact common-coordinate normalization for the actual all-child gluing and
root coefficient update. Every normalization is a specified linear equivalence. -/
open Module Polynomial
noncomputable section
namespace HydrologyTree

section Coordinates
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I] [DecidableEq I]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma basis_normalized_jacobian (bE : Basis I ℝ E) (bF : Basis I ℝ F)
    (f : E → F) (x : E) (hf : DifferentiableAt ℝ f x) :
    endJacobian (fun z => (bE.equiv bF (Equiv.refl I)).symm (f z)) x =
      (LinearMap.toMatrix bE bF (fderiv ℝ f x).toLinearMap).det := by
  let e := bE.equiv bF (Equiv.refl I)
  have h := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt
  calc
    _ = LinearMap.det (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ f x)).toLinearMap := endJacobian_of_hasFDerivAt h
    _ = _ := by
      rw [← LinearMap.det_toMatrix bE]
      congr 1
      ext i j
      simp [LinearMap.toMatrix_apply, e, Basis.equiv]

end Coordinates

abbrev FamilyPairs (ns : List ℕ) := ProductInput ns × ProductInput ns

def familyPairEquiv (ns : List ℕ) : FamilyPairs ns ≃ₗ[ℝ] (Coeff ns.sum × Coeff ns.sum) :=
  ((familyBasis ns).prod (familyBasis ns)).equiv
    ((degreeLT.basis ℝ ns.sum).prod (degreeLT.basis ℝ ns.sum)) (Equiv.refl _)

def normalizedFamilyGlue (ns : List ℕ) (z : FamilyPairs ns) : FamilyPairs ns :=
  (familyPairEquiv ns).symm (familyGlue ns z)

lemma differentiable_normalizedFamilyGlue (ns : List ℕ) : Differentiable ℝ (normalizedFamilyGlue ns) := by
  intro z
  exact (familyPairEquiv ns).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp z
    (hasFDerivAt_familyGlue ns z).differentiableAt

theorem normalizedFamilyGlue_jacobian (ns : List ℕ) (z : FamilyPairs ns) :
    endJacobian (normalizedFamilyGlue ns) z = pairwiseResultants (familyPolynomials ns z.1)^2 := by
  unfold normalizedFamilyGlue familyPairEquiv
  rw [basis_normalized_jacobian _ _ _ _
    (hasFDerivAt_familyGlue ns z).differentiableAt]
  exact familyGlueJacobian_eq_pairwise ns z

abbrev FamilyRootInputs (ns : List ℕ) := FamilyPairs ns × ℝ

def rootRegroupEquiv (N : ℕ) : ((Coeff N × Coeff N) × ℝ) ≃ₗ[ℝ] (Coeff N × (ℝ × Coeff N)) where
  toFun z := (z.1.1,(z.2,z.1.2))
  invFun z := ((z.1,z.2.2),z.2.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def familyRootEquiv (ns : List ℕ) : FamilyRootInputs ns ≃ₗ[ℝ] (Coeff ns.sum × (ℝ × Coeff ns.sum)) :=
  ((familyPairEquiv ns).prodCongr (LinearEquiv.refl ℝ ℝ)).trans (rootRegroupEquiv ns.sum)

/-- Parent coefficients, reordered without changing or scaling any scalar. -/
def rootOutputEquiv (N : ℕ) : (Coeff (N+1) × Coeff N) ≃ₗ[ℝ] (Coeff N × (ℝ × Coeff N)) :=
  (LinearEquiv.prodComm ℝ (Coeff (N+1)) (Coeff N)).trans
    ((LinearEquiv.refl ℝ (Coeff N)).prodCongr (leadingEquiv N).symm)

lemma rootOutputEquiv_actual (N : ℕ) (z : Coeff N × (ℝ × Coeff N)) :
    rootOutputEquiv N (cut (N+1) (rootPolynomial z),z.1) = rootCoefficientMap z := by
  change (z.1, (((cut (N+1) (rootPolynomial z) : Coeff (N+1)) : ℝ[X]).coeff N,
    cut N (cut (N+1) (rootPolynomial z) : ℝ[X]))) = _
  rw [cut_coeff (N+1) _ ⟨N,Nat.lt_succ_self N⟩, cut_cut (Nat.le_succ N)]
  rfl

def normalizedFamilyRoot (ns : List ℕ) (z : FamilyRootInputs ns) : FamilyRootInputs ns :=
  (familyRootEquiv ns).symm (rootCoefficientMap (familyRootEquiv ns z))

lemma differentiable_normalizedFamilyRoot (ns : List ℕ) : Differentiable ℝ (normalizedFamilyRoot ns) := by
  intro z
  exact (familyRootEquiv ns).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp z
    ((hasFDerivAt_rootCoefficientMap (familyRootEquiv ns z)).differentiableAt.comp z
      (familyRootEquiv ns).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt)

/-- Exact root-update determinant after transport into the common family coordinates. -/
theorem normalizedFamilyRoot_jacobian (ns : List ℕ) (z : FamilyRootInputs ns) :
    endJacobian (normalizedFamilyRoot ns) z = (-1 : ℝ)^ns.sum := by
  have h := endJacobian_conjugate
    (familyRootEquiv ns).symm.toContinuousLinearEquiv rootCoefficientMap z
      (hasFDerivAt_rootCoefficientMap _).differentiableAt
  have hlocal : endJacobian rootCoefficientMap (familyRootEquiv ns z) = (-1 : ℝ)^ns.sum := by
    rw [endJacobian_of_hasFDerivAt (hasFDerivAt_rootCoefficientMap _),
      ← LinearMap.det_toMatrix ((degreeLT.basis ℝ ns.sum).prod
        ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ ns.sum))), det_rootChartDerivative]
    simp
  exact h.trans hlocal

end HydrologyTree
