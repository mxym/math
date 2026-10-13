import HydrologyTree.EndJacobian
import HydrologyTree.RootUpdate

/-! The root polynomial operation and monic numerator scaling combined in a
single explicitly triangular map. Its determinant is valid at zero scales. -/
open Module
noncomputable section
namespace HydrologyTree

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev RootTransitionSpace (P E : Type*) := P × ((ℝ × ℝ) × E)

def rootTransition (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E)
    (x : RootTransitionSpace P E) : RootTransitionSpace P E :=
  (x.1, ((x.2.1.1 + α x.1, β x.1 + x.2.1.1 * α x.1 - x.2.1.2),
    L x.1 + x.2.1.1 • K x.1 - x.2.1.2 • x.2.2))

def rootTransitionCross (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E) (d : ℝ) :
    P →L[ℝ] ((ℝ × ℝ) × E) := (α.prod (β + d • α)).prod (L + d • K)

def rootTransitionFiberCross (K : P →L[ℝ] E) (p : P) (q : E) : (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (K p) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight q

def rootTransitionDerivative (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E)
    (x : RootTransitionSpace P E) : RootTransitionSpace P E →L[ℝ] RootTransitionSpace P E :=
  lowerBlock (ContinuousLinearMap.id ℝ P) (rootTransitionCross α β L K x.2.1.1)
    (lowerBlock (rootFiber (α x.1)) (rootTransitionFiberCross K x.1 x.2.2)
      (-x.2.1.2 • ContinuousLinearMap.id ℝ E))

theorem hasFDerivAt_rootTransition (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E)
    (x : RootTransitionSpace P E) :
    HasFDerivAt (rootTransition α β L K) (rootTransitionDerivative α β L K x) x := by
  let A : RootTransitionSpace P E →L[ℝ] P := ContinuousLinearMap.fst ℝ P _
  let B : RootTransitionSpace P E →L[ℝ] ((ℝ × ℝ) × E) := ContinuousLinearMap.snd ℝ P _
  let D : RootTransitionSpace P E →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) E).comp B)
  let C : RootTransitionSpace P E →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) E).comp B)
  let Q : RootTransitionSpace P E →L[ℝ] E := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) E).comp B
  have ha := α.hasFDerivAt.comp x A.hasFDerivAt
  have h1 := D.hasFDerivAt.add ha
  have h2 := ((β.hasFDerivAt.comp x A.hasFDerivAt).add (D.hasFDerivAt.mul ha)).sub C.hasFDerivAt
  have h3 := ((L.hasFDerivAt.comp x A.hasFDerivAt).add
    (D.hasFDerivAt.smul (K.hasFDerivAt.comp x A.hasFDerivAt))).sub
      (C.hasFDerivAt.smul Q.hasFDerivAt)
  apply (A.hasFDerivAt.prodMk ((h1.prodMk h2).prodMk h3)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · change h.2.1.1 + α h.1 = α h.1 + h.2.1.1
        exact add_comm _ _
      · change β h.1 + (x.2.1.1 * α h.1 + α x.1 * h.2.1.1) - h.2.1.2 =
          (β h.1 + x.2.1.1 * α h.1) + (h.2.1.1 * α x.1 - h.2.1.2)
        ring
    · change L h.1 + (x.2.1.1 • K h.1 + h.2.1.1 • K x.1) -
          (x.2.1.2 • h.2.2 + h.2.1.2 • x.2.2) =
        (L h.1 + x.2.1.1 • K h.1) +
          ((h.2.1.1 • K x.1 - h.2.1.2 • x.2.2) + (-x.2.1.2) • h.2.2)
      simp only [neg_smul]
      abel

lemma endDet_scalarRootFiber (p : ℝ) : LinearMap.det (rootFiber p).toLinearMap = -1 := by
  simpa only [LinearMap.det_toMatrix, Fintype.card_unique, pow_one] using
    det_rootFiber (Basis.singleton Unit ℝ) p

/-- Root coefficient update plus numerator scaling: exact all-scale determinant. -/
theorem endJacobian_rootTransition [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]
    (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E) (x : RootTransitionSpace P E) :
    endJacobian (rootTransition α β L K) x =
      (-1 : ℝ) ^ (Module.finrank ℝ E + 1) * x.2.1.2 ^ Module.finrank ℝ E := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_rootTransition α β L K x),
    rootTransitionDerivative, endDet_lowerBlock, endDet_lowerBlock, endDet_scalarRootFiber]
  simp only [ContinuousLinearMap.coe_id, ContinuousLinearMap.coe_smul, LinearMap.det_id,
    LinearMap.det_smul, one_mul, mul_one]
  rw [neg_eq_neg_one_mul, mul_pow, pow_succ]
  ring

end HydrologyTree
