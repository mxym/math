import HydrologyTree.Triangular

/-! The nonlinear change from root leak/connectors to full root diagonal and
edge products. Its Jacobian is proved at zero rates, without dividing by leaks. -/
open Module Matrix
noncomputable section
namespace HydrologyTree

variable {C Y : Type*} [Fintype C] [DecidableEq C]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def sumCoordinates : (C → ℝ) →L[ℝ] ℝ := ∑ c : C, ContinuousLinearMap.proj c

@[simp] lemma sumCoordinates_apply (f : C → ℝ) : sumCoordinates f = ∑ c, f c := by
  simp [sumCoordinates]

/-- With the child rates frozen, the root leak has coefficient one and each
connector has coefficient equal to its child leak. -/
def couplingFiber (a : C → ℝ) : (ℝ × (C → ℝ)) →L[ℝ] (ℝ × (C → ℝ)) :=
  ((ContinuousLinearMap.fst ℝ ℝ (C → ℝ)) +
    sumCoordinates.comp (ContinuousLinearMap.snd ℝ ℝ (C → ℝ))).prod
    (ContinuousLinearMap.pi fun c => a c •
      (ContinuousLinearMap.proj c).comp (ContinuousLinearMap.snd ℝ ℝ (C → ℝ)))

@[simp] lemma couplingFiber_apply (a : C → ℝ) (z : ℝ × (C → ℝ)) :
    couplingFiber a z = (z.1 + ∑ c, z.2 c, fun c => a c * z.2 c) := by
  simp [couplingFiber]

lemma toMatrix_couplingFiber (a : C → ℝ) :
    LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C))
      ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)) (couplingFiber a).toLinearMap =
    Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) (Matrix.of fun _ _ => 1) 0 (Matrix.diagonal a) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, couplingFiber, sumCoordinates,
      Matrix.one_apply, Matrix.diagonal_apply, Pi.basisFun_apply,
      Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem det_couplingFiber (a : C → ℝ) :
    (LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C))
      ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)) (couplingFiber a).toLinearMap).det =
      ∏ c, a c := by
  rw [toMatrix_couplingFiber, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Keep child data, replace λ by λ+sum f and each f_c by a_c(y) f_c. -/
def rootCoupling (a : Y →L[ℝ] (C → ℝ)) (z : Y × (ℝ × (C → ℝ))) : Y × (ℝ × (C → ℝ)) :=
  (z.1, (z.2.1 + sumCoordinates z.2.2, fun c => a z.1 c * z.2.2 c))

def couplingCross (a : Y →L[ℝ] (C → ℝ)) (f : C → ℝ) : Y →L[ℝ] (ℝ × (C → ℝ)) :=
  (0 : Y →L[ℝ] ℝ).prod
    (ContinuousLinearMap.pi fun c => f c • (ContinuousLinearMap.proj c).comp a)

def rootCouplingDerivative (a : Y →L[ℝ] (C → ℝ)) (z : Y × (ℝ × (C → ℝ))) :
    (Y × (ℝ × (C → ℝ))) →L[ℝ] (Y × (ℝ × (C → ℝ))) :=
  lowerBlock (ContinuousLinearMap.id ℝ Y) (couplingCross a z.2.2) (couplingFiber (a z.1))

/-- Actual derivative, including changes of child leaks with child parameters. -/
theorem hasFDerivAt_rootCoupling (a : Y →L[ℝ] (C → ℝ)) (z : Y × (ℝ × (C → ℝ))) :
    HasFDerivAt (rootCoupling a) (rootCouplingDerivative a z) z := by
  let P : (Y × (ℝ × (C → ℝ))) →L[ℝ] Y := ContinuousLinearMap.fst ℝ Y _
  let Q : (Y × (ℝ × (C → ℝ))) →L[ℝ] (ℝ × (C → ℝ)) := ContinuousLinearMap.snd ℝ Y _
  let L := (ContinuousLinearMap.fst ℝ ℝ (C → ℝ)).comp Q
  let F := (ContinuousLinearMap.snd ℝ ℝ (C → ℝ)).comp Q
  have hd := L.hasFDerivAt.add (sumCoordinates.hasFDerivAt.comp z F.hasFDerivAt)
  have hc : HasFDerivAt (fun w => fun c => a (P w) c * F w c)
      (ContinuousLinearMap.pi fun c =>
        a (P z) c • (ContinuousLinearMap.proj c).comp F +
        F z c • (ContinuousLinearMap.proj c).comp (a.comp P)) z := by
    apply hasFDerivAt_pi.mpr
    intro c
    exact ((ContinuousLinearMap.proj c).comp (a.comp P)).hasFDerivAt.mul
      ((ContinuousLinearMap.proj c).comp F).hasFDerivAt
  apply (P.hasFDerivAt.prodMk (hd.prodMk hc)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change h.2.1 + sumCoordinates h.2.2 = 0 + (h.2.1 + sumCoordinates h.2.2)
      simp
    · funext c
      change a z.1 c * h.2.2 c + z.2.2 c * a h.1 c =
        z.2.2 c * a h.1 c + a z.1 c * h.2.2 c
      ring

/-- The missing connector factor is exactly the product of the child leaks,
even if some or every leak is zero. -/
theorem det_rootCouplingDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ Y) (a : Y →L[ℝ] (C → ℝ)) (z : Y × (ℝ × (C → ℝ))) :
    (LinearMap.toMatrix (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)))
      (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)))
      (rootCouplingDerivative a z).toLinearMap).det = ∏ c, a z.1 c := by
  rw [rootCouplingDerivative, det_lowerBlock, det_couplingFiber]
  simp

theorem rootCoupling_jacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ Y) (a : Y →L[ℝ] (C → ℝ)) (z : Y × (ℝ × (C → ℝ))) :
    (LinearMap.toMatrix (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)))
      (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ C)))
      (fderiv ℝ (rootCoupling a) z).toLinearMap).det = ∏ c, a z.1 c := by
  rw [(hasFDerivAt_rootCoupling a z).fderiv, det_rootCouplingDerivative]

end HydrologyTree
