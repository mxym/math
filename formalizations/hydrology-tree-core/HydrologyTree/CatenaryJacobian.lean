import HydrologyTree.PathInduction

/-! Endpoint-catenary Jacobian for every finite size, evaluated on the actual
physical characteristic/root-cofactor coefficient map and original rate arrays.
The displayed bases only permute the explicitly defined scalar coordinates. -/
open Module Matrix Polynomial
noncomputable section
namespace HydrologyTree

@[reducible] def PathCoordinateIndex : ℕ → Type
  | 0 => Unit
  | n+1 => PathCoordinateIndex n ⊕ (Unit ⊕ Unit)

instance pathCoordinateFintype : (n : ℕ) → Fintype (PathCoordinateIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := pathCoordinateFintype n
    exact inferInstanceAs (Fintype (PathCoordinateIndex n ⊕ (Unit ⊕ Unit)))

instance pathCoordinateDecidableEq (n : ℕ) : DecidableEq (PathCoordinateIndex n) := Classical.decEq _

/-- Every basis vector is a single unscaled physical rate coordinate. -/
def pathRateBasis : (n : ℕ) → Basis (PathCoordinateIndex n) ℝ (PathRates n)
  | 0 => Basis.singleton Unit ℝ
  | n+1 => (pathRateBasis n).prod ((Basis.singleton Unit ℝ).prod (Basis.singleton Unit ℝ))

def catenaryInputBasis (n : ℕ) : Basis (PathCoordinateIndex n) ℝ (TreeRates n) :=
  (pathRateBasis n).map (pathRateEquiv n)

def catenaryOutputBasis (n : ℕ) : Basis (PathCoordinateIndex n) ℝ (PathCoefficients n) :=
  (pathRateBasis n).map (pathCoefficientEquiv n).symm

/-- The determinant of fderiv of the actual original path coefficient map. -/
def catenaryJacobian (n : ℕ) (x : TreeRates n) : ℝ :=
  (LinearMap.toMatrix (catenaryInputBasis n) (catenaryOutputBasis n)
    (fderiv ℝ (pathCoefficientMap n) x).toLinearMap).det

lemma toMatrix_coordinate_transport {E X Y I : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [Fintype I] [DecidableEq I]
    (b : Basis I ℝ E) (ein : E ≃ₗ[ℝ] X) (eout : Y ≃ₗ[ℝ] E) (L : X →ₗ[ℝ] Y) :
    LinearMap.toMatrix (b.map ein) (b.map eout.symm) L =
      LinearMap.toMatrix b b (eout.toLinearMap.comp (L.comp ein.toLinearMap)) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.map_repr]

/-- Exact transport from the common-coordinate induction to the actual derivative. -/
theorem normalizedPathJacobian_eq_catenary (n : ℕ) (z : PathRates n) :
    endJacobian (normalizedPhysicalPath n) z = catenaryJacobian n (pathRateEquiv n z) := by
  have hc := (differentiable_pathCoefficientMap n (pathRateEquiv n z)).hasFDerivAt
  have h := (pathCoefficientEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z
    (hc.comp z (pathRateEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)
  have hd : fderiv ℝ (normalizedPhysicalPath n) z =
      (pathCoefficientEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ (pathCoefficientMap n) (pathRateEquiv n z)).comp
          (pathRateEquiv n).toContinuousLinearEquiv.toContinuousLinearMap) := h.fderiv
  rw [endJacobian, hd, ← LinearMap.det_toMatrix (pathRateBasis n),
    catenaryJacobian, catenaryInputBasis, catenaryOutputBasis, toMatrix_coordinate_transport]
  rfl

/-- Full all-size endpoint-catenary formula, including every zero-rate boundary.
For n edges the inward exponents are n,n-1,...,1 and the outward exponents
are n-1,n-2,...,0. The root leak is unrestricted and contributes no factor. -/
theorem catenaryJacobian_eq (n : ℕ) (x : TreeRates n) :
    catenaryJacobian n x = pathOrientation n *
      ∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1) := by
  have h := normalizedPhysicalPath_jacobian n ((pathRateEquiv n).symm x)
  rw [normalizedPathJacobian_eq_catenary, pathWeight_eq_rate_monomial] at h
  simpa only [LinearEquiv.apply_symm_apply, pathRateMonomial] using h

/-- Orientation-free form of the same exact identity. -/
theorem catenaryJacobian_sq (n : ℕ) (x : TreeRates n) :
    catenaryJacobian n x ^ 2 =
      (∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1)) ^ 2 := by
  rw [catenaryJacobian_eq, mul_pow, pathOrientation_sq, one_mul]

lemma pathOrientation_ne_zero (n : ℕ) : pathOrientation n ≠ 0 := by
  intro h
  have hs := pathOrientation_sq n
  rw [h] at hs
  norm_num at hs

lemma pathRateMonomial_zero_iff (n : ℕ) (x : TreeRates n) :
    pathRateMonomial n x = 0 ↔
      (∃ i : Fin n, x.1 i.succ = 0) ∨
      (∃ i : Fin n, i.val+1 < n ∧ x.2 i = 0) := by
  rw [pathRateMonomial, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i,_,hi⟩
    rcases mul_eq_zero.mp hi with ha | hf
    · left
      refine ⟨i,?_⟩
      by_contra h
      exact (pow_ne_zero _ h) ha
    · right
      have hp : 0 < n-i.val-1 := by
        by_contra h
        have he : n-i.val-1 = 0 := Nat.eq_zero_of_not_pos h
        rw [he, pow_zero] at hf
        exact one_ne_zero hf
      refine ⟨i, by omega, ?_⟩
      by_contra h
      exact (pow_ne_zero _ h) hf
  · intro h
    rcases h with ⟨i,ha⟩ | ⟨i,hi,hf⟩
    · refine ⟨i,Finset.mem_univ i,?_⟩
      have hp : n-i.val ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt i.isLt)
      simp [ha, hp]
    · refine ⟨i,Finset.mem_univ i,?_⟩
      have hp : n-i.val-1 ≠ 0 := by omega
      simp [hf, hp]

/-- Exact real singular set of the original unreduced coefficient map. -/
theorem catenaryJacobian_zero_iff (n : ℕ) (x : TreeRates n) :
    catenaryJacobian n x = 0 ↔
      (∃ i : Fin n, x.1 i.succ = 0) ∨
      (∃ i : Fin n, i.val+1 < n ∧ x.2 i = 0) := by
  rw [catenaryJacobian_eq, mul_eq_zero]
  simp only [pathOrientation_ne_zero, false_or]
  exact pathRateMonomial_zero_iff n x

/-- Inward rates and nonterminal outward rates are exactly the required nonzeros.
The last outward rate and root leak may vanish without Jacobian singularity. -/
theorem catenaryJacobian_ne_zero (n : ℕ) (x : TreeRates n)
    (ha : ∀ i : Fin n, x.1 i.succ ≠ 0)
    (hf : ∀ i : Fin n, i.val+1 < n → x.2 i ≠ 0) : catenaryJacobian n x ≠ 0 := by
  intro hz
  rcases (catenaryJacobian_zero_iff n x).mp hz with (⟨i,hi⟩ | ⟨i,hi,h0⟩)
  · exact ha i hi
  · exact hf i hi h0

end HydrologyTree
