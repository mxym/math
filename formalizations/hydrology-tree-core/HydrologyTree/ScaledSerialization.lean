import HydrologyTree.PiSerialization
import HydrologyTree.FamilyCoordinateEnergy

/-! Actual child numerator slots in finite-list gluing coordinates. The leading
coefficient is its connector scale and the remaining coefficients are a monic
child cofactor. Serialization changes no coefficient value. -/
open Polynomial
noncomputable section
namespace HydrologyTree

def piScaledFinEquiv : {k : ℕ} → (m : Fin k → ℕ) →
    ((i : Fin k) → Coeff (m i+1)) ≃ₗ[ℝ] ScaledFamilyInput (finDegreeList m)
  | 0, m => by
    change ((i : Fin 0) → Coeff (m i+1)) ≃ₗ[ℝ] Coeff 0
    have : Subsingleton (Coeff 0) := (degreeLTEquiv ℝ 0).injective.subsingleton
    exact LinearEquiv.ofSubsingleton _ _
  | k+1, m =>
    (finPiHeadTail (fun i => Coeff (m i+1))).trans
      ((LinearEquiv.refl ℝ (Coeff (m 0+1))).prodCongr
        (piScaledFinEquiv (fun i : Fin k => m i.succ)))

lemma piScaledFin_polynomials {k : ℕ} (m : Fin k → ℕ)
    (p : (i : Fin k) → Coeff (m i+1)) :
    familyPolynomials (ChildFactorDegrees (finDegreeList m)) (piScaledFinEquiv m p) =
      List.ofFn (fun i : Fin k => (monicPoly (p i) : ℝ[X])) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ]
    change (monicPoly (p 0) : ℝ[X]) ::
      familyPolynomials (ChildFactorDegrees (finDegreeList (fun i : Fin k => m i.succ)))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ)) = _
    rw [ih]

lemma piScaledFin_weight {k : ℕ} (m : Fin k → ℕ)
    (p : (i : Fin k) → Coeff (m i+1)) :
    scaleFamilyWeight (finDegreeList m) (piScaledFinEquiv m p) =
      ∏ i : Fin k, (p i : ℝ[X]).coeff (m i) ^ (m i) := by
  induction k with
  | zero => simp [finDegreeList,scaleFamilyWeight]
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    change (p 0 : ℝ[X]).coeff (m 0) ^ (m 0) *
      scaleFamilyWeight (finDegreeList (fun i : Fin k => m i.succ))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ)) = _
    rw [ih]

lemma piScaledFin_scale {k : ℕ} (m : Fin k → ℕ)
    (p : (i : Fin k) → Coeff (m i+1)) :
    scaleFamily (finDegreeList m) (piScaledFinEquiv m p) =
      piScaledFinEquiv m (fun i => scaleLeading (m i) (p i)) := by
  induction k with
  | zero =>
    change (_ : Coeff 0) = _
    have : Subsingleton (Coeff 0) := (degreeLTEquiv ℝ 0).injective.subsingleton
    exact Subsingleton.elim _ _
  | succ k ih =>
    change (scaleLeading (m 0) (p 0),
      scaleFamily (finDegreeList (fun i : Fin k => m i.succ))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ))) = _
    rw [ih]
    rfl

lemma piScaledFin_dot {k : ℕ} (m : Fin k → ℕ)
    (p q : (i : Fin k) → Coeff (m i+1)) :
    familyCoordinateDot (ChildFactorDegrees (finDegreeList m))
      (piScaledFinEquiv m p) (piScaledFinEquiv m q) =
        ∑ i : Fin k, coefficientDot (m i+1) (p i) (q i) := by
  induction k with
  | zero =>
    change (0 : ℝ) = ∑ i : Fin 0, coefficientDot (m i+1) (p i) (q i)
    simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    change coefficientDot (m 0+1) (p 0) (q 0) +
      familyCoordinateDot (ChildFactorDegrees (finDegreeList (fun i : Fin k => m i.succ)))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => q i.succ)) = _
    rw [ih]

variable {I : Type*} [Fintype I]

def piScaledEquiv (m : I → ℕ) :
    ((i : I) → Coeff (m i+1)) ≃ₗ[ℝ] ScaledFamilyInput (degreeSequence m) :=
  (LinearEquiv.piCongrLeft' ℝ (fun i => Coeff (m i+1)) (Fintype.equivFin I)).trans
    (piScaledFinEquiv (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i)))

lemma piScaled_polynomials (m : I → ℕ) (p : (i : I) → Coeff (m i+1)) :
    familyPolynomials (ChildFactorDegrees (degreeSequence m)) (piScaledEquiv m p) =
      List.ofFn (fun i : Fin (Fintype.card I) => (monicPoly (p ((Fintype.equivFin I).symm i)) : ℝ[X])) :=
  piScaledFin_polynomials _ _

lemma piScaled_weight (m : I → ℕ) (p : (i : I) → Coeff (m i+1)) :
    scaleFamilyWeight (degreeSequence m) (piScaledEquiv m p) =
      ∏ i : I, (p i : ℝ[X]).coeff (m i) ^ (m i) := by
  have h := piScaledFin_weight (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i))
    (fun i : Fin (Fintype.card I) => p ((Fintype.equivFin I).symm i))
  exact h.trans ((Fintype.equivFin I).symm.prod_comp (fun i => (p i : ℝ[X]).coeff (m i)^m i))

lemma piScaled_scale (m : I → ℕ) (p : (i : I) → Coeff (m i+1)) :
    scaleFamily (degreeSequence m) (piScaledEquiv m p) =
      piScaledEquiv m (fun i => scaleLeading (m i) (p i)) :=
  piScaledFin_scale _ _

lemma piScaled_dot (m : I → ℕ) (p q : (i : I) → Coeff (m i+1)) :
    familyCoordinateDot (ChildFactorDegrees (degreeSequence m))
      (piScaledEquiv m p) (piScaledEquiv m q) =
        ∑ i : I, coefficientDot (m i+1) (p i) (q i) := by
  have h := piScaledFin_dot (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i))
    (fun i : Fin (Fintype.card I) => p ((Fintype.equivFin I).symm i))
    (fun i : Fin (Fintype.card I) => q ((Fintype.equivFin I).symm i))
  exact h.trans ((Fintype.equivFin I).symm.sum_comp (fun i => coefficientDot (m i+1) (p i) (q i)))

lemma piScaled_product (m : I → ℕ) (p : (i : I) → Coeff (m i+1)) :
    (monicPoly (familyProduct (ChildFactorDegrees (degreeSequence m)) (piScaledEquiv m p)) : ℝ[X]) =
      ∏ i : I, (monicPoly (p i) : ℝ[X]) := by
  rw [familyProduct_reconstruct,piScaled_polynomials,List.prod_ofFn]
  exact (Fintype.equivFin I).symm.prod_comp (fun i : I => (monicPoly (p i) : ℝ[X]))

end HydrologyTree
