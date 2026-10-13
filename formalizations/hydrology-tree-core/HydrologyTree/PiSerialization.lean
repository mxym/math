import HydrologyTree.BranchStep
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Pi

/-! Exact serialization of independently indexed child coefficient spaces into
the all-arity gluing coordinates. No dimension matching is assumed. -/
open Module Polynomial
noncomputable section
namespace HydrologyTree

def finPiHeadTail {k : ℕ} (E : Fin (k+1) → Type*)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] :
    ((i : Fin (k+1)) → E i) ≃ₗ[ℝ] E 0 × ((i : Fin k) → E i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree list with definitional head/tail reduction. -/
@[reducible] def finDegreeList : {k : ℕ} → (Fin k → ℕ) → List ℕ
  | 0, _ => []
  | k+1, m => m 0 :: finDegreeList (fun i : Fin k => m i.succ)

lemma finDegreeList_eq_ofFn {k : ℕ} (m : Fin k → ℕ) : finDegreeList m = List.ofFn m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [finDegreeList, List.ofFn_succ, ih]

/-- Serialize actual bounded polynomials without changing coefficient values. -/
def piCoefficientsFinEquiv : {k : ℕ} → (m : Fin k → ℕ) →
    ((i : Fin k) → Coeff (m i)) ≃ₗ[ℝ] ProductInput (finDegreeList m)
  | 0, m => by
    have : Subsingleton (Coeff 0) := (degreeLTEquiv ℝ 0).injective.subsingleton
    exact LinearEquiv.ofSubsingleton _ _
  | k+1, m =>
    (finPiHeadTail (fun i => Coeff (m i))).trans
      ((LinearEquiv.refl ℝ (Coeff (m 0))).prodCongr
        (piCoefficientsFinEquiv (fun i : Fin k => m i.succ)))

lemma piCoefficientsFinEquiv_polynomials {k : ℕ} (m : Fin k → ℕ)
    (p : (i : Fin k) → Coeff (m i)) :
    familyPolynomials (finDegreeList m) (piCoefficientsFinEquiv m p) =
      List.ofFn (fun i : Fin k => (monicPoly (p i) : ℝ[X])) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ]
    change (monicPoly (p 0) : ℝ[X]) ::
      familyPolynomials (finDegreeList (fun i : Fin k => m i.succ))
        (piCoefficientsFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ)) = _
    rw [ih]

variable {I : Type*} [Fintype I]

@[reducible] def degreeSequence (m : I → ℕ) : List ℕ :=
  finDegreeList (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i))

/-- The enumeration depends only on the finite index type, never on rates. -/
def piCoefficientsEquiv (m : I → ℕ) :
    ((i : I) → Coeff (m i)) ≃ₗ[ℝ] ProductInput (degreeSequence m) :=
  (LinearEquiv.piCongrLeft' ℝ (fun i : I => Coeff (m i)) (Fintype.equivFin I)).trans
    (piCoefficientsFinEquiv (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i)))

lemma degreeSequence_sum (m : I → ℕ) : (degreeSequence m).sum = ∑ i : I, m i := by
  rw [degreeSequence, finDegreeList_eq_ofFn, List.sum_ofFn]
  exact (Fintype.equivFin I).symm.sum_comp m

lemma degreeSequence_addOne (m : I → ℕ) :
    degreeSequence (fun i => m i+1) = ChildFactorDegrees (degreeSequence m) := by
  simp only [degreeSequence, finDegreeList_eq_ofFn, ChildFactorDegrees, List.map_ofFn, Function.comp_def]

def productInputCast {ms ns : List ℕ} (h : ms = ns) : ProductInput ms ≃ₗ[ℝ] ProductInput ns := by
  subst ns
  exact LinearEquiv.refl ℝ _

def piScaleSlotsEquiv (m : I → ℕ) :
    ((i : I) → Coeff (m i+1)) ≃ₗ[ℝ] ScaledFamilyInput (degreeSequence m) :=
  (piCoefficientsEquiv (fun i => m i+1)).trans (productInputCast (degreeSequence_addOne m))

lemma piCoefficientsEquiv_polynomials (m : I → ℕ) (p : (i : I) → Coeff (m i)) :
    familyPolynomials (degreeSequence m) (piCoefficientsEquiv m p) =
      List.ofFn (fun i : Fin (Fintype.card I) =>
        (monicPoly (p ((Fintype.equivFin I).symm i)) : ℝ[X])) := by
  apply piCoefficientsFinEquiv_polynomials

end HydrologyTree
