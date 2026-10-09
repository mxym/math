import BapatMixedFischer
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual first permanental compound. Rows and columns are deleted
in their original order; the minor is not transposed. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
variable {V W R : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [CommSemiring R]
noncomputable section

def firstCofactor (A : Matrix V V R) (i j : V) : R :=
  BapatFischer.mixedPermanent (fun r : {r : V // r ≠ i} =>
    fun c : {c : V // c ≠ j} => A r.val c.val)

def compound (A : Matrix V V R) : Matrix V V R :=
  fun i j => A i j*firstCofactor A i j

theorem permanent_reindex (A : Matrix V V R) (e : W ≃ V) :
    Matrix.permanent (fun i j => A (e i) (e j)) = A.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv e.permCongr
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.permCongr_apply]

theorem firstCofactor_eq_deletedMinor {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (i j : Fin (n+1)) : firstCofactor A i j =
      Matrix.permanent (A.submatrix i.succAbove j.succAbove) := by
  let ei := finSuccAboveEquiv i
  let ej := finSuccAboveEquiv j
  let e := ei.symm.trans ej
  unfold firstCofactor
  rw [BapatFischer.mixedPermanent_eq_permanent e]
  have h := permanent_reindex
    (fun r c : {r : Fin (n+1) // r ≠ i} => A r.val (e c).val) ei
  have hm : (fun r c : Fin n => A (ei r).val (e (ei c)).val) =
      A.submatrix i.succAbove j.succAbove := by
    ext r c
    change A (ei r).val (ej (ei.symm (ei c))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [← hm]
  exact h.symm

def extendOnePoint (i j : V) (e : {r : V // r ≠ i} ≃ {c : V // c ≠ j}) : Equiv.Perm V :=
  (Equiv.optionSubtypeNe i).symm.trans (e.optionCongr.trans (Equiv.optionSubtypeNe j))

@[simp] theorem extendOnePoint_at (i j : V) (e : {r : V // r ≠ i} ≃ {c : V // c ≠ j}) :
    extendOnePoint i j e i = j := by simp [extendOnePoint]

@[simp] theorem extendOnePoint_complement (i j : V)
    (e : {r : V // r ≠ i} ≃ {c : V // c ≠ j}) (r : {r : V // r ≠ i}) :
    extendOnePoint i j e r.val = (e r).val := by
  simp [extendOnePoint,Equiv.optionSubtypeNe_symm_of_ne r.property]

def restrictOnePoint (i j : V) (σ : Equiv.Perm V) (hσ : σ i=j) :
    {r : V // r ≠ i} ≃ {c : V // c ≠ j} where
  toFun r := ⟨σ r.val,fun h => r.property (σ.injective (h.trans hσ.symm))⟩
  invFun c := ⟨σ.symm c.val,fun h => c.property (by
    calc c.val=σ (σ.symm c.val) := (σ.apply_symm_apply _).symm
         _=σ i := congrArg σ h
         _=j := hσ)⟩
  left_inv r := Subtype.ext (σ.symm_apply_apply r.val)
  right_inv c := Subtype.ext (σ.apply_symm_apply c.val)

def onePointFiberEquiv (i j : V) : {σ : Equiv.Perm V // σ i=j} ≃
    ({r : V // r ≠ i} ≃ {c : V // c ≠ j}) where
  toFun σ := restrictOnePoint i j σ.val σ.property
  invFun e := ⟨extendOnePoint i j e,extendOnePoint_at i j e⟩
  left_inv σ := by
    apply Subtype.ext
    ext r
    by_cases hr : r=i
    · subst r; simpa using σ.property.symm
    · exact extendOnePoint_complement i j (restrictOnePoint i j σ.val σ.property) ⟨r,hr⟩
  right_inv e := by
    ext r
    exact extendOnePoint_complement i j e r

theorem firstCofactor_eq_permutationFiber (A : Matrix V V R) (i j : V) :
    firstCofactor A i j = ∑ σ : {σ : Equiv.Perm V // σ i=j},
      ∏ r : {r : V // r ≠ i},A r.val (σ.val r.val) := by
  unfold firstCofactor BapatFischer.mixedPermanent
  symm
  apply Fintype.sum_equiv (onePointFiberEquiv i j)
  intro σ
  rfl

theorem compound_row_sum (A : Matrix V V R) (i : V) :
    (∑ j,compound A i j) = A.permanent := by
  calc
    _ = ∑ j,∑ σ : {σ : Equiv.Perm V // σ i=j},
        ∏ r,A r (σ.val r) := by
      simp only [compound,firstCofactor_eq_permutationFiber,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro σ _
      rw [Fintype.prod_eq_mul_prod_subtype_ne (fun r => A r (σ.val r)) i,σ.property]
    _ = ∑ σ : Equiv.Perm V,∏ r,A r (σ r) :=
      Fintype.sum_fiberwise (fun σ : Equiv.Perm V => σ i) (fun σ => ∏ r,A r (σ r))
    _ = A.permanent := Matrix.permanent_transpose A

end
end CofactorSpectral
