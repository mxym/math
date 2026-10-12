import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
namespace Bapat

/-- The actual remaining row/column indices, keeping their original indices. -/
abbrev Remaining {n : ℕ} (i j : Fin n) := {r : Fin n // r ≠ i ∧ r ≠ j}

/-- Actual permanent of the two-row/two-column deletion, indexed without choosing a relabeling. -/
def minorPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j k l : Fin n) : ℂ :=
  ∑ e : Remaining i j ≃ Remaining k l, ∏ r : Remaining i j, A r (e r)

/-- Actual full permutations with prescribed images for two distinct rows. -/
abbrev Prescribed {n : ℕ} (i j k l : Fin n) :=
  {σ : Equiv.Perm (Fin n) // σ i = k ∧ σ j = l}

 def restrictPrescribed {n : ℕ} {i j k l : Fin n}
    (σ : Prescribed i j k l) : Remaining i j ≃ Remaining k l :=
  σ.val.subtypeEquiv (by
    intro r
    constructor
    · intro hr
      constructor
      · intro h; exact hr.1 (σ.val.injective (h.trans σ.property.1.symm))
      · intro h; exact hr.2 (σ.val.injective (h.trans σ.property.2.symm))
    · intro hr
      constructor
      · intro h; exact hr.1 (by simpa [h] using σ.property.1)
      · intro h; exact hr.2 (by simpa [h] using σ.property.2))

 def extendRemaining {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : Remaining i j ≃ Remaining k l) : Equiv.Perm (Fin n) where
  toFun r := if hri : r = i then k else if hrj : r = j then l else e ⟨r,hri,hrj⟩
  invFun c := if hck : c = k then i else if hcl : c = l then j else e.symm ⟨c,hck,hcl⟩
  left_inv r := by
    by_cases hri : r = i
    · subst r; simp
    by_cases hrj : r = j
    · subst r; simp [hij.symm, hkl.symm]
    have h1 := (e ⟨r,hri,hrj⟩).property.1
    have h2 := (e ⟨r,hri,hrj⟩).property.2
    simp only [dite_eq_right hri, dite_eq_right hrj, dite_eq_right h1, dite_eq_right h2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨r,hri,hrj⟩)
  right_inv c := by
    by_cases hck : c = k
    · subst c; simp
    by_cases hcl : c = l
    · subst c; simp [hkl.symm, hij.symm]
    have h1 := (e.symm ⟨c,hck,hcl⟩).property.1
    have h2 := (e.symm ⟨c,hck,hcl⟩).property.2
    simp only [dite_eq_right hck, dite_eq_right hcl, dite_eq_right h1, dite_eq_right h2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨c,hck,hcl⟩)

 theorem extendRemaining_i {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : Remaining i j ≃ Remaining k l) : extendRemaining hij hkl e i = k := by
  simp [extendRemaining]
 theorem extendRemaining_j {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : Remaining i j ≃ Remaining k l) : extendRemaining hij hkl e j = l := by
  simp [extendRemaining, hij.symm]
 theorem extendRemaining_other {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : Remaining i j ≃ Remaining k l) (r : Remaining i j) :
    extendRemaining hij hkl e r = (e r).val := by
  simp [extendRemaining, r.property.1, r.property.2]

/-- The precise bijection used in the two-row permanent expansion. -/
 def prescribedEquivRemaining {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) :
    Prescribed i j k l ≃ (Remaining i j ≃ Remaining k l) where
  toFun := restrictPrescribed
  invFun e := ⟨extendRemaining hij hkl e,
    extendRemaining_i hij hkl e, extendRemaining_j hij hkl e⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro r
    by_cases hri : r = i
    · subst r; rw [extendRemaining_i]; exact σ.property.1.symm
    by_cases hrj : r = j
    · subst r; rw [extendRemaining_j]; exact σ.property.2.symm
    simp [extendRemaining, hri, hrj, restrictPrescribed, Equiv.subtypeEquiv]
  right_inv e := by
    apply Equiv.ext
    intro r
    apply Subtype.ext
    exact extendRemaining_other hij hkl e r

 theorem product_split_two {n : ℕ} (f : Fin n → ℂ) {i j : Fin n} (hij : i ≠ j) :
    (∏ r, f r) = f i * f j * ∏ r : Remaining i j, f r := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne f i]
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun r : {r : Fin n // r ≠ i} => f r)
    ⟨j,hij.symm⟩]
  rw [mul_assoc]
  congr 1
  congr 1
  let E : {r : {r : Fin n // r ≠ i} // r ≠ ⟨j,hij.symm⟩} ≃ Remaining i j :=
    { toFun := fun r => ⟨r.val.val, r.val.property,
        fun h => r.property (Subtype.ext h)⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩,
        fun h => r.property.2 (congrArg Subtype.val h)⟩
      left_inv := fun r => by rfl
      right_inv := fun r => by rfl }
  exact Fintype.prod_equiv E _ _ (fun r => rfl)

 theorem prescribed_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Prescribed i j k l, ∏ r : Fin n, A r (σ.val r)) =
      A i k * A j l * minorPermanent A i j k l := by
  calc
    _ = ∑ e : Remaining i j ≃ Remaining k l,
        A i k * A j l * ∏ r : Remaining i j, A r (e r) := by
      apply Fintype.sum_equiv (prescribedEquivRemaining hij hkl)
      intro σ
      rw [product_split_two (fun r => A r (σ.val r)) hij]
      simp only [σ.property.1, σ.property.2]
      rfl
    _ = _ := by rw [← Finset.mul_sum]; rfl

 theorem prescribed_sum_ite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Equiv.Perm (Fin n),
      if σ i = k ∧ σ j = l then ∏ r : Fin n, A r (σ r) else 0) =
      A i k * A j l * minorPermanent A i j k l := by
  rw [← prescribed_sum A hij hkl, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

 theorem minorPermanent_swap_cols {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j k l : Fin n) : minorPermanent A i j l k = minorPermanent A i j k l := by
  let E : Remaining l k ≃ Remaining k l :=
    Equiv.subtypeEquivRight (fun r => and_comm)
  unfold minorPermanent
  apply Fintype.sum_equiv ((Equiv.refl (Remaining i j)).equivCongr E)
  intro e
  rfl

/-- This complement-indexed definition is the ordinary permanent after any row/column relabeling.
In particular one may choose the increasing labels to get the ordered deleted matrix in the paper. -/
 theorem minorPermanent_eq_submatrix_permanent {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n)
    (eR : Fin m ≃ Remaining i j) (eC : Fin m ≃ Remaining k l) :
    minorPermanent A i j k l =
      (A.submatrix (fun r => (eR r).val) (fun c => (eC c).val)).permanent := by
  rw [← Matrix.permanent_transpose]
  unfold minorPermanent Matrix.permanent
  symm
  apply Fintype.sum_equiv (eR.equivCongr eC)
  intro σ
  apply Fintype.prod_equiv eR
  intro r
  simp

end Bapat
