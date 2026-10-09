import CholletFischerPairs
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open MvPolynomial BapatFiniteRank

namespace Chollet

variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]
noncomputable section

/-- The Gram representation includes singular matrices and the empty type. -/
theorem psd_exists_gram (A : Matrix V V ℝ) (hA : A.PosSemidef) :
    ∃ v : V → V → ℝ, ∀ i j, A i j = scalarProduct (v i) (v j) := by
  let B := CFC.sqrt A
  have hB : B.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hBB : B * B = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  refine ⟨B, fun i j => ?_⟩
  rw [← hBB]
  change (∑ k, B i k * B k j) = ∑ k, B i k * B j k
  apply Finset.sum_congr rfl
  intro k hk
  have h : B k j = B j k := by simpa using hB.apply j k
  rw [h]

theorem permanent_gram_eq (v : V → C → ℝ) :
    Matrix.permanent (fun i j => scalarProduct (v i) (v j)) =
      fischerPair (formsProduct v) (formsProduct v) :=
  permanent_gram_fischer v

theorem permanent_psd_nonneg (A : Matrix V V ℝ) (hA : A.PosSemidef) :
    0 ≤ A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have h : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  rw [h, permanent_gram_eq]
  exact pair_self_nonneg _

theorem formsProduct_singleton_split (v : V → C → ℝ) (i : V) :
    formsProduct v = linearForm (v i) *
      formsProduct (fun j : {j : V // j ≠ i} => v j.val) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => linearForm (v j)) i

/-- The singleton block permanent inequality, proved without assuming Lieb. -/
theorem permanent_psd_singleton (A : Matrix V V ℝ) (hA : A.PosSemidef) (i : V) :
    A i i * Matrix.permanent
      (A.submatrix (fun j : {j : V // j ≠ i} => j.val) Subtype.val) ≤ A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have h : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  rw [h]
  change scalarProduct (v i) (v i) * Matrix.permanent
    (fun j k : {j : V // j ≠ i} => scalarProduct (v j.val) (v k.val)) ≤ _
  rw [permanent_gram_eq, permanent_gram_eq, formsProduct_singleton_split v i]
  exact linear_factor_norm_bound _ _

theorem formsProduct_pair_split (v : V → C → ℝ) (i j : V) (hij : i ≠ j) :
    formsProduct v = linearForm (v i) * (linearForm (v j) *
      formsProduct (fun k : {k : V // k ≠ i ∧ k ≠ j} => v k.val)) := by
  rw [formsProduct_singleton_split v i]
  have hji : j ≠ i := Ne.symm hij
  rw [formsProduct_singleton_split (fun k : {k : V // k ≠ i} => v k.val) ⟨j, hji⟩]
  congr 2
  let e : {k : {k : V // k ≠ i} // k ≠ ⟨j, hji⟩} ≃
      {k : V // k ≠ i ∧ k ≠ j} :=
    { toFun := fun k => ⟨k.val.val, k.val.property, fun h => k.property (Subtype.ext h)⟩
      invFun := fun k => ⟨⟨k.val, k.property.1⟩, fun h => k.property.2 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.prod_comp (fun k => linearForm (v k.val))

/-- The two-vertex block lower bound needed for every matching in Chollet.
The remaining principal submatrix can be singular and can have any size. -/
theorem permanent_psd_pair (A : Matrix V V ℝ) (hA : A.PosSemidef)
    (i j : V) (hij : i ≠ j) :
    (A i i * A j j + (A i j)^2) * Matrix.permanent
      (A.submatrix (fun k : {k : V // k ≠ i ∧ k ≠ j} => k.val) Subtype.val) ≤
      A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have h : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  rw [h]
  change (scalarProduct (v i) (v i) * scalarProduct (v j) (v j) +
    (scalarProduct (v i) (v j))^2) * Matrix.permanent
      (fun k l : {k : V // k ≠ i ∧ k ≠ j} => scalarProduct (v k.val) (v l.val)) ≤ _
  rw [permanent_gram_eq, permanent_gram_eq, formsProduct_pair_split v i j hij]
  exact quadratic_factor_norm_bound _ _ _

end
end Chollet
