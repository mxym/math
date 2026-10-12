import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push

-- Source: QDefinitions.lean

open scoped BigOperators
open Finset
namespace Bapat

/-- The actual number of inverted pairs of a permutation. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ σ j < σ i then 1 else 0

/-- The row-to-column product in the definition of the permanent. -/
def permutationWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ := ∏ i, A i (σ i)

/-- Bapat's inversion-weighted permanent, as an actual polynomial function. -/
def qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversionCount σ * permutationWeight A σ

/-- The endpoint derivative, not a proxy for it. -/
def endpointDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (inversionCount σ : ℂ) * permutationWeight A σ

 theorem qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    qPermanent A 1 = A.permanent := by
  simp only [qPermanent, one_pow, one_mul, permutationWeight]
  rw [← Matrix.permanent_transpose]
  rfl

 theorem endpointDerivative_pairs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    endpointDerivative A = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then ∑ σ : Equiv.Perm (Fin n),
        if σ j < σ i then permutationWeight A σ else 0 else 0 := by
  unfold endpointDerivative inversionCount
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

 theorem inversionCount_inverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversionCount σ.symm = inversionCount σ := by
  unfold inversionCount
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        if σ i < σ j ∧ j < i then 1 else 0 := by
      rw [← Equiv.sum_comp σ]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Equiv.sum_comp σ]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [and_comm]

end Bapat

-- Source: QPermanent.lean

open scoped BigOperators
namespace Bapat
 theorem hasDerivAt_qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (qPermanent A) (endpointDerivative A) 1 := by
  unfold qPermanent endpointDerivative
  apply HasDerivAt.fun_sum
  intro σ hσ
  simpa using ((hasDerivAt_id (1 : ℂ)).pow (inversionCount σ)).mul_const
    (permutationWeight A σ)

end Bapat

-- Source: MinorPermanent.lean

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

-- Source: EndpointIdentity.lean

open scoped BigOperators
open Finset
namespace Bapat

 theorem row_inversion_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (hij : i < j) :
    (∑ σ : Equiv.Perm (Fin n), if σ j < σ i then permutationWeight A σ else 0) =
      ∑ k : Fin n, ∑ l : Fin n,
        if k < l then A i l * A j k * minorPermanent A i j k l else 0 := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n, ∑ l : Fin n,
        if k < l then
          if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have ht (k l : Fin n) :
          (if k < l then
            if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0) =
          if σ j = k then if σ i = l then
            if k < l then permutationWeight A σ else 0 else 0 else 0 := by
        by_cases h1 : k < l <;> by_cases h2 : σ i = l <;>
          by_cases h3 : σ j = k <;> simp [h1,h2,h3]
      simp_rw [ht]
      simp
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if k < l then
          if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k < l
      · simp only [hkl, ite_true]
        simp only [permutationWeight]
        rw [prescribed_sum_ite A (ne_of_lt hij) (ne_of_gt hkl)]
        rw [minorPermanent_swap_cols]
      · simp [hkl]

/-- The exact two-row/two-column deleted-minor formula for the endpoint derivative. -/
 theorem endpointDerivative_minor_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    endpointDerivative A = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then ∑ k : Fin n, ∑ l : Fin n,
        if k < l then A i l * A j k * minorPermanent A i j k l else 0 else 0 := by
  rw [endpointDerivative_pairs]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ite_true]
    exact row_inversion_sum A hij
  · simp [hij]

end Bapat

namespace Bapat
 theorem sum_distinct_pairs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    (∑ k : Fin n, ∑ l : Fin n, if k ≠ l then f k l else 0) =
      ∑ k : Fin n, ∑ l : Fin n, if k < l then f k l + f l k else 0 := by
  have hs (k l : Fin n) :
      (if k ≠ l then f k l else 0) =
        (if k < l then f k l else 0) + (if l < k then f k l else 0) := by
    rcases lt_trichotomy k l with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst l; simp
    · simp [h, ne_of_gt h, not_lt_of_ge (le_of_lt h)]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k l : Fin n => if l < k then f k l else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k < l <;> simp [h]

 theorem permanent_two_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (hij : i ≠ j) :
    A.permanent = ∑ k : Fin n, ∑ l : Fin n, if k < l then
      (A i k * A j l + A i l * A j k) * minorPermanent A i j k l else 0 := by
  have hweight : A.permanent = ∑ σ : Equiv.Perm (Fin n), permutationWeight A σ := by
    rw [← qPermanent_one]
    simp [qPermanent]
  rw [hweight]
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n, ∑ l : Fin n,
        if σ i = k ∧ σ j = l then permutationWeight A σ else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [ite_and]
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if σ i = k ∧ σ j = l then permutationWeight A σ else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then
        A i k * A j l * minorPermanent A i j k l else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k ≠ l
      · change (∑ σ : Equiv.Perm (Fin n),
          if σ i = k ∧ σ j = l then ∏ r : Fin n, A r (σ r) else 0) =
          if k ≠ l then A i k * A j l * minorPermanent A i j k l else 0
        rw [ite_eq_left hkl]
        exact prescribed_sum_ite A hij hkl
      · have heq : k = l := not_ne_iff.mp hkl
        subst l
        have hnone (σ : Equiv.Perm (Fin n)) : ¬(σ i = k ∧ σ j = k) := by
          intro h; exact hij (σ.injective (h.1.trans h.2.symm))
        simp [hnone]
    _ = _ := by
      rw [sum_distinct_pairs]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k < l
      · simp only [hkl, ite_true]
        rw [minorPermanent_swap_cols]
        ring
      · simp [hkl]
end Bapat

-- Source: EndpointDefect.lean

open scoped BigOperators
open Finset
namespace Bapat

/-- The actual determinant of the indicated ordered two-by-two minor. -/
def pairDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n) : ℂ :=
  Matrix.det (fun r c : Fin 2 => A (if r = 0 then i else j) (if c = 0 then k else l))

 theorem pairDeterminant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n) :
    pairDeterminant A i j k l = A i k * A j l - A i l * A j k := by
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    fun r c => A (if r = 0 then i else j) (if c = 0 then k else l)
  simpa [pairDeterminant, M] using Matrix.det_fin_two M

/-- The paper's signed deleted-minor sum, with actual determinants and actual permanents. -/
def endpointDefect {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ∑ k : Fin n, ∑ l : Fin n,
    if k < l then pairDeterminant A i j k l * minorPermanent A i j k l else 0 else 0

 theorem sum_row_pairs_const {n : ℕ} (c : ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then c else 0) =
      ((n * (n - 1) / 2 : ℕ) : ℂ) * c := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => if p.1 < p.2 then c else 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]

 theorem endpointDerivative_defect_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    2 * endpointDerivative A = ((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent -
      endpointDefect A := by
  have hexp :
      (∑ i : Fin n, ∑ j : Fin n, if i < j then ∑ k : Fin n, ∑ l : Fin n,
        if k < l then (A i k * A j l + A i l * A j k) *
          minorPermanent A i j k l else 0 else 0) =
      ((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent := by
    rw [← sum_row_pairs_const]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, ite_true]
      exact (permanent_two_rows A (ne_of_lt hij)).symm
    · simp [hij]
  rw [endpointDerivative_minor_formula, ← hexp]
  unfold endpointDefect
  simp_rw [pairDeterminant_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ite_true]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hkl : k < l <;> simp [hkl] <;> ring
  · simp [hij]

/-- The direct analytic version of the endpoint identity. -/
 theorem hasDerivAt_qPermanent_defect {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (qPermanent A)
      ((((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent - endpointDefect A) / 2) 1 := by
  convert hasDerivAt_qPermanent_one A using 1
  have h := endpointDerivative_defect_identity A
  apply (div_eq_iff (two_ne_zero : (2 : ℂ) ≠ 0)).2
  simpa [mul_comm] using h.symm

end Bapat

-- Source: HermitianReality.lean

open scoped BigOperators
namespace Bapat
 theorem star_permutationWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (σ : Equiv.Perm (Fin n)) :
    star (permutationWeight A σ) = permutationWeight A σ.symm := by
  unfold permutationWeight
  rw [star_prod]
  simp only [hA.apply]
  simpa using Equiv.prod_comp σ (fun r => A r (σ.symm r))

/-- The actual q-permanent is real on the real axis for a Hermitian matrix. -/
 theorem star_qPermanent_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) : star (qPermanent A (q : ℂ)) = qPermanent A (q : ℂ) := by
  unfold qPermanent
  rw [star_sum]
  simp only [star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
  simp_rw [← Complex.star_def, star_permutationWeight A hA]
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        (q : ℂ) ^ inversionCount σ.symm * permutationWeight A σ.symm := by
      simp_rw [inversionCount_inverse]
      simp only [mul_comm]
    _ = _ := by
      let E : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
        ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
      exact Equiv.sum_comp E (fun σ =>
        (q : ℂ) ^ inversionCount σ * permutationWeight A σ)

end Bapat

-- Source: ProductBounds.lean

open scoped BigOperators

namespace BapatBounds

theorem product_norm_bound {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i ∈ s, ‖a i‖ ≤ R) :
    ‖∏ i ∈ s, a i‖ ≤ R ^ s.card := by
  calc
    ‖∏ i ∈ s, a i‖ ≤ ∏ i ∈ s, ‖a i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, R := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) ha
    _ = R ^ s.card := by simp

/-- A telescoping bound, including the empty product and zero-radius cases. -/
theorem product_difference_bound {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ R) (hb : ∀ i ∈ s, ‖b i‖ ≤ R)
    (hd : ∀ i ∈ s, ‖a i - b i‖ ≤ t) :
    ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤ (s.card : ℝ) * t * R ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have hbi := hb i (Finset.mem_insert_self i s)
    have hdi := hd i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, ‖a j‖ ≤ R := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, ‖b j‖ ≤ R := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hds : ∀ j ∈ s, ‖a j - b j‖ ≤ t := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    specialize ih has hbs hds
    by_cases hs : s.card = 0
    · have : s = ∅ := Finset.card_eq_zero.mp hs
      subst s
      simpa using hdi
    have hsp : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs
    have hpow : R * R ^ (s.card - 1) = R ^ s.card := by
      rw [← pow_succ']
      congr 1
      omega
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have heq : a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j) =
        (a i - b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) := by ring
    rw [heq]
    calc
      _ ≤ ‖(a i - b i) * (∏ j ∈ s, a j)‖ +
          ‖b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)‖ := norm_add_le _ _
      _ = ‖a i - b i‖ * ‖∏ j ∈ s, a j‖ +
          ‖b i‖ * ‖(∏ j ∈ s, a j) - ∏ j ∈ s, b j‖ := by simp only [norm_mul]
      _ ≤ t * R ^ s.card + R * ((s.card : ℝ) * t * R ^ (s.card - 1)) :=
        add_le_add (mul_le_mul hdi (product_norm_bound s a R hR has) (norm_nonneg _) ht)
          (mul_le_mul hbi ih (norm_nonneg _) hR)
      _ = ((s.card + 1 : ℕ) : ℝ) * t * R ^ (s.card + 1 - 1) := by
        rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        calc
          _ = t * R ^ s.card + (s.card : ℝ) * t * (R * R ^ (s.card - 1)) := by ring
          _ = _ := by rw [hpow]; ring

/-- The actual matrix product along any permutation has the same bound. -/
theorem permutation_product_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n))
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (hB : ∀ i j, ‖B i j‖ ≤ R)
    (hd : ∀ i j, ‖A i j - B i j‖ ≤ t) :
    ‖(∏ i, A i (σ i)) - ∏ i, B i (σ i)‖ ≤ (n : ℝ) * t * R ^ (n - 1) := by
  simpa using product_difference_bound Finset.univ (fun i => A i (σ i))
    (fun i => B i (σ i)) R t hR ht (fun i _ => hA i (σ i))
    (fun i _ => hB i (σ i)) (fun i _ => hd i (σ i))

end BapatBounds

-- Source: PolynomialBounds.lean

open scoped BigOperators
open Set

namespace BapatBounds

def realPolynomial {ι : Type*} [Fintype ι] (e : ι → ℕ) (c : ι → ℝ)
    (q : ℝ) : ℝ := ∑ i, q ^ e i * c i

def realDerivative {ι : Type*} [Fintype ι] (e : ι → ℕ) (c : ι → ℝ)
    (q : ℝ) : ℝ := ∑ i, (e i : ℝ) * q ^ (e i - 1) * c i

theorem realPolynomial_hasDerivAt {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (q : ℝ) :
    HasDerivAt (realPolynomial e c) (realDerivative e c q) q := by
  unfold realPolynomial realDerivative
  apply HasDerivAt.fun_sum
  intro i hi
  simpa using ((hasDerivAt_id q).pow (e i)).mul_const (c i)

theorem realPolynomial_deriv {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (q : ℝ) :
    deriv (realPolynomial e c) q = realDerivative e c q :=
  (realPolynomial_hasDerivAt e c q).deriv

theorem abs_pow_sub_one_bound (q : ℝ) (m : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |q ^ m - 1| ≤ (m : ℝ) * (1 - q) := by
  have hpow : ∀ m : ℕ, 1 - q ^ m ≤ (m : ℝ) * (1 - q) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      have hd : 0 ≤ 1 - q := sub_nonneg.mpr hq1
      have hmul : q * (1 - q ^ m) ≤ q * ((m : ℝ) * (1 - q)) :=
        mul_le_mul_of_nonneg_left ih hq0
      have hle : q * ((m : ℝ) * (1 - q)) ≤ (m : ℝ) * (1 - q) :=
        mul_le_of_le_one_left (mul_nonneg hm hd) hq1
      rw [pow_succ, Nat.cast_succ]
      nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_one₀ hq0 hq1))]
  simpa only [neg_sub] using hpow m

/-- Uniform derivative variation for a finite polynomial, with natural exponents.
The bound includes exponents zero and one; truncated subtraction is intentional. -/
theorem realDerivative_difference_bound {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (N : ℕ) (M q : ℝ)
    (hM : 0 ≤ M) (he : ∀ i, e i ≤ N) (hc : ∀ i, |c i| ≤ M)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |realDerivative e c q - realDerivative e c 1| ≤
      (Fintype.card ι : ℝ) * (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) := by
  classical
  have hdelta : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hterm (i : ι) :
      |(e i : ℝ) * q ^ (e i - 1) * c i - (e i : ℝ) * 1 ^ (e i - 1) * c i| ≤
        (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) := by
    have he0 : 0 ≤ (e i : ℝ) := Nat.cast_nonneg _
    have heb : (e i : ℝ) * ((e i - 1 : ℕ) : ℝ) ≤
        (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul (he i) (Nat.sub_le_sub_right (he i) 1)
    have hx : |q ^ (e i - 1) - 1| ≤ ((e i - 1 : ℕ) : ℝ) * (1 - q) :=
      abs_pow_sub_one_bound q _ hq0 hq1
    have heq : (e i : ℝ) * q ^ (e i - 1) * c i - (e i : ℝ) * 1 ^ (e i - 1) * c i =
        (e i : ℝ) * (q ^ (e i - 1) - 1) * c i := by simp; ring
    rw [heq, abs_mul, abs_mul, abs_of_nonneg he0]
    calc
      _ ≤ (e i : ℝ) * (((e i - 1 : ℕ) : ℝ) * (1 - q)) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he0) (hc i) (abs_nonneg _)
          (mul_nonneg he0 (mul_nonneg (Nat.cast_nonneg _) hdelta))
      _ = ((e i : ℝ) * ((e i - 1 : ℕ) : ℝ)) * (M * (1 - q)) := by ring
      _ ≤ ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) * (M * (1 - q)) :=
        mul_le_mul_of_nonneg_right heb (mul_nonneg hM hdelta)
      _ = _ := by ring
  unfold realDerivative
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(e i : ℝ) * q ^ (e i - 1) * c i -
        (e i : ℝ) * 1 ^ (e i - 1) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_assoc]

/-- An explicit interval witnessing failure of monotonicity. The hypotheses
are derivative and variation bounds, not an assumed optimizer or conclusion. -/
theorem explicit_reverse_interval (f g : ℝ → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hd : ∀ q, HasDerivAt f (g q) q) (h1 : g 1 ≤ -(1 / 4 : ℝ))
    (hvariation : ∀ q ∈ Icc (0 : ℝ) 1, |g q - g 1| ≤ K * (1 - q)) :
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    0 < q₀ ∧ q₀ < 1 ∧ h / 8 ≤ f q₀ - f 1 ∧ f 1 < f q₀ := by
  dsimp
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hK
  have hh : 0 < 1 / (8 * K) := by positivity
  have hh1 : 1 / (8 * K) ≤ (1 / 8 : ℝ) := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hq0 : 0 < 1 - 1 / (8 * K) := by linarith
  have hq1 : 1 - 1 / (8 * K) < 1 := by linarith
  have hk : K * (1 / (8 * K)) = (1 / 8 : ℝ) := by field_simp
  have hder : ∀ q ∈ Icc (1 - 1 / (8 * K)) 1, deriv f q ≤ -(1 / 8 : ℝ) := by
    intro q hq
    rw [(hd q).deriv]
    have hnonneg : 0 ≤ q := hq0.le.trans hq.1
    have hv := hvariation q ⟨hnonneg, hq.2⟩
    have hup := (abs_le.mp hv).2
    have hbound : K * (1 - q) ≤ K * (1 / (8 * K)) := by
      apply mul_le_mul_of_nonneg_left _ hKp.le
      linarith [hq.1]
    linarith
  have hdiff : Differentiable ℝ f := fun q => (hd q).differentiableAt
  have hs := (convex_Icc (1 - 1 / (8 * K)) (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun q hq => hder q (interior_subset hq))
    (1 - 1 / (8 * K)) ⟨le_rfl, hq1.le⟩ 1 ⟨hq1.le, le_rfl⟩ hq1.le
  refine ⟨hq0, hq1, ?_, ?_⟩
  · linarith
  · have hh8 : 0 < 1 / (8 * K) / 8 := by positivity
    linarith

end BapatBounds

-- Source: MatrixPerturbation.lean

open scoped BigOperators ComplexOrder

namespace BapatBounds

def diagonalPerturbation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  A + Matrix.diagonal (fun _ => (t : ℂ))

theorem diagonalPerturbation_difference {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (ht : 0 ≤ t) (i j : Fin n) :
    ‖diagonalPerturbation A t i j - A i j‖ ≤ t := by
  by_cases hij : i = j
  · subst j
    simp [diagonalPerturbation, Matrix.diagonal_apply, abs_of_nonneg ht]
  · simp [diagonalPerturbation, Matrix.diagonal_apply, hij, ht]

theorem diagonalPerturbation_entries {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i j, ‖diagonalPerturbation A t i j‖ ≤ R + 1 := by
  intro i j
  have hd := diagonalPerturbation_difference A t ht i j
  have heq : diagonalPerturbation A t i j =
      A i j + (diagonalPerturbation A t i j - A i j) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith [hA i j])

/-- Positive definiteness for the actual perturbed Gram matrix; no eigenvalue
or spectral gap hypothesis is supplied. -/
theorem gram_diagonalPerturbation_posDef {n r : ℕ}
    (V : Matrix (Fin n) (Fin r) ℂ) (t : ℝ) (ht : 0 < t) :
    (diagonalPerturbation (V * V.conjTranspose) t).PosDef := by
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_self_mul_conjTranspose V)
    (Matrix.PosDef.diagonal (fun _ => Complex.zero_lt_real.mpr ht))

theorem diagonalPerturbation_product_difference {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(∏ i, diagonalPerturbation A t i (σ i)) - ∏ i, A i (σ i)‖ ≤
      (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  apply permutation_product_difference _ _ σ (R + 1) t (by linarith) ht
    (diagonalPerturbation_entries A R t hA ht ht1)
    (fun i j => (hA i j).trans (by linarith))
    (diagonalPerturbation_difference A t ht)

/-- A weighted endpoint sum. Substituting inversionCount gives the actual
endpoint derivative once its combinatorial bound is proved. -/
def weightedEndpoint {n : ℕ} (e : Equiv.Perm (Fin n) → ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ, (e σ : ℂ) * ∏ i, A i (σ i)

theorem weightedEndpoint_perturbation_bound {n : ℕ}
    (e : Equiv.Perm (Fin n) → ℕ) (N : ℕ) (he : ∀ σ, e σ ≤ N)
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖weightedEndpoint e (diagonalPerturbation A t) - weightedEndpoint e A‖ ≤
      (N : ℝ) * (n.factorial : ℝ) * (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  classical
  unfold weightedEndpoint
  rw [← Finset.sum_sub_distrib]
  have hterm (σ : Equiv.Perm (Fin n)) :
      ‖(e σ : ℂ) * (∏ i, diagonalPerturbation A t i (σ i)) -
        (e σ : ℂ) * (∏ i, A i (σ i))‖ ≤
        (N : ℝ) * ((n : ℝ) * t * (R + 1) ^ (n - 1)) := by
    rw [← mul_sub, norm_mul, Complex.norm_natCast]
    exact mul_le_mul (by exact_mod_cast he σ)
      (diagonalPerturbation_product_difference A σ R t hR hA ht ht1)
      (norm_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ σ, ‖(e σ : ℂ) * (∏ i, diagonalPerturbation A t i (σ i)) -
        (e σ : ℂ) * (∏ i, A i (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (N : ℝ) * ((n : ℝ) * t * (R + 1) ^ (n - 1)) :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by simp [Fintype.card_perm, mul_assoc, mul_left_comm]

end BapatBounds

-- Source: InversionBounds.lean

open scoped BigOperators

namespace BapatBounds

theorem ordered_pairs_count (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0 : ℕ) = n.choose 2 := by
  rw [Finset.sum_comm]
  have inner (j : Fin n) : (∑ i : Fin n, if i < j then 1 else 0 : ℕ) = j.val := by
    rw [Finset.sum_boole]
    have heq : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [heq, Fin.card_Iio]
    rfl
  simp_rw [inner]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j), Finset.sum_range_id, Nat.choose_two_right]

/-- Sharp uniform bound on the actual inversion count used by qPermanent. -/
theorem inversionCount_le_choose {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Bapat.inversionCount σ ≤ n.choose 2 := by
  rw [← ordered_pairs_count]
  unfold Bapat.inversionCount
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs <;> omega

end BapatBounds

-- Source: EndpointBridge.lean

open scoped BigOperators
open Set

namespace BapatBounds

theorem realPolynomial_qPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    realPolynomial Bapat.inversionCount (fun σ => (Bapat.permutationWeight A σ).re) q =
      (Bapat.qPermanent A (q : ℂ)).re := by
  simp [realPolynomial, Bapat.qPermanent, Complex.mul_re, ← Complex.ofReal_pow]

theorem realDerivative_endpoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    realDerivative Bapat.inversionCount (fun σ => (Bapat.permutationWeight A σ).re) 1 =
      (Bapat.endpointDerivative A).re := by
  simp [realDerivative, Bapat.endpointDerivative, Complex.mul_re]

theorem real_permutation_coefficient_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (σ : Equiv.Perm (Fin n)) :
    |(Bapat.permutationWeight A σ).re| ≤ R ^ n := by
  apply (Complex.abs_re_le_norm _).trans
  simpa [Bapat.permutationWeight] using
    product_norm_bound Finset.univ (fun i => A i (σ i)) R hR (fun i _ => hA i (σ i))

/-- The actual inversion-weighted endpoint derivative obeys the exact bound
used to make the rank-two complex witness positive definite. -/
theorem endpointDerivative_perturbation_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖Bapat.endpointDerivative (diagonalPerturbation A t) - Bapat.endpointDerivative A‖ ≤
      (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  exact weightedEndpoint_perturbation_bound Bapat.inversionCount (n.choose 2)
    inversionCount_le_choose A R t hR hA ht ht1

/-- The original qPermanent itself, with the stated explicit interval. -/
theorem qPermanent_explicit_reverse_interval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative A).re ≤ -(1 / 4 : ℝ))
    (hK : 1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * R ^ n) :
    let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * R ^ n
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    0 < q₀ ∧ q₀ < 1 ∧ h / 8 ≤
      (Bapat.qPermanent A (q₀ : ℂ)).re - (Bapat.qPermanent A 1).re ∧
      (Bapat.qPermanent A 1).re < (Bapat.qPermanent A (q₀ : ℂ)).re := by
  classical
  let e := Bapat.inversionCount (n := n)
  let c := fun σ : Equiv.Perm (Fin n) => (Bapat.permutationWeight A σ).re
  let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) * (n.factorial : ℝ) * R ^ n
  have hv : ∀ q ∈ Icc (0 : ℝ) 1,
      |realDerivative e c q - realDerivative e c 1| ≤ K * (1 - q) := by
    intro q hq
    have hh := realDerivative_difference_bound e c (n.choose 2) (R ^ n) q
      (pow_nonneg hR _) inversionCount_le_choose
      (real_permutation_coefficient_bound A R hR hA) hq.1 hq.2
    simpa [K, Fintype.card_perm, mul_assoc, mul_left_comm, mul_comm] using hh
  have hd : ∀ q, HasDerivAt (realPolynomial e c) (realDerivative e c q) q :=
    realPolynomial_hasDerivAt e c
  have he1 : realDerivative e c 1 ≤ -(1 / 4 : ℝ) := by
    simpa [e, c, realDerivative_endpoint] using h1
  have hh := explicit_reverse_interval (realPolynomial e c) (realDerivative e c) K hK hd he1 hv
  simpa [e, c, K, realPolynomial_qPermanent] using hh

end BapatBounds

-- Source: NonDiagonal.lean

open scoped BigOperators

namespace BapatBounds

theorem inversionCount_one (n : ℕ) : Bapat.inversionCount (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold Bapat.inversionCount
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Equiv.Perm.one_apply]
  have hfalse : ¬(i < j ∧ j < i) := fun h => (lt_asymm h.1 h.2)
  simp [hfalse]

theorem diagonal_endpointDerivative_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, i ≠ j → A i j = 0) : Bapat.endpointDerivative A = 0 := by
  classical
  unfold Bapat.endpointDerivative
  apply Finset.sum_eq_zero
  intro σ hσmem
  by_cases hσ : σ = 1
  · subst σ
    simp [inversionCount_one]
  have hex : ∃ i, σ i ≠ i := by
    by_contra hn
    push Not at hn
    apply hσ
    apply Equiv.ext
    intro i
    simpa using hn i
  obtain ⟨i, hi⟩ := hex
  have hz : Bapat.permutationWeight A σ = 0 := by
    unfold Bapat.permutationWeight
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hA i (σ i) hi.symm)
  rw [hz, mul_zero]

theorem negative_endpoint_nondiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hneg : (Bapat.endpointDerivative A).re < 0) :
    ∃ i j, i ≠ j ∧ A i j ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz := diagonal_endpointDerivative_zero A hn
  simp [hz] at hneg

end BapatBounds

-- Source: PositiveDefiniteViolation.lean

open scoped BigOperators ComplexOrder
open Set

namespace BapatBounds

theorem negative_endpoint_survives_diagonalPerturbation {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative A).re ≤ -(1 / 2 : ℝ))
    (hΓ : 1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
      (R + 1) ^ (n - 1)) :
    let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
    let ε := 1 / (4 * Γ)
    0 < ε ∧ ε ≤ 1 ∧
      (Bapat.endpointDerivative (diagonalPerturbation A ε)).re ≤ -(1 / 4 : ℝ) := by
  dsimp
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  have hΓp : 0 < Γ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΓ
  have hεp : 0 < 1 / (4 * Γ) := by positivity
  have hε1 : 1 / (4 * Γ) ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ 4 * Γ by linarith)
    simpa using hh
  have heq : Γ * (1 / (4 * Γ)) = (1 / 4 : ℝ) := by field_simp
  have hb := endpointDerivative_perturbation_bound A R (1 / (4 * Γ)) hR hA hεp.le hε1
  have hb' : ‖Bapat.endpointDerivative (diagonalPerturbation A (1 / (4 * Γ))) -
      Bapat.endpointDerivative A‖ ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
          (1 / (4 * Γ)) * (R + 1) ^ (n - 1) := hb
      _ = Γ * (1 / (4 * Γ)) := by dsimp [Γ]; ring
      _ = _ := heq
  have hr := (Complex.re_le_norm
    (Bapat.endpointDerivative (diagonalPerturbation A (1 / (4 * Γ))) -
      Bapat.endpointDerivative A)).trans hb'
  simp only [Complex.sub_re] at hr
  exact ⟨hεp, hε1, by linarith⟩

/-- This closes the actual positive-definite perturbation and explicit-interval
chain. The negative endpoint hypothesis must separately come from the actual
Gram/Bargmann bridge and the integer certificate; this is not that certificate. -/
theorem gram_explicit_monotonicity_failure {n r : ℕ}
    (V : Matrix (Fin n) (Fin r) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ))
    (hΓ : 1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
      (R + 1) ^ (n - 1))
    (hK : 1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n) :
    let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
    let ε := 1 / (4 * Γ)
    let B := diagonalPerturbation (V * V.conjTranspose) ε
    let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    B.PosDef ∧ (∃ i j, i ≠ j ∧ B i j ≠ 0) ∧ 0 < q₀ ∧ q₀ < 1 ∧
      h / 8 ≤ (Bapat.qPermanent B (q₀ : ℂ)).re - (Bapat.qPermanent B 1).re ∧
      (Bapat.qPermanent B 1).re < (Bapat.qPermanent B (q₀ : ℂ)).re := by
  dsimp
  let A := V * V.conjTranspose
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  let ε := 1 / (4 * Γ)
  obtain ⟨hεp, hε1, hb1⟩ := negative_endpoint_survives_diagonalPerturbation A R hR hA h1 hΓ
  have hB := gram_diagonalPerturbation_posDef V ε hεp
  have hentries := diagonalPerturbation_entries A R ε hA hεp.le hε1
  exact ⟨hB, negative_endpoint_nondiagonal _ (by linarith [hb1]),
    qPermanent_explicit_reverse_interval (diagonalPerturbation A ε) (R + 1)
      (by linarith) hentries hb1 hK⟩

end BapatBounds

-- Source: DimensionBounds.lean

namespace BapatBounds

theorem dimension_at_least_three_bounds (n : ℕ) (hn : 3 ≤ n) (R : ℝ) (hR : 0 ≤ R) :
    1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1) ∧
    1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n := by
  have hN3 : 3 ≤ n.choose 2 := by
    calc
      3 = Nat.choose 3 2 := by decide
      _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn
  have hN : (1 : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast (by omega : 1 ≤ n.choose 2)
  have hNm : (1 : ℝ) ≤ ((n.choose 2 - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n.choose 2 - 1)
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hd : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hp : ∀ m : ℕ, (1 : ℝ) ≤ (R + 1) ^ m := fun _m => one_le_pow₀ (by linarith)
  have hm (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
    have hh := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ a)
    simpa using hh
  exact ⟨hm _ _ (hm _ _ (hm _ _ hN hf) hd) (hp _),
    hm _ _ (hm _ _ (hm _ _ hN hNm) hf) (hp _)⟩

end BapatBounds

-- Source: CounterexampleTransfer.lean

open scoped BigOperators ComplexOrder
open Set

namespace BapatBounds

/-- Every actual negative-endpoint Gram matrix satisfying the quantified
entry bound gives a positive-definite, non-diagonal violation on [-1,1].
This is a transfer theorem, not an existence assertion for its input. -/
theorem negative_gram_counterexample_transfer {n r : ℕ} (hn : 3 ≤ n)
    (V : Matrix (Fin n) (Fin r) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ)) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, B.PosDef ∧
      (∃ i j, i ≠ j ∧ B i j ≠ 0) ∧
      ∃ q₀ : ℝ, 0 < q₀ ∧ q₀ < 1 ∧
        (Bapat.qPermanent B 1).re < (Bapat.qPermanent B (q₀ : ℂ)).re ∧
        ¬MonotoneOn (fun q : ℝ => (Bapat.qPermanent B (q : ℂ)).re) (Icc (-1) 1) := by
  let A := V * V.conjTranspose
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  let ε := 1 / (4 * Γ)
  let B := diagonalPerturbation A ε
  let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
    (n.factorial : ℝ) * (R + 1) ^ n
  let q₀ := 1 - 1 / (8 * K)
  have hd := dimension_at_least_three_bounds n hn R hR
  obtain ⟨hB, hnon, hq0, hq1, _, hreverse⟩ :=
    gram_explicit_monotonicity_failure V R hR hA h1 hd.1 hd.2
  refine ⟨B, hB, hnon, q₀, hq0, hq1, hreverse, ?_⟩
  intro hmono
  have hm := hmono (show q₀ ∈ Icc (-1 : ℝ) 1 by
      constructor
      · linarith
      · exact hq1.le)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) hq1.le
  exact (not_le_of_gt hreverse) hm

end BapatBounds

-- Source: Controls.lean

namespace BapatBounds

theorem constant_polynomial_control (q : ℝ) :
    realPolynomial (fun _ : Unit => 0) (fun _ => 7) q = 7 ∧
      realDerivative (fun _ : Unit => 0) (fun _ => 7) q = 0 := by
  simp [realPolynomial, realDerivative]

theorem linear_reverse_control :
    realPolynomial (fun _ : Unit => 1) (fun _ => -1) (7 / 8 : ℝ) >
      realPolynomial (fun _ : Unit => 1) (fun _ => -1) 1 := by
  norm_num [realPolynomial]

theorem omitted_negative_endpoint_control :
    (∀ q : ℝ, HasDerivAt (fun x : ℝ => x) 1 q) ∧
    (∀ q : ℝ, |(1 : ℝ) - 1| ≤ 1 * (1 - q) ↔ q ≤ 1) ∧
    ¬((1 : ℝ) < 1 - 1 / (8 * 1)) := by
  refine ⟨fun q => hasDerivAt_id q, ?_, ?_⟩
  · intro q
    simp
  · norm_num

end BapatBounds
