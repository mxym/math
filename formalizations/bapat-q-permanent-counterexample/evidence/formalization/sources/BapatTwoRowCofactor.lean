import BapatMarkedInversions

set_option autoImplicit false

open scoped BigOperators

namespace BapatRankTwo.MarkedInversions

section Equivalences

variable {ι : Type*} [DecidableEq ι]

/-- The untouched rows or columns, with their original labels. -/
abbrev TwoPointComplement (i j : ι) := {x : ι // x ≠ i ∧ x ≠ j}

/-- Extend a bijection of the remaining indices by the specified two images. -/
def extendTwoPoint {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (e : TwoPointComplement i j ≃ TwoPointComplement k l) : Equiv.Perm ι where
  toFun x := if hi : x = i then k else if hj : x = j then l else
    (e ⟨x, hi, hj⟩).val
  invFun y := if hk : y = k then i else if hl : y = l then j else
    (e.symm ⟨y, hk, hl⟩).val
  left_inv x := by
    by_cases hi : x = i
    · subst x
      simp
    by_cases hj : x = j
    · subst x
      simp [hij.symm, hkl.symm]
    have hk := (e ⟨x, hi, hj⟩).property.1
    have hl := (e ⟨x, hi, hj⟩).property.2
    simp only [dif_neg hi, dif_neg hj, dif_neg hk, dif_neg hl]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hi, hj⟩)
  right_inv y := by
    by_cases hk : y = k
    · subst y
      simp
    by_cases hl : y = l
    · subst y
      simp [hkl.symm, hij.symm]
    have hi := (e.symm ⟨y, hk, hl⟩).property.1
    have hj := (e.symm ⟨y, hk, hl⟩).property.2
    simp only [dif_neg hk, dif_neg hl, dif_neg hi, dif_neg hj]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hk, hl⟩)

@[simp] theorem extendTwoPoint_first {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (e : TwoPointComplement i j ≃ TwoPointComplement k l) :
    extendTwoPoint hij hkl e i = k := by
  simp [extendTwoPoint]

@[simp] theorem extendTwoPoint_second {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (e : TwoPointComplement i j ≃ TwoPointComplement k l) :
    extendTwoPoint hij hkl e j = l := by
  simp [extendTwoPoint, hij.symm]

@[simp] theorem extendTwoPoint_complement {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (e : TwoPointComplement i j ≃ TwoPointComplement k l) (x : TwoPointComplement i j) :
    extendTwoPoint hij hkl e x.val = (e x).val := by
  simp [extendTwoPoint, x.property.1, x.property.2]

/-- Restrict a full permutation with fixed images to the untouched indices. -/
def restrictTwoPoint {i j k l : ι} (σ : Equiv.Perm ι)
    (hi : σ i = k) (hj : σ j = l) :
    TwoPointComplement i j ≃ TwoPointComplement k l where
  toFun x := ⟨σ x.val, by
    constructor
    · intro he
      exact x.property.1 (σ.injective (he.trans hi.symm))
    · intro he
      exact x.property.2 (σ.injective (he.trans hj.symm))⟩
  invFun y := ⟨σ.symm y.val, by
    constructor
    · intro he
      apply y.property.1
      calc
        y.val = σ (σ.symm y.val) := (σ.apply_symm_apply _).symm
        _ = σ i := congrArg σ he
        _ = k := hi
    · intro he
      apply y.property.2
      calc
        y.val = σ (σ.symm y.val) := (σ.apply_symm_apply _).symm
        _ = σ j := congrArg σ he
        _ = l := hj⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
  right_inv y := Subtype.ext (σ.apply_symm_apply y.val)

@[simp] theorem restrictTwoPoint_apply {i j k l : ι} (σ : Equiv.Perm ι)
    (hi : σ i = k) (hj : σ j = l) (x : TwoPointComplement i j) :
    (restrictTwoPoint σ hi hj x).val = σ x.val := rfl

/-- Each complementary bijection has exactly one extension. This is the
cofactor multiplicity-one fact, not a cardinality assumption. -/
def twoPointFiberEquiv {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    {σ : Equiv.Perm ι // σ i = k ∧ σ j = l} ≃
      (TwoPointComplement i j ≃ TwoPointComplement k l) where
  toFun σ := restrictTwoPoint σ.val σ.property.1 σ.property.2
  invFun e := ⟨extendTwoPoint hij hkl e, extendTwoPoint_first hij hkl e,
    extendTwoPoint_second hij hkl e⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    by_cases hi : x = i
    · subst x
      simpa using σ.property.1.symm
    by_cases hj : x = j
    · subst x
      simpa using σ.property.2.symm
    change extendTwoPoint hij hkl (restrictTwoPoint σ.val σ.property.1 σ.property.2) x =
      σ.val x
    simpa using extendTwoPoint_complement hij hkl
      (restrictTwoPoint σ.val σ.property.1 σ.property.2) ⟨x, hi, hj⟩
  right_inv e := by
    ext x
    exact extendTwoPoint_complement hij hkl e x

end Equivalences

section Cofactor

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

local instance : Fintype (Equiv.Perm ι) := fintypePerm

theorem twoPointComplement_card {i j : ι} (hij : i ≠ j) :
    Fintype.card (TwoPointComplement i j) = Fintype.card ι - 2 := by
  have hc : Fintype.card (TwoPointComplement i j) =
      ((Finset.univ.erase i).erase j).card :=
    Fintype.card_of_finset' (p := {x : ι | x ≠ i ∧ x ≠ j})
      ((Finset.univ.erase i).erase j) (by intro x; simp [and_comm])
  rw [hc]
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  omega

theorem remainingWeight_eq_complement_product (A : ι → ι → R)
    (i j : ι) (σ : Equiv.Perm ι) :
    remainingWeight A i j σ =
      ∏ x : TwoPointComplement i j, A x.val (σ x.val) := by
  unfold remainingWeight
  apply Finset.prod_subtype
  intro x
  simp [and_comm]

/-- The two-row cofactor is the mixed permanent on the actual complementary
row and column sets. Both label sets are retained. -/
theorem twoRowCofactor_eq_equiv_sum (A : ι → ι → R) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) :
    twoRowCofactor A i j k l =
      ∑ e : TwoPointComplement i j ≃ TwoPointComplement k l,
        ∏ x : TwoPointComplement i j, A x.val (e x).val := by
  unfold twoRowCofactor
  rw [Finset.sum_subtype (p := fun σ : Equiv.Perm ι => σ i = k ∧ σ j = l)
    _ (by intro σ; simp)]
  apply Fintype.sum_equiv (twoPointFiberEquiv hij hkl)
  intro σ
  rw [remainingWeight_eq_complement_product]
  rfl

end Cofactor

end BapatRankTwo.MarkedInversions
