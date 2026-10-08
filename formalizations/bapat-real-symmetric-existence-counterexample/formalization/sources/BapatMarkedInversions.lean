import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit false

/-!
The ordered-pair part of the Bapat rank-two identity.

No simultaneous reindexing invariance is used: `i < j` and `σ j < σ i`
always refer to the original order. The sole reindexing is the explicit
involution `σ ↦ σ ∘ swap i j` on the sum over all permutations.
-/

open scoped BigOperators

namespace BapatRankTwo.MarkedInversions

section FiniteProducts

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def permutationWeight (A : ι → ι → R) (σ : Equiv.Perm ι) : R :=
  ∏ k, A k (σ k)

def remainingWeight (A : ι → ι → R) (i j : ι) (σ : Equiv.Perm ι) : R :=
  ∏ k ∈ (Finset.univ.erase i).erase j, A k (σ k)

def swapRowsPerm (i j : ι) (σ : Equiv.Perm ι) : Equiv.Perm ι :=
  (Equiv.swap i j).trans σ

@[simp] theorem swapRowsPerm_apply (i j : ι) (σ : Equiv.Perm ι) (k : ι) :
    swapRowsPerm i j σ k = σ (Equiv.swap i j k) := rfl

@[simp] theorem swapRowsPerm_twice (i j : ι) (σ : Equiv.Perm ι) :
    swapRowsPerm i j (swapRowsPerm i j σ) = σ := by
  ext k
  simp

def swapRowsEquiv (i j : ι) : Equiv.Perm ι ≃ Equiv.Perm ι where
  toFun := swapRowsPerm i j
  invFun := swapRowsPerm i j
  left_inv := swapRowsPerm_twice i j
  right_inv := swapRowsPerm_twice i j

theorem permutationWeight_split (A : ι → ι → R) (σ : Equiv.Perm ι)
    {i j : ι} (hij : i ≠ j) :
    permutationWeight A σ = A i (σ i) * A j (σ j) * remainingWeight A i j σ := by
  unfold permutationWeight remainingWeight
  rw [← Finset.mul_prod_erase Finset.univ (fun k => A k (σ k)) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => A k (σ k))
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  ring

@[simp] theorem remainingWeight_swapRowsPerm (A : ι → ι → R) (i j : ι)
    (σ : Equiv.Perm ι) :
    remainingWeight A i j (swapRowsPerm i j σ) = remainingWeight A i j σ := by
  unfold remainingWeight
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem permutationWeight_sub_swapRowsPerm (A : ι → ι → R)
    (σ : Equiv.Perm ι) {i j : ι} (hij : i ≠ j) :
    permutationWeight A σ - permutationWeight A (swapRowsPerm i j σ) =
      (A i (σ i) * A j (σ j) - A i (σ j) * A j (σ i)) *
        remainingWeight A i j σ := by
  rw [permutationWeight_split A σ hij,
    permutationWeight_split A (swapRowsPerm i j σ) hij]
  simp only [swapRowsPerm_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    remainingWeight_swapRowsPerm]
  ring

end FiniteProducts

section OrderedSums

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

local instance : Fintype (Equiv.Perm ι) := fintypePerm

/-- The all-permutation sum, before any rank-two specialization. -/
def permanentSum (A : ι → ι → R) : R := ∑ σ : Equiv.Perm ι, permutationWeight A σ

/-- The contribution of one marked original-order inversion pair. -/
def inversionPairSum (A : ι → ι → R) (i j : ι) : R :=
  ∑ σ : Equiv.Perm ι, if σ j < σ i then permutationWeight A σ else 0

/-- Swapping the two rows converts descending images to ascending images. -/
theorem inversionPairSum_eq_swap (A : ι → ι → R) (i j : ι) :
    inversionPairSum A i j =
      ∑ σ : Equiv.Perm ι,
        if σ i < σ j then permutationWeight A (swapRowsPerm i j σ) else 0 := by
  unfold inversionPairSum
  have h := (swapRowsEquiv i j).sum_comp
    (fun σ : Equiv.Perm ι => if σ j < σ i then permutationWeight A σ else 0)
  simpa only [swapRowsEquiv, Equiv.coe_fn_mk, swapRowsPerm_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right] using h.symm

theorem permanentSum_split_images (A : ι → ι → R) {i j : ι} (hij : i ≠ j) :
    permanentSum A =
      (∑ σ : Equiv.Perm ι, if σ i < σ j then permutationWeight A σ else 0) +
        inversionPairSum A i j := by
  unfold permanentSum inversionPairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hs : σ i ≠ σ j := fun he => hij (σ.injective he)
  rcases lt_or_gt_of_ne hs with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h]

/-- The generic two-row determinant identity. This is the marked-inversion
step, and is valid for every matrix over a commutative ring. -/
theorem permanentSum_sub_two_inversionPairSum (A : ι → ι → R)
    {i j : ι} (hij : i ≠ j) :
    permanentSum A - 2 * inversionPairSum A i j =
      ∑ σ : Equiv.Perm ι, if σ i < σ j then
        (A i (σ i) * A j (σ j) - A i (σ j) * A j (σ i)) *
          remainingWeight A i j σ else 0 := by
  rw [permanentSum_split_images A hij]
  calc
    _ = (∑ σ : Equiv.Perm ι, if σ i < σ j then permutationWeight A σ else 0) -
        inversionPairSum A i j := by ring
    _ = (∑ σ : Equiv.Perm ι, if σ i < σ j then permutationWeight A σ else 0) -
        ∑ σ : Equiv.Perm ι,
          if σ i < σ j then permutationWeight A (swapRowsPerm i j σ) else 0 := by
      rw [inversionPairSum_eq_swap]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs with h
      · exact permutationWeight_sub_swapRowsPerm A σ hij
      · simp

/-- Every pair retains the original linear order on the index type. -/
def originalPairs : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 < p.2)

/-- The actual inversion number; this is a cardinality, not a free weight. -/
def originalInversions (σ : Equiv.Perm ι) : ℕ :=
  (Finset.univ.filter fun p : ι × ι => p.1 < p.2 ∧ σ p.2 < σ p.1).card

theorem originalPairs_card : (originalPairs (ι := ι)).card = (Fintype.card ι).choose 2 := by
  simpa [originalPairs] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset ι)))

theorem originalInversions_cast (σ : Equiv.Perm ι) :
    (originalInversions σ : R) =
      ∑ p ∈ originalPairs (ι := ι), if σ p.2 < σ p.1 then (1 : R) else 0 := by
  unfold originalInversions originalPairs
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 < p.2 <;> by_cases hσ : σ p.2 < σ p.1 <;> simp [hp, hσ]

/-- The derivative-at-one finite sum, before making an analytic claim. -/
def weightedInversionSum (A : ι → ι → R) : R :=
  ∑ σ : Equiv.Perm ι, (originalInversions σ : R) * permutationWeight A σ

theorem weightedInversionSum_eq_sum_pairs (A : ι → ι → R) :
    weightedInversionSum A =
      ∑ p ∈ originalPairs (ι := ι), inversionPairSum A p.1 p.2 := by
  unfold weightedInversionSum
  simp_rw [originalInversions_cast, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  unfold inversionPairSum
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ p.2 < σ p.1 <;> simp [hσ]

/-- All marked inversions expressed using genuine two-by-two determinants.
The only missing bridge to Fischer norms is the remaining mixed permanent. -/
theorem marked_inversion_determinant_identity (A : ι → ι → R) :
    ((Fintype.card ι).choose 2 : R) * permanentSum A -
        2 * weightedInversionSum A =
      ∑ p ∈ originalPairs (ι := ι), ∑ σ : Equiv.Perm ι,
        if σ p.1 < σ p.2 then
          (A p.1 (σ p.1) * A p.2 (σ p.2) -
            A p.1 (σ p.2) * A p.2 (σ p.1)) *
            remainingWeight A p.1 p.2 σ else 0 := by
  have hc : (∑ _p ∈ originalPairs (ι := ι), permanentSum A) =
      ((originalPairs (ι := ι)).card : R) * permanentSum A := by
    simp [nsmul_eq_mul]
  rw [weightedInversionSum_eq_sum_pairs, ← originalPairs_card, ← hc]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact permanentSum_sub_two_inversionPairSum A
    (ne_of_lt (Finset.mem_filter.mp hp).2)

/-- A genuine two-row/two-column permanent cofactor, presented as a fiber
of the full permutation set. No division or artificial multiplicity occurs. -/
def twoRowCofactor (A : ι → ι → R) (i j k l : ι) : R :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)).filter
      (fun σ => σ i = k ∧ σ j = l), remainingWeight A i j σ

/-- Group the ascending-image permutations by their exact two column images. -/
theorem ascending_images_eq_cofactor_sum (A D : ι → ι → R) (i j : ι) :
    (∑ σ : Equiv.Perm ι, if σ i < σ j then
      D (σ i) (σ j) * remainingWeight A i j σ else 0) =
    ∑ p ∈ originalPairs (ι := ι), D p.1 p.2 * twoRowCofactor A i j p.1 p.2 := by
  have hf := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Equiv.Perm ι)) (originalPairs (ι := ι))
    (fun σ : Equiv.Perm ι => (σ i, σ j))
    (fun σ : Equiv.Perm ι => D (σ i) (σ j) * remainingWeight A i j σ)
  have hleft :
      (∑ p ∈ originalPairs (ι := ι),
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)).filter
          (fun σ => (σ i, σ j) = p),
          D (σ i) (σ j) * remainingWeight A i j σ) =
      ∑ p ∈ originalPairs (ι := ι), D p.1 p.2 * twoRowCofactor A i j p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    rcases p with ⟨k, l⟩
    unfold twoRowCofactor
    rw [Finset.mul_sum]
    simp only [Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨hi, hj⟩ := (Finset.mem_filter.mp hσ).2
    rw [hi, hj]
  rw [hleft] at hf
  simpa only [originalPairs, Finset.sum_filter, Finset.mem_filter,
    Finset.mem_univ, true_and] using hf.symm

/-- The fully grouped, ordered two-row permanent expansion. -/
theorem marked_inversion_cofactor_identity (A : ι → ι → R) :
    ((Fintype.card ι).choose 2 : R) * permanentSum A -
        2 * weightedInversionSum A =
      ∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
        (A p.1 q.1 * A p.2 q.2 - A p.1 q.2 * A p.2 q.1) *
          twoRowCofactor A p.1 p.2 q.1 q.2 := by
  rw [marked_inversion_determinant_identity]
  apply Finset.sum_congr rfl
  intro p _
  exact ascending_images_eq_cofactor_sum A
    (fun k l => A p.1 k * A p.2 l - A p.1 l * A p.2 k) p.1 p.2

end OrderedSums

end BapatRankTwo.MarkedInversions
