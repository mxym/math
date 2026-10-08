import BapatDefs
import BapatTwoRowCofactor
import BapatMixedFischer

set_option autoImplicit false

open scoped BigOperators Nat
open Polynomial

namespace BapatRankTwo

open MarkedInversions BapatFischer

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The determinant of the two originally ordered rank-two vectors. -/
def wedge (a b : ι → ℂ) (i j : ι) : ℂ := a i * b j - b i * a j

/-- Dehomogenization of the genuine product after deleting exactly i and j.
Its homogeneous degree is card ι - 2 whenever i ≠ j. -/
def remainingPolynomial (a b : ι → ℂ) (i j : ι) : ℂ[X] :=
  twoColorProduct (fun x : TwoPointComplement i j => a x.val)
    (fun x : TwoPointComplement i j => b x.val)

theorem remainingPolynomial_eq_erased_product (a b : ι → ℂ) (i j : ι) :
    remainingPolynomial a b i j =
      ∏ k ∈ (Finset.univ.erase i).erase j, (C (a k) + C (b k) * X) := by
  unfold remainingPolynomial twoColorProduct
  symm
  apply Finset.prod_subtype
  intro k
  simp [and_comm]

/-- The originally ordered sum S of wedges times the remaining products. -/
def wedgePolynomial (a b : ι → ℂ) : ℂ[X] :=
  ∑ p ∈ originalPairs (ι := ι), C (wedge a b p.1 p.2) *
    remainingPolynomial a b p.1 p.2

theorem permanentSum_eq_permanent (A : Matrix ι ι ℂ) :
    permanentSum A = Matrix.permanent A := by
  rw [← Matrix.permanent_transpose A]
  unfold permanentSum permutationWeight Matrix.permanent
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rfl

/-- The cofactor is a mixed Fischer pairing on the two actual complements. -/
theorem gram_twoRowCofactor (a b : ι → ℂ) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) :
    twoRowCofactor (gram a b) i j k l =
      fischerPair (Fintype.card ι - 2)
        (remainingPolynomial a b i j) (remainingPolynomial a b k l) := by
  unfold gram
  rw [twoRowCofactor_eq_equiv_sum _ hij hkl]
  let e₀ : TwoPointComplement i j ≃ TwoPointComplement k l :=
    Fintype.equivOfCardEq ((twoPointComplement_card hij).trans
      (twoPointComplement_card hkl).symm)
  change mixedPermanent (fun x : TwoPointComplement i j =>
    fun y : TwoPointComplement k l =>
      a x.val * star (a y.val) + b x.val * star (b y.val)) = _
  rw [mixedPermanent_gram e₀, twoPointComplement_card hij]
  rfl

/-- Expand S's Fischer norm as its actual two-pair mixed sum. -/
theorem wedgePolynomial_pair (a b : ι → ℂ) :
    fischerPair (Fintype.card ι - 2) (wedgePolynomial a b) (wedgePolynomial a b) =
      ∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
        wedge a b p.1 p.2 * star (wedge a b q.1 q.2) *
          fischerPair (Fintype.card ι - 2)
            (remainingPolynomial a b p.1 p.2) (remainingPolynomial a b q.1 q.2) := by
  unfold wedgePolynomial
  rw [fischerPair_sum_left]
  apply Finset.sum_congr rfl
  intro p _
  rw [fischerPair_C_mul_left, fischerPair_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [fischerPair_C_mul_right]
  ring

/-- The full rank-two identity. The inversion-weighted term is the genuine
all-permutation derivative-at-one sum, not an assumed analytic input. -/
theorem rankTwo_fischer_inversion_identity (a b : ι → ℂ) :
    2 * weightedInversionSum (gram a b) =
      ((Fintype.card ι).choose 2 : ℂ) *
          (fischerNormSq (Fintype.card ι) (twoColorProduct a b) : ℂ) -
        (fischerNormSq (Fintype.card ι - 2) (wedgePolynomial a b) : ℂ) := by
  have h := marked_inversion_cofactor_identity (gram a b)
  have hsum :
      (∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
        (gram a b p.1 q.1 * gram a b p.2 q.2 -
          gram a b p.1 q.2 * gram a b p.2 q.1) *
          twoRowCofactor (gram a b) p.1 p.2 q.1 q.2) =
        (fischerNormSq (Fintype.card ι - 2) (wedgePolynomial a b) : ℂ) := by
    rw [← fischerPair_self, wedgePolynomial_pair]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [gram_minor, gram_twoRowCofactor a b
      (ne_of_lt (Finset.mem_filter.mp hp).2)
      (ne_of_lt (Finset.mem_filter.mp hq).2)]
    rfl
  have hp : permanentSum (gram a b) =
      (fischerNormSq (Fintype.card ι) (twoColorProduct a b) : ℂ) := by
    calc
      _ = Matrix.permanent (gram a b) := permanentSum_eq_permanent _
      _ = _ := permanent_rankTwo_gram a b
  rw [hsum, hp] at h
  linear_combination -h

/-- The real polynomial used in the original interval conjecture has exactly
the endpoint derivative supplied by the Fischer certificate. -/
theorem realQPolynomial_derivative_fischer {n : ℕ} (a b : Fin n → ℂ) :
    2 * (realQPolynomial (gram a b)).derivative.eval 1 =
      (n.choose 2 : ℝ) * fischerNormSq n (twoColorProduct a b) -
        fischerNormSq (n - 2) (wedgePolynomial a b) := by
  rw [realQPolynomial_derivative_one]
  simpa [Complex.mul_re] using
    congrArg Complex.re (rankTwo_fischer_inversion_identity a b)

end

end BapatRankTwo
