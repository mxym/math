import BapatMvFischer
import BapatFiniteWedge
import BapatTwoRowCofactor
import BapatDefs

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

variable {ι C R : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype C] [LinearOrder C] [CommRing R]

noncomputable section

def gram (v : ι → C → R) : Matrix ι ι R := fun i j => ∑ c, v i c * v j c

def wedge (v : ι → C → R) (i j : ι) (a b : C) : R :=
  v i a * v j b - v i b * v j a

def remainingPolynomial (v : ι → C → R) (i j : ι) : MvPolynomial C R :=
  formsProduct (fun x : TwoPointComplement i j => v x.val)

def wedgePolynomial (v : ι → C → R) (a b : C) : MvPolynomial C R :=
  ∑ p ∈ originalPairs (ι := ι),
    MvPolynomial.C (wedge v p.1 p.2 a b) * remainingPolynomial v p.1 p.2

theorem gram_minor (v : ι → C → R) (i j k l : ι) :
    gram v i k * gram v j l - gram v i l * gram v j k =
      ∑ c ∈ originalPairs (ι := C), wedge v i j c.1 c.2 * wedge v k l c.1 c.2 := by
  exact dot_minor_eq_wedges (v i) (v j) (v k) (v l)

theorem gram_twoRowCofactor (v : ι → C → R) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) :
    twoRowCofactor (gram v) i j k l =
      fischerPair (remainingPolynomial v i j) (remainingPolynomial v k l) := by
  unfold gram
  rw [twoRowCofactor_eq_equiv_sum _ hij hkl]
  exact mixedPermanent_fischer (fun x : TwoPointComplement i j => v x.val)
    (fun y : TwoPointComplement k l => v y.val)

theorem wedgePolynomial_pair (v : ι → C → R) (a b : C) :
    fischerPair (wedgePolynomial v a b) (wedgePolynomial v a b) =
      ∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
        wedge v p.1 p.2 a b * wedge v q.1 q.2 a b *
          fischerPair (remainingPolynomial v p.1 p.2) (remainingPolynomial v q.1 q.2) := by
  unfold wedgePolynomial
  rw [fischerPair_sum_left]
  apply Finset.sum_congr rfl
  intro p hp
  rw [fischerPair_C_mul_left, fischerPair_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fischerPair_C_mul_right]
  ring

theorem permanentSum_eq_permanent (A : Matrix ι ι R) :
    permanentSum A = Matrix.permanent A := by
  rw [← Matrix.permanent_transpose A]
  unfold permanentSum permutationWeight Matrix.permanent
  apply Finset.sum_congr (by ext σ; simp)
  intro σ hσ
  rfl

/-- The full arbitrary finite rank endpoint identity, in any commutative ring.
Over the reals, self-pairings are exactly the squared Fischer norms. -/
theorem finiteRank_fischer_inversion_identity (v : ι → C → R) :
    2 * weightedInversionSum (gram v) =
      ((Fintype.card ι).choose 2 : R) * fischerPair (formsProduct v) (formsProduct v) -
        ∑ c ∈ originalPairs (ι := C),
          fischerPair (wedgePolynomial v c.1 c.2) (wedgePolynomial v c.1 c.2) := by
  have h := marked_inversion_cofactor_identity (gram v)
  have hp : permanentSum (gram v) = fischerPair (formsProduct v) (formsProduct v) := by
    rw [permanentSum_eq_permanent]
    exact permanent_gram_fischer v
  have hs :
      (∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
        (gram v p.1 q.1 * gram v p.2 q.2 - gram v p.1 q.2 * gram v p.2 q.1) *
          twoRowCofactor (gram v) p.1 p.2 q.1 q.2) =
        ∑ c ∈ originalPairs (ι := C),
          fischerPair (wedgePolynomial v c.1 c.2) (wedgePolynomial v c.1 c.2) := by
    calc
      _ = ∑ p ∈ originalPairs (ι := ι), ∑ q ∈ originalPairs (ι := ι),
          ∑ c ∈ originalPairs (ι := C),
            wedge v p.1 p.2 c.1 c.2 * wedge v q.1 q.2 c.1 c.2 *
              fischerPair (remainingPolynomial v p.1 p.2) (remainingPolynomial v q.1 q.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [gram_minor, gram_twoRowCofactor v
          (ne_of_lt (Finset.mem_filter.mp hp).2) (ne_of_lt (Finset.mem_filter.mp hq).2),
          Finset.sum_mul]
      _ = ∑ p ∈ originalPairs (ι := ι), ∑ c ∈ originalPairs (ι := C),
          ∑ q ∈ originalPairs (ι := ι),
            wedge v p.1 p.2 c.1 c.2 * wedge v q.1 q.2 c.1 c.2 *
              fischerPair (remainingPolynomial v p.1 p.2) (remainingPolynomial v q.1 q.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        exact (wedgePolynomial_pair v c.1 c.2).symm
  rw [hp, hs] at h
  linear_combination -h

def fischerNormSq (p : MvPolynomial C ℝ) : ℝ := fischerPair p p

theorem fischerNormSq_coefficients (p : MvPolynomial C ℝ) :
    fischerNormSq p = ∑ α ∈ p.support, (multiFactorial α : ℝ) * (p.coeff α)^2 := by
  simp only [fischerNormSq, fischerPair, MvPolynomial.sum_def]
  apply Finset.sum_congr rfl
  intro α hα
  ring

theorem fischerNormSq_nonneg (p : MvPolynomial C ℝ) : 0 ≤ fischerNormSq p := by
  rw [fischerNormSq_coefficients]
  exact Finset.sum_nonneg (fun α _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end
end BapatFiniteRank
