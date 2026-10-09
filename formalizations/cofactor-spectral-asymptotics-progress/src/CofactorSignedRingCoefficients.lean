import CofactorRingPolynomial
import CofactorGroupedSignAverage
import CofactorCoefficientRatio

/-! Signed ring coefficients as actual grouped finite sign sums, including all degree collisions. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

def ringAmplitude (d : K → ℕ) (R : K → ℝ) (s : Finset K) : ℝ := ∏ k ∈ s, (R k)^(d k)

theorem signCharacter_eq_subset_product (ε : K → Bool) (s : Finset K) :
    signCharacter ε s = ∏ i ∈ s, (if ε i then (-1 : ℝ) else 1) := by
  calc
    _ = ∏ i ∈ s, signFactor s i (ε i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ s)
      intro i _ hi
      simp [signFactor,hi]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [signFactor,if_pos hi]

theorem signedRingCoefficient_subset_product (d : K → ℕ) (R : K → ℝ)
    (ε : K → Bool) (s : Finset K) :
    (∏ k ∈ s, signedRingCoefficient (ε k) (R k) (d k)) =
      ringAmplitude d R s*signCharacter ε s := by
  unfold signedRingCoefficient ringAmplitude
  rw [Finset.prod_mul_distrib,signCharacter_eq_subset_product]
  ring

def ringDegree (n : ℕ) (d : K → ℕ) (hd : 2*∑ k, d k ≤ n) (s : Finset K) : Fin (n+1) :=
  ⟨2*∑ k ∈ s, d k, by
    have hs : (∑ k ∈ s, d k) ≤ ∑ k, d k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    omega⟩

theorem signedRingPolynomial_coeff (n : ℕ) (d : K → ℕ) (hd : 2*∑ k, d k ≤ n)
    (R : K → ℝ) (ε : K → Bool) (j : Fin (n+1)) :
    (ringPolynomial d (fun k => (signedRingCoefficient (ε k) (R k) (d k) : ℂ))).coeff j.val =
      (groupedSignCombination (ringAmplitude d R) (ringDegree n d hd) j ε : ℂ) := by
  rw [ringPolynomial_coeff]
  simp only [groupedSignCombination,signCombination,Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro s _
  have he : ringDegree n d hd s = j ↔ 2*∑ k ∈ s, d k = j.val := Fin.ext_iff
  by_cases h : 2*∑ k ∈ s, d k = j.val
  · rw [if_pos h,if_pos (he.mpr h)]
    rw [← Complex.ofReal_prod,signedRingCoefficient_subset_product,Complex.ofReal_mul]
  · rw [if_neg h,if_neg (not_congr he |>.mpr h)]
    simp only [Complex.ofReal_zero,zero_mul]

end
end CofactorSpectral
