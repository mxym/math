import CofactorSignedRingCoefficients

/-! An actual small coefficient-ratio sign choice for the finite ring polynomial. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem signedRingPolynomial_ratio (n : ℕ) (d : K → ℕ) (hd : 2*∑ k, d k ≤ n)
    (R : K → ℝ) (ε : K → Bool) :
    binaryCoefficientRatio n
      (ringPolynomial d (fun k => (signedRingCoefficient (ε k) (R k) (d k) : ℂ))) =
      ∑ j : Fin (n+1), (1/(n.choose j.val : ℝ))*
        groupedSignCombination (ringAmplitude d R) (ringDegree n d hd) j ε ^ 2 := by
  unfold binaryCoefficientRatio
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Complex.normSq ((ringPolynomial d
      (fun k => (signedRingCoefficient (ε k) (R k) (d k) : ℂ))).coeff j)/
        (n.choose j : ℝ)) (n+1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [signedRingPolynomial_coeff n d hd R ε j,Complex.normSq_ofReal]
  ring

theorem signedRingPolynomial_has_small_choice (n : ℕ) (d : K → ℕ)
    (hd : 2*∑ k, d k ≤ n) (R : K → ℝ) :
    ∃ ε : K → Bool,
      binaryCoefficientRatio n
        (ringPolynomial d (fun k => (signedRingCoefficient (ε k) (R k) (d k) : ℂ))) ≤
        ∑ s : Finset K, (ringAmplitude d R s)^2/(n.choose (2*∑ k ∈ s, d k) : ℝ) := by
  obtain ⟨ε,hε⟩ := groupedSignCombination_has_small_choice (ringAmplitude d R)
    (ringDegree n d hd) (fun j => 1/(n.choose j.val : ℝ))
  refine ⟨ε,?_⟩
  rw [signedRingPolynomial_ratio n d hd]
  have he : (∑ s : Finset K, (1/(n.choose (ringDegree n d hd s).val : ℝ))*
      ringAmplitude d R s^2) =
      ∑ s : Finset K, (ringAmplitude d R s)^2/(n.choose (2*∑ k ∈ s, d k) : ℝ) := by
    apply Finset.sum_congr rfl
    intro s _
    change (1/(n.choose (2*∑ k ∈ s, d k) : ℝ))*ringAmplitude d R s^2 = _
    ring
  exact hε.trans_eq he

end
end CofactorSpectral
