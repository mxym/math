import CofactorRingSignChoice

/-! Actual normalized rank-two correlation Gram matrices with an explicit finite subset bound. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem exists_normalized_ring_family_small_permanent
    (r : ℕ) (hr : 0 < r) (d : K → ℕ) (hd : ∀ k, 2 ≤ d k)
    (R : K → ℝ) (hR : ∀ k, 0 < R k) (k0 : K) :
    ∃ z : RingFamilyIndex r d → ℂ,
      (normalizedBinaryGram z).PosSemidef ∧
      0 < (normalizedBinaryGram z).permanent.re ∧
      (∀ i, normalizedBinaryGram z i i = 1) ∧
      (normalizedBinaryGram z).rank = 2 ∧
      (∃ i0 i1, z i0 = 0 ∧ z i1 ≠ 0) ∧
      (∑ i, z i) = 0 ∧ (∑ i, z i^2) = 0 ∧
      (∑ i, Complex.normSq (z i)) = ∑ k, (2*d k : ℕ)*R k ∧
      (∑ i, (z i).im^2) = ∑ k, (d k : ℝ)*R k ∧
      (normalizedBinaryGram z).permanent.re ≤
        ((Fintype.card (RingFamilyIndex r d)).factorial : ℝ)*(binaryGamma z)^2*
          ∑ s : Finset K, (ringAmplitude d R s)^2 /
            ((Fintype.card (RingFamilyIndex r d)).choose (2*∑ k ∈ s, d k) : ℝ) := by
  classical
  let n := Fintype.card (RingFamilyIndex r d)
  have hdeg : 2*∑ k, d k ≤ n := by
    dsimp [n]
    rw [ringFamily_card]
    omega
  obtain ⟨ε,hε⟩ := signedRingPolynomial_has_small_choice n d hdeg R
  obtain ⟨z,hnorm,hsum,hsquare,hnormsum,him,hprod⟩ :=
    exists_signed_ring_family r d hd R hR ε
  let w := ringFamilySlopes r d z
  obtain ⟨i0,i1,h0,h1⟩ := ringFamily_zero_nonzero_witness r hr d z k0
    (by have h := hd k0; omega) (R k0) (hR k0) (hnorm k0)
  refine ⟨w,normalizedBinaryGram_psd w,normalizedBinaryGram_permanent_pos w,
    normalizedBinaryGram_diagonal w,normalizedBinaryGram_rank_two w i0 i1 h0 h1,
    ⟨i0,i1,h0,h1⟩,
    hsum,hsquare,hnormsum,him,?_⟩
  let f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![1,Polynomial.X]
  have he : slopePolynomial w =
      ringPolynomial d (fun k => (signedRingCoefficient (ε k) (R k) (d k) : ℂ)) := by
    have h := congrArg f hprod
    simpa only [f,map_prod,map_mul,map_add,map_pow,MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,one_pow,one_mul,slopePolynomial,ringPolynomial,w] using h
  rw [normalizedBinaryGram_permanent_ratio,he]
  exact mul_le_mul_of_nonneg_left hε (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end
end CofactorSpectral
