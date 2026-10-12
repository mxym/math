import CofactorFiniteRingConstruction

/-! The finite root-ring construction on the actual standard matrix index Fin N. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem exists_rankTwoCorrelation_ring_bound
    (N r : ℕ) (hr : 0 < r) (d : K → ℕ) (hd : ∀ k, 2 ≤ d k)
    (hN : r+2*∑ k, d k = N) (R : K → ℝ) (hR : ∀ k, 0 < R k) (k0 : K) :
    ∃ z : Fin N → ℂ,
      rankTwoCorrelationAdmissible (normalizedBinaryGram z) ∧
      (∑ i, z i) = 0 ∧ (∑ i, z i^2) = 0 ∧
      vectorNormSq z = ∑ k, (2*d k : ℕ)*R k ∧
      vectorNormSq (fun i => ((z i).im : ℂ)) = ∑ k, (d k : ℝ)*R k ∧
      (normalizedBinaryGram z).permanent.re ≤
        (N.factorial : ℝ)*(binaryGamma z)^2*
          ∑ s : Finset K, (ringAmplitude d R s)^2 /
            (N.choose (2*∑ k ∈ s, d k) : ℝ) := by
  classical
  obtain ⟨z,hpsd,hpos,hdiag,hrank,⟨i0,i1,h0,h1⟩,hsum,hsquare,hnorm,him,hper⟩ :=
    exists_normalized_ring_family_small_permanent r hr d hd R hR k0
  have hc : Fintype.card (RingFamilyIndex r d) = N := (ringFamily_card r d).trans hN
  let e : RingFamilyIndex r d ≃ Fin N := Fintype.equivFinOfCardEq hc
  let w : Fin N → ℂ := fun i => z (e.symm i)
  have hw0 : w (e i0) = 0 := by simpa only [w,Equiv.symm_apply_apply] using h0
  have hw1 : w (e i1) ≠ 0 := by simpa only [w,Equiv.symm_apply_apply] using h1
  have hG : binaryGamma w = binaryGamma z := by
    unfold binaryGamma
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hP : slopePolynomial w = slopePolynomial z := by
    unfold slopePolynomial
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hperEq : (normalizedBinaryGram w).permanent.re =
      (normalizedBinaryGram z).permanent.re := by
    rw [normalizedBinaryGram_permanent_ratio,normalizedBinaryGram_permanent_ratio,
      Fintype.card_fin,hc,hG,hP]
  refine ⟨w,normalizedBinaryGram_rankTwoCorrelationAdmissible w (e i0) (e i1) hw0 hw1,
    ?_,?_,?_,?_,?_⟩
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans hsum
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans hsquare
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans hnorm
  · have he : vectorNormSq (fun i => ((w i).im : ℂ)) = ∑ i, (z i).im^2 := by
      simp only [vectorNormSq,Complex.normSq_ofReal,← pow_two]
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    exact he.trans him
  · rw [hperEq,hG]
    simpa only [hc] using hper

end
end CofactorSpectral
