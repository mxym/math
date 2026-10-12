import BapatFiniteBase

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions

namespace BapatRealExistence
noncomputable section

/-- An actual finite real rank-four Gram witness with negative endpoint derivative.
The cloud, canonical maxima, selector, row order and repetition are all existentially
constructed here; no analytic existence or gap hypothesis remains. -/
theorem exists_real_gram_negative_endpoint :
    ∃ (N : ℕ) (v : Fin N → Fin 4 → ℝ), 4<N ∧
      (qPolynomial (gram v)).derivative.eval 1 < 0 := by
  obtain ⟨m,v,t,hm,ht,ht',hp,hmax,hscore⟩ := exists_canonical_cloud_score_gap
  let a := appendSelectorRows v (selectorParameter t)
  let b := sortRows a t
  let u := canonicalSphere4 t (show 0≤t by linarith) (show t≤1 by linarith)
  obtain ⟨hap,ham,hao⟩ := appendSelectorRows_peak v ht ht' hp hmax
  have he (z : ComplexUnitSphere4) : rowProductModulus b z = rowProductModulus a z := by
    unfold rowProductModulus b
    rw [sortRows_product]
  have hbp : 0<rowProductModulus b u := by rw [he]; exact hap
  have hbm : ∀ z, rowProductModulus b z ≤ rowProductModulus b u := by
    intro z; rw [he,he]; exact ham z
  have hbc : ∀ z, rowProductModulus b z = rowProductModulus b u → rowWedgeEnergy b z=rowWedgeEnergy b u := by
    intro z hz
    rw [he,he] at hz
    exact rowWedgeEnergy_eq_on_conjugate_orbits b u z (hao z hz)
  have hbound := sortRows_wedge_energy_bound a (show 0≤t by linarith) (show t≤1 by linarith)
    (norm_ne_zero_iff.mp (ne_of_gt hap))
  have hgap : ((m+4:ℕ):ℝ)^4*(rowProductModulus b u)^2 < 2*rowWedgeEnergy b u := by
    have hh := mul_lt_mul_of_pos_right hscore (sq_pos_of_pos hbp)
    change (rowProductModulus b u)^2*(realPairScore (rowRatios a t))^2≤rowWedgeEnergy b u at hbound
    change ((m+4:ℕ):ℝ)^4*(rowProductModulus b u)^2 <
      (2*(realPairScore (rowRatios a t))^2)*(rowProductModulus b u)^2 at hh
    nlinarith
  obtain ⟨L,hL,hN,hneg⟩ := exists_contiguous_negative_endpoint b (by omega) u hbp hbm hbc hgap
  exact ⟨(m+4)*L,contiguousRows b L,hN,hneg⟩

end
end BapatRealExistence
