import BapatRankFourSphereEndpoint

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped Topology
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section

/-- A fixed base configuration with the required strict peak gap yields a finite
contiguous repetition with negative endpoint derivative. This reduction does not
assert existence of the base configuration. -/
theorem exists_contiguous_negative_endpoint {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    (hn : 2 ≤ n) (z₀ : ComplexUnitSphere4) (hpos : 0 < rowProductModulus v z₀)
    (hmax : ∀ z, rowProductModulus v z ≤ rowProductModulus v z₀)
    (hcommon : ∀ z, rowProductModulus v z = rowProductModulus v z₀ →
      rowWedgeEnergy v z = rowWedgeEnergy v z₀)
    (hgap : (n : ℝ)^4 * (rowProductModulus v z₀)^2 < 2 * rowWedgeEnergy v z₀) :
    ∃ L : ℕ, 0 < L ∧ 4 < n*L ∧
      (qPolynomial (gram (contiguousRows v L))).derivative.eval 1 < 0 := by
  let μ := normalizedSphere (complexProductHaar (Fin 4))
  let I₀ : ℕ → ℝ := fun L => ∫ z : ComplexUnitSphere4, (rowProductModulus v z)^(2*L) ∂μ
  let I₁ : ℕ → ℝ := fun L => ∫ z : ComplexUnitSphere4,
    (rowProductModulus v z)^(2*L-2) * rowWedgeEnergy v z ∂μ
  have hf : Continuous (rowProductModulus v) := rowProductModulus_continuous v
  have hg : Continuous (rowWedgeEnergy v) := rowWedgeEnergy_continuous v
  have hnf : ∀ z, 0 ≤ rowProductModulus v z := fun _ => norm_nonneg _
  have hratio := sphere_even_power_integral_ratio (complexProductHaar (Fin 4))
    (rowProductModulus v) (rowWedgeEnergy v) hf hg hnf z₀ hpos hmax hcommon
  have hnpos : 0 < n := by omega
  have hlim := (rank_four_prefactor_limit hnpos).mul hratio
  have hn4 : 0 < (n : ℝ)^4 := pow_pos (Nat.cast_pos.mpr hnpos) _
  have hf2 : 0 < (rowProductModulus v z₀)^2 := pow_pos hpos _
  have hgt : 1 < 2 / (n : ℝ)^4 *
      (rowWedgeEnergy v z₀ / (rowProductModulus v z₀)^2) := by
    rw [div_mul_div_comm]
    apply (lt_div_iff₀ (mul_pos hn4 hf2)).mpr
    simpa using hgap
  obtain ⟨L, hlarge, hr⟩ := ((eventually_ge_atTop 3).and
    ((tendsto_order.mp hlim).1 1 hgt)).exists
  have hL : 0 < L := by omega
  have hnL : 2 ≤ n*L := le_trans hn (Nat.le_mul_of_pos_right _ hL)
  have hI₀ : 0 < I₀ L := sphere_power_integral_pos (complexProductHaar (Fin 4))
    (rowProductModulus v) hf hnf z₀ hpos (2*L)
  let D : ℝ := ((n*L).choose 2 : ℝ) * ((n*L : ℕ)+3) * ((n*L : ℕ)+2)
  have hD : 0 < D := by
    apply mul_pos
    · exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hnL)) (by positivity)
    · positivity
  change 1 < (L : ℝ)^4 / D * (I₁ L / I₀ L) at hr
  rw [div_mul_div_comm] at hr
  have hcross : D * I₀ L < (L : ℝ)^4 * I₁ L := by
    simpa using (lt_div_iff₀ (mul_pos hD hI₀)).mp hr
  have hfac : ((n*L+3).factorial : ℝ) =
      ((n*L : ℕ)+3) * ((n*L : ℕ)+2) * ((n*L+1).factorial : ℝ) := by
    rw [show n*L+3 = (n*L+2)+1 by omega, Nat.factorial_succ,
      show n*L+2 = (n*L+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hfactor : 0 < ((n*L+1).factorial : ℝ) / 6 := by positivity
  have hnegative := mul_neg_of_pos_of_neg hfactor (sub_neg.mpr hcross)
  have he := real_contiguous_sphere_endpoint v hn hL
  rw [hfac] at he
  change 2 * (qPolynomial (gram (contiguousRows v L))).derivative.eval 1 =
    ((n*L).choose 2 : ℝ) *
      ((((n*L : ℕ)+3) * ((n*L : ℕ)+2) * ((n*L+1).factorial : ℝ)) / 6) * I₀ L -
    (L : ℝ)^4 * (((n*L+1).factorial : ℝ) / 6) * I₁ L at he
  have hd : 2 * (qPolynomial (gram (contiguousRows v L))).derivative.eval 1 < 0 := by
    rw [he]
    convert hnegative using 1 <;> dsimp [D] <;> ring
  refine ⟨L, hL, ?_, by linarith⟩
  have : 2*3 ≤ n*L := Nat.mul_le_mul hn hlarge
  omega

end
end BapatRealExistence
