import CofactorNormalizedRows

/-! Exact rank two of the normalized actual Gram matrix from a zero and nonzero slope. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem normalizedBinaryRows_rank_two (z : V → ℂ) (i0 i1 : V)
    (h0 : z i0 = 0) (h1 : z i1 ≠ 0) :
    Matrix.rank (normalizedBinaryRows z) = 2 := by
  classical
  let B : Matrix V (Fin 2) ℂ := normalizedBinaryRows z
  let r : Fin 2 → V := ![i0,i1]
  let D : Matrix (Fin 2) (Fin 2) ℂ := B.submatrix r id
  have ha0 : (binaryScale z i0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (binaryScale_pos z i0)
  have ha1 : (binaryScale z i1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (binaryScale_pos z i1)
  have hD : D.det ≠ 0 := by
    have he : D.det = (binaryScale z i0 : ℂ)*((binaryScale z i1 : ℂ)*z i1) := by
      rw [Matrix.det_fin_two]
      change (binaryScale z i0 : ℂ)*((binaryScale z i1 : ℂ)*z i1) -
        ((binaryScale z i0 : ℂ)*z i0)*(binaryScale z i1 : ℂ) = _
      rw [h0]
      ring
    rw [he]
    exact mul_ne_zero ha0 (mul_ne_zero ha1 h1)
  have hDr : D.rank = 2 := by simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hD
  have hlo : 2 ≤ B.rank := by
    exact hDr.ge.trans (B.rank_submatrix_le r id)
  have hhi : B.rank ≤ 2 := by simpa only [Fintype.card_fin] using B.rank_le_card_width
  exact le_antisymm hhi hlo

theorem normalizedBinaryGram_rank_two (z : V → ℂ) (i0 i1 : V)
    (h0 : z i0 = 0) (h1 : z i1 ≠ 0) : (normalizedBinaryGram z).rank = 2 := by
  unfold normalizedBinaryGram
  rw [complexGram_eq_self_mul_conjTranspose,Matrix.rank_self_mul_conjTranspose]
  exact normalizedBinaryRows_rank_two z i0 i1 h0 h1

theorem normalizedBinaryGram_rankTwoCorrelationAdmissible {n : ℕ} (z : Fin n → ℂ)
    (i0 i1 : Fin n) (h0 : z i0 = 0) (h1 : z i1 ≠ 0) :
    rankTwoCorrelationAdmissible (normalizedBinaryGram z) :=
  ⟨⟨normalizedBinaryGram_psd z,normalizedBinaryGram_permanent_pos z⟩,
    normalizedBinaryGram_diagonal z,normalizedBinaryGram_rank_two z i0 i1 h0 h1⟩

theorem normalizedBinaryGram_marked_lower (z w : V → ℂ) :
    ((Fintype.card V-1).factorial : ℝ) * (binaryGamma z)^2 *
      Complex.normSq (∑ i, star (w i)*z i) ≤
        (∑ i,∑ j,star (w i)*compound (normalizedBinaryGram z) i j*w j).re := by
  have h := binaryRows_marked_quadratic_lower (fun i => (binaryScale z i : ℂ)) z w
  have he : (∏ i, (binaryScale z i : ℂ)) = (binaryGamma z : ℂ) := by
    simp [binaryGamma]
  rw [he,Complex.normSq_ofReal,← pow_two] at h
  exact h

end
end CofactorSpectral
