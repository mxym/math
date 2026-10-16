import SpectralProtocol.LinearPhysical

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι ο J : Type*} {κ : J → Type*}
  [Fintype ι] [Fintype ο] [Fintype J]
  [DecidableEq ι] [DecidableEq ο] [DecidableEq J]
  [∀ j,Fintype (κ j)] [∀ j,DecidableEq (κ j)]

theorem orthogonal_block_expansion (C : ∀ j,Matrix ι (κ j) ℂ)
    (X : Matrix ι ι ℂ) :
    (∑ j,C j*(C j)ᴴ)*X*(∑ j,C j*(C j)ᴴ)=
      ∑ j,∑ l,C j*((C j)ᴴ*X*C l)*(C l)ᴴ := by
  simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.mul_assoc]
  rw [Finset.sum_comm]

theorem channel_orthogonal_block_sum
    (F : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (C : ∀ j,Matrix ι (κ j) ℂ)
    (hoff : ∀ j l,j≠l → ∀ Y : Matrix (κ j) (κ l) ℂ,F (C j*Y*(C l)ᴴ)=0)
    (X : Matrix ι ι ℂ) :
    F ((∑ j,C j*(C j)ᴴ)*X*(∑ j,C j*(C j)ᴴ))=
      ∑ j,F (C j*((C j)ᴴ*X*C j)*(C j)ᴴ) := by
  classical
  rw [orthogonal_block_expansion]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_eq_single j
  · intro l hl hlj
    exact hoff j l (Ne.symm hlj) _
  · simp

/-- Positive discarded support and exact removal of off-diagonal source blocks
turn the actual block decoders into a weighted bound for the entire input. -/
theorem channel_weighted_block_lower
    (F : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hF : ∀ X : Matrix ι ι ℂ,X.PosSemidef → (F X).PosSemidef)
    (Q : Matrix ο ο ℂ) (hQ : Q.PosSemidef)
    (C : ∀ j,Matrix ι (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1)
    (horth : ∀ j l,j≠l → (C j)ᴴ*C l=0)
    (w : J → ℝ)
    (hdecode : ∀ j (Y : Matrix (κ j) (κ j) ℂ),Y.PosSemidef →
      w j*Y.trace.re ≤ (Q*F (C j*Y*(C j)ᴴ)).trace.re)
    (hoff : ∀ j l,j≠l → ∀ Y : Matrix (κ j) (κ l) ℂ,F (C j*Y*(C l)ᴴ)=0)
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (hcomm : (∑ j,C j*(C j)ᴴ)*X=X*(∑ j,C j*(C j)ᴴ)) :
    (∑ j,w j*((C j*(C j)ᴴ)*X).trace.re) ≤ (Q*F X).trace.re := by
  classical
  let P := ∑ j,C j*(C j)ᴴ
  have hiso := concatenateIsometries_isometry C hC horth
  have he : concatenateIsometries C*(concatenateIsometries C)ᴴ=P :=
    concatenateIsometries_projection C
  have hP : P.IsHermitian := by
    rw [← he]
    exact Matrix.isHermitian_mul_conjTranspose_self _
  have hPP : P*P=P := by
    rw [← he]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (concatenateIsometries C)ᴴ,hiso,Matrix.one_mul]
  have hR : (X-P*X*P).PosSemidef :=
    projection_remainder_posSemidef_of_commute P X hP hPP hX hcomm
  have hrem := Extraction.positive_product_trace_re Q (F (X-P*X*P)) hQ (hF _ hR)
  simp only [map_sub,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re] at hrem
  have hselected :
      (∑ j,w j*((C j*(C j)ᴴ)*X).trace.re) ≤ (Q*F (P*X*P)).trace.re := by
    rw [channel_orthogonal_block_sum F C hoff X]
    simp only [Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hY := hX.conjTranspose_mul_mul_same (C j)
    have h := hdecode j _ hY
    have ht : ((C j)ᴴ*X*C j).trace=((C j*(C j)ᴴ)*X).trace := by
      rw [Matrix.trace_mul_cycle]
    rwa [ht] at h
  linarith

end SpectralProtocol