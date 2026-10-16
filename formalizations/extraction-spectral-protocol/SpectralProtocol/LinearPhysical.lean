import SpectralProtocol.MultisectorDecoder

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι ο τ : Type*} [Fintype ι] [Fintype ο] [Fintype τ]
  [DecidableEq ι] [DecidableEq ο]

/-- The actual finite Kraus map including its actual initial unitary, as a
complex linear map for exact finite block-sum calculations. -/
noncomputable def physicalChannelLinearMap (A : τ → Matrix ο ι ℂ)
    (U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ where
  toFun := fun X => Extraction.krausApply A ((U : Matrix ι ι ℂ)*X*(U : Matrix ι ι ℂ)ᴴ)
  map_add' := by
    intro X Y
    simp only [Matrix.mul_add,Matrix.add_mul,Extraction.krausApply_add]
  map_smul' := by
    intro c X
    simp only [Matrix.mul_smul,Matrix.smul_mul,Extraction.krausApply,Finset.smul_sum,
      RingHom.id_apply]

theorem physicalChannelLinearMap_posSemidef (A : τ → Matrix ο ι ℂ)
    (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) (hX : X.PosSemidef) :
    (physicalChannelLinearMap A U X).PosSemidef :=
  Extraction.krausApply_posSemidef _ _ (hX.mul_mul_conjTranspose_same _)

variable {J : Type*} {κ : J → Type*} [Fintype J] [DecidableEq J]
  [∀ j,Fintype (κ j)] [∀ j,DecidableEq (κ j)]

theorem concatenateIsometries_projection (C : ∀ j,Matrix ι (κ j) ℂ) :
    concatenateIsometries C*(concatenateIsometries C)ᴴ=∑ j,C j*(C j)ᴴ := by
  ext x y
  simp only [concatenateIsometries,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_sigma,Matrix.sum_apply]

/-- Orthogonal projections commute with a PSD input precisely as needed for
a positive discarded complement; arbitrary within-support coherences remain. -/
theorem projection_remainder_posSemidef_of_commute
    (P X : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P*P=P)
    (hX : X.PosSemidef) (hcomm : P*X=X*P) : (X-P*X*P).PosSemidef := by
  have hPX : P*X*P=P*X := by
    calc
      P*X*P = (X*P)*P := by rw [hcomm]
      _ = X*P := by rw [Matrix.mul_assoc,hPP]
      _ = P*X := hcomm.symm
  have hPH : (1-P)ᴴ=1-P := by simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.eq]
  have he : (1-P)*X*(1-P)=X-P*X*P := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    rw [hPX,hcomm]
    abel
  have h := hX.mul_mul_conjTranspose_same (1-P)
  rwa [hPH,he] at h

end SpectralProtocol