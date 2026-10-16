import SchurCompletion.PermutationAction

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace ExtractionSchur

open ExtractionRankSupport

noncomputable section

/-- Equality of actual column Gram matrices is witnessed by an actual
ambient unitary, including singular matrices. -/
theorem exists_unitary_mul_of_equal_gram {ι ν : Type*} [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν] (X Y : Matrix ι ν ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    ∃ U : Matrix.unitaryGroup ι ℂ, (U : Matrix ι ι ℂ) * Y = X := by
  classical
  obtain ⟨P,hP,hPP,hPR,hPRank,hPfix⟩ :=
    MatrixSubspace.exists_subspace_projection (LinearMap.range Y.mulVecLin)
  obtain ⟨κ,iκ,eκ,F,hF,hFP,hCard⟩ := Extraction.exists_projection_factor P hP hPP
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  have hRangeF : LinearMap.range F.mulVecLin = LinearMap.range Y.mulVecLin := by
    rw [isometry_factor_range F hF, hFP, hPR]
  have hPY : P * Y = Y := by
    have hcol (w : ν) : P *ᵥ Y.col w = Y.col w := by
      apply hPfix
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨w,rfl⟩
    ext i w
    simpa only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply,
      Matrix.mul_apply] using congrFun (hcol w) i
  let B := Fᴴ * Y
  have hFB : F * B = Y := by
    dsimp only [B]
    rw [← Matrix.mul_assoc, hFP, hPY]
  have hBsurj : Function.Surjective B.mulVec := by
    intro v
    have hv : F *ᵥ v ∈ LinearMap.range Y.mulVecLin := by
      rw [← hRangeF]
      exact ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := hv
    refine ⟨w, ?_⟩
    change Y *ᵥ w = F *ᵥ v at hw
    change (Fᴴ * Y) *ᵥ w = v
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hF, Matrix.one_mulVec]
  obtain ⟨R,hBR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hBsurj
  let C := X * R
  have hYR : Y * R = F := by
    rw [← hFB, Matrix.mul_assoc, hBR, Matrix.mul_one]
  have hC : Cᴴ * C = 1 := by
    calc
      _ = Rᴴ * (Xᴴ * X) * R := by simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Y * R)ᴴ * (Y * R) := by rw [hGram]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hYR, hF]
  let T := 1-R*B
  have hBT : B * T = 0 := by
    simp only [T, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBR, Matrix.one_mul, sub_self]
  have hYT : Y * T = 0 := by rw [← hFB, Matrix.mul_assoc, hBT, Matrix.mul_zero]
  have hXTgram : (X*T)ᴴ * (X*T) = 0 := by
    calc
      _ = (Y*T)ᴴ * (Y*T) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Xᴴ, hGram]
        rw [Matrix.mul_assoc]
      _ = 0 := by rw [hYT]; simp
  have hXT : X*T = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (by rw [hXTgram]; simp)
  have hCB : C * B = X := by
    change X*(1-R*B) = 0 at hXT
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc] at hXT
    exact (sub_eq_zero.mp hXT).symm
  obtain ⟨U,hU⟩ := Extraction.exists_unitary_between_isometries F C hF hC
  refine ⟨U, ?_⟩
  rw [← hFB, ← Matrix.mul_assoc, hU, hCB]

/-- A true polar factorization on the original coordinate space. -/
theorem exists_unitary_mul_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ), H.PosSemidef ∧
      (U : Matrix ι ι ℂ) * H = X := by
  let H := CFC.sqrt (Xᴴ * X)
  have hH : H.PosSemidef := (CFC.sqrt_nonneg (Xᴴ * X)).posSemidef
  have hHH : Hᴴ * H = Xᴴ * X := by
    rw [hH.isHermitian.eq]
    simpa only [pow_two] using
      CFC.sq_sqrt (Xᴴ * X) (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  obtain ⟨U,hU⟩ := exists_unitary_mul_of_equal_gram X H hHH.symm
  exact ⟨U,H,hH,hU⟩

end
end ExtractionSchur
