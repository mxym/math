import CircuitCompletion.Semantics

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

noncomputable def diagonalUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (hz : ∀ i,Complex.normSq (z i)=1) : Matrix.unitaryGroup ι ℂ := by
  refine ⟨Matrix.diagonal z,Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (Matrix.diagonal z)ᴴ*Matrix.diagonal z=1
  have hd : (Matrix.diagonal z)ᴴ=Matrix.diagonal (star z) := by
    ext i j
    by_cases h : i=j
    · subst j;simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]
  rw [hd,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    have h := Complex.mul_conj (z i)
    rw [hz i] at h
    simpa only [starRingEnd_apply,Complex.ofReal_one,Pi.star_apply,mul_comm] using h
  · simp [Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]

theorem singleWire_diagonal_entry {n : ℕ} (i : Fin n) (z : Bool → ℂ)
    (hz : ∀ b,Complex.normSq (z b)=1) (w v : Bits n) :
    (singleWire i (diagonalUnitary z hz) : Matrix (Bits n) (Bits n) ℂ) w v=
      if w=v then z (w i) else 0 := by
  change (Matrix.diagonal z ⊗ₖ (1 : Matrix ({j : Fin n // j≠i}→Bool)
    ({j : Fin n // j≠i}→Bool) ℂ)) ((wireCoordinates i) w) ((wireCoordinates i) v)=_
  simp only [Matrix.kronecker_apply,wireCoordinates,Matrix.diagonal_apply,Matrix.one_apply]
  by_cases hwi : w i=v i
  · by_cases hs : (fun j : {j : Fin n // j≠i} => w j.1)=(fun j => v j.1)
    · have hwv : w=v := by
        apply (wireCoordinates i).injective
        exact Prod.ext hwi hs
      simp [hwi,hs,hwv]
    · have hwv : w≠v := by intro h;apply hs;rw [h]
      simp [hwi,hs,hwv]
  · have hwv : w≠v := by intro h;apply hwi;rw [h]
    simp [hwi,hwv]

theorem singleWire_diagonal_action {n : ℕ} (i : Fin n) (z : Bool → ℂ)
    (hz : ∀ b,Complex.normSq (z b)=1) (v : Bits n → ℂ) :
    ((Gate.single i (diagonalUnitary z hz)).denote : Matrix (Bits n) (Bits n) ℂ)*ᵥv=
      fun w => z (w i)*v w := by
  ext w
  simp only [Matrix.mulVec,dotProduct,Gate.denote,singleWire_diagonal_entry]
  simp

end CircuitCompletion
