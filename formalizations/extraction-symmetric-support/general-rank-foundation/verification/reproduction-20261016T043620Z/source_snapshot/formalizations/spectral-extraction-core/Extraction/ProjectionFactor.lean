import Extraction.SubspacePacking

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

universe u
variable {ι : Type u} {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem coordinateIsometry_projector (f : κ ↪ ι) (p q : ι) :
    (coordinateIsometry f * (coordinateIsometry f)ᴴ) p q =
      if p = q then if p ∈ Set.range f then 1 else 0 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    by_cases hp : p ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hp
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateIsometry,
        f.injective.eq_iff, eq_comm]
    · have hf (j : κ) : p ≠ f j := by
        intro h
        exact hp ⟨j, h.symm⟩
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateIsometry, hp, hf]
  · rw [if_neg hpq]
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hp : p = f j <;> by_cases hq : q = f j <;>
      simp_all [Matrix.conjTranspose_apply, coordinateIsometry]

/-- Every actual Hermitian idempotent has an actual orthonormal column
factorization of exactly its matrix rank. No basis or rank certificate is
provided by the caller. -/
theorem exists_projection_factor (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) :
    ∃ (κ : Type u) (_ : Fintype κ) (_ : DecidableEq κ)
      (C : Matrix ι κ ℂ),
      Cᴴ * C = 1 ∧ C * Cᴴ = P ∧ Fintype.card κ = P.rank := by
  classical
  let U := hP.eigenvectorUnitary
  have hU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hUU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hd : (U : Matrix ι ι ℂ)ᴴ * P * U =
      Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hP.conjStarAlgAut_star_eigenvectorUnitary
  have hdd : Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) *
      Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) =
      Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    rw [← hd]
    calc
      _ = (U : Matrix ι ι ℂ)ᴴ * (P * P) * U := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ), hUU, Matrix.one_mul]
      _ = _ := by rw [hPP]
  have heig (i : ι) : hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
    have hh := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) hdd
    have hs : hP.eigenvalues i * hP.eigenvalues i = hP.eigenvalues i := by
      simpa [Matrix.diagonal_mul_diagonal, Complex.mul_re] using hh
    have hz : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  let κ := {i : ι // hP.eigenvalues i ≠ 0}
  let f : κ ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let G := coordinateIsometry f
  let C := (U : Matrix ι ι ℂ) * G
  have hG : Gᴴ * G = 1 := coordinateIsometry_isometry f
  have hGG : G * Gᴴ = Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    ext p q
    rw [coordinateIsometry_projector]
    by_cases hpq : p = q
    · subst q
      by_cases hp : hP.eigenvalues p = 0
      · have hn : p ∉ Set.range f := by
          rintro ⟨i, hi⟩
          change (i : ι) = p at hi
          exact i.property (by rw [hi, hp])
        simp [hp, hn]
      · have hin : p ∈ Set.range f := ⟨⟨p,hp⟩, rfl⟩
        have he : hP.eigenvalues p = 1 := (heig p).resolve_left hp
        simp [hin, he]
    · simp [hpq, Matrix.diagonal_apply]
  refine ⟨κ, inferInstance, inferInstance, C, ?_, ?_, ?_⟩
  · exact isometry_mul (U : Matrix ι ι ℂ) G hU hG
  · change (U : Matrix ι ι ℂ) * G * ((U : Matrix ι ι ℂ) * G)ᴴ = P
    rw [Matrix.conjTranspose_mul]
    have he : (U : Matrix ι ι ℂ) * G * (Gᴴ * (U : Matrix ι ι ℂ)ᴴ) =
        (U : Matrix ι ι ℂ) * (G * Gᴴ) * (U : Matrix ι ι ℂ)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [he, hGG]
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hP.spectral_theorem.symm
  · exact hP.rank_eq_card_non_zero_eigs.symm

end Extraction
