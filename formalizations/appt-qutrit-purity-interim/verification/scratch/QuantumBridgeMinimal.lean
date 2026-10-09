import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators

namespace QuantumBridgeMinimal

abbrev I := Fin 3 × Fin 3

noncomputable def delta (p : I) (x : I) : ℝ := if x = p then 1 else 0

noncomputable def r : ℝ := (Real.sqrt 2)⁻¹

/-- Columns are labelled by their original spectral indices:
    antisymmetric 01/02/12, diagonal 22, symmetric 12/02,
    diagonal 11, symmetric 01, diagonal 00. -/
noncomputable def qAcol : Fin 9 → I → ℝ :=
  ![(fun x => r * (delta (0, 1) x - delta (1, 0) x)),
    (fun x => r * (delta (0, 2) x - delta (2, 0) x)),
    (fun x => r * (delta (1, 2) x - delta (2, 1) x)),
    delta (2, 2),
    (fun x => r * (delta (1, 2) x + delta (2, 1) x)),
    (fun x => r * (delta (0, 2) x + delta (2, 0) x)),
    delta (1, 1),
    (fun x => r * (delta (0, 1) x + delta (1, 0) x)),
    delta (0, 0)]

noncomputable def qA : Matrix I (Fin 9) ℝ := fun x j => qAcol j x

noncomputable def dA (y : Fin 9 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.diagonal y

noncomputable def rhoA (y : Fin 9 → ℝ) : Matrix I I ℝ :=
  qA * dA y * Matrix.transpose qA

noncomputable def ptranspose (ρ : Matrix I I ℝ) : Matrix I I ℝ :=
  fun (i,j) (k,l) => ρ (i,l) (k,j)

noncomputable def diagonalEmbed (v : Fin 3 → ℝ) : I → ℝ :=
  fun x => if x.1 = x.2 then v x.1 else 0

noncomputable def qform (ρ : Matrix I I ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dotProduct (diagonalEmbed v) (Matrix.mulVec (ptranspose ρ) (diagonalEmbed v))

noncomputable def matA (y : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*y 8, y 7-y 0, y 5-y 1;
     y 7-y 0, 2*y 6, y 4-y 2;
     y 5-y 1, y 4-y 2, 2*y 3]

noncomputable def quadA (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dotProduct v (Matrix.mulVec (matA y) v)

theorem r_mul_r : r * r = (1 / 2 : ℝ) := by
  dsimp [r]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The nine columns are an orthonormal eigenbasis for the A witness. -/
theorem qA_orth : Matrix.transpose qA * qA = (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, qA, qAcol, delta,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply, r_mul_r]

/-- Both row and column orthogonality are checked explicitly. -/
theorem qA_row_orth : qA * Matrix.transpose qA = (1 : Matrix I I ℝ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, qA, qAcol, delta,
      Fin.sum_univ_succ, Matrix.one_apply, r_mul_r]

/-- Entry formula for the actual orthogonal conjugation. -/
theorem rhoA_apply (y : Fin 9 → ℝ) (x z : I) :
    rhoA y x z = ∑ j : Fin 9, qA x j * y j * qA z j := by
  change (∑ j : Fin 9, (qA * Matrix.diagonal y) x j * qA z j) = _
  simp only [Matrix.mul_diagonal]

/-- The partial transpose sends the selected two-particle corner to A/2. -/
theorem rhoA_corner (y : Fin 9 → ℝ) (i j : Fin 3) :
    rhoA y (i,j) (j,i) = matA y i j / 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [rhoA_apply, qA, qAcol, delta, matA, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [pow_two, r_mul_r] <;> ring

/-- Extraction for an arbitrary tensor-indexed real matrix. -/
theorem qform_corner (ρ : Matrix I I ℝ) (v : Fin 3 → ℝ) :
    qform ρ v = ∑ i : Fin 3, ∑ j : Fin 3, v i * ρ (i,j) (j,i) * v j := by
  simp [qform, diagonalEmbed, ptranspose, dotProduct, Matrix.mulVec,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- Exact extraction, without assuming positivity or eigenvalue ordering. -/
theorem qform_rhoA (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) :
    qform (rhoA y) v = quadA y v / 2 := by
  rw [qform_corner]
  simp_rw [rhoA_corner]
  simp [quadA, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- B exchanges the eigenvectors assigned to spectral entries 5 and 6. -/
noncomputable def qB : Matrix I (Fin 9) ℝ :=
  fun x j => qA x (Equiv.swap (5 : Fin 9) 6 j)

noncomputable def rhoB (y : Fin 9 → ℝ) : Matrix I I ℝ :=
  qB * Matrix.diagonal y * Matrix.transpose qB

noncomputable def matB (y : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*y 8, y 7-y 0, y 6-y 1;
     y 7-y 0, 2*y 5, y 4-y 2;
     y 6-y 1, y 4-y 2, 2*y 3]

noncomputable def quadB (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dotProduct v (Matrix.mulVec (matB y) v)

theorem qB_orth : Matrix.transpose qB * qB = (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, qB, Equiv.swap_apply_def,
      qA, qAcol, delta, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.one_apply, r_mul_r]

theorem qB_row_orth : qB * Matrix.transpose qB = (1 : Matrix I I ℝ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, qB, Equiv.swap_apply_def,
      qA, qAcol, delta, Fin.sum_univ_succ, Matrix.one_apply, r_mul_r]

theorem rhoB_apply (y : Fin 9 → ℝ) (x z : I) :
    rhoB y x z = ∑ j : Fin 9, qB x j * y j * qB z j := by
  change (∑ j : Fin 9, (qB * Matrix.diagonal y) x j * qB z j) = _
  simp only [Matrix.mul_diagonal]

theorem rhoB_corner (y : Fin 9 → ℝ) (i j : Fin 3) :
    rhoB y (i,j) (j,i) = matB y i j / 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [rhoB_apply, qB, Equiv.swap_apply_def, qA, qAcol, delta, matB,
      Fin.sum_univ_succ] <;>
    ring_nf <;> simp [pow_two, r_mul_r] <;> ring

theorem qform_rhoB (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) :
    qform (rhoB y) v = quadB y v / 2 := by
  rw [qform_corner]
  simp_rw [rhoB_corner]
  simp [quadB, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- Real two-qutrit orbit semantics: every orthogonal change of basis of the
    diagonal matrix with entries y has positive-semidefinite partial transpose.
    Both orthogonality equations are required and explicitly proved for A/B.
    This predicate does not mention either extracted matrix. -/
def APPTChosen (y : Fin 9 → ℝ) : Prop :=
  ∀ Q : Matrix I (Fin 9) ℝ,
    Matrix.transpose Q * Q = (1 : Matrix (Fin 9) (Fin 9) ℝ) →
    Q * Matrix.transpose Q = (1 : Matrix I I ℝ) →
      (ptranspose (Q * Matrix.diagonal y * Matrix.transpose Q)).PosSemidef

theorem appt_implies_quadA_nonneg (y : Fin 9 → ℝ) (h : APPTChosen y)
    (v : Fin 3 → ℝ) : 0 ≤ quadA y v := by
  have hp : (ptranspose (rhoA y)).PosSemidef := h qA qA_orth qA_row_orth
  have hq : 0 ≤ qform (rhoA y) v := by
    simpa [qform] using hp.dotProduct_mulVec_nonneg (diagonalEmbed v)
  rw [qform_rhoA] at hq
  linarith

theorem appt_implies_quadB_nonneg (y : Fin 9 → ℝ) (h : APPTChosen y)
    (v : Fin 3 → ℝ) : 0 ≤ quadB y v := by
  have hp : (ptranspose (rhoB y)).PosSemidef := h qB qB_orth qB_row_orth
  have hq : 0 ≤ qform (rhoB y) v := by
    simpa [qform] using hp.dotProduct_mulVec_nonneg (diagonalEmbed v)
  rw [qform_rhoB] at hq
  linarith

theorem matA_hermitian (y : Fin 9 → ℝ) : (matA y).IsHermitian := by
  change Matrix.conjTranspose (matA y) = matA y
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, Matrix.conjTranspose_apply]

theorem matB_hermitian (y : Fin 9 → ℝ) : (matB y).IsHermitian := by
  change Matrix.conjTranspose (matB y) = matB y
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matB, Matrix.conjTranspose_apply]

theorem appt_implies_matA_psd (y : Fin 9 → ℝ) (h : APPTChosen y) :
    (matA y).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (matA_hermitian y)
  intro v
  simpa [quadA] using appt_implies_quadA_nonneg y h v

theorem appt_implies_matB_psd (y : Fin 9 → ℝ) (h : APPTChosen y) :
    (matB y).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (matB_hermitian y)
  intro v
  simpa [quadB] using appt_implies_quadB_nonneg y h v

/-- A negative extracted quadratic form gives an actual violating orbit. -/
theorem negative_quadA_not_appt (y : Fin 9 → ℝ) (v : Fin 3 → ℝ)
    (hv : quadA y v < 0) : ¬ APPTChosen y := by
  intro h
  exact (not_lt_of_ge (appt_implies_quadA_nonneg y h v)) hv

theorem negative_quadB_not_appt (y : Fin 9 → ℝ) (v : Fin 3 → ℝ)
    (hv : quadB y v < 0) : ¬ APPTChosen y := by
  intro h
  exact (not_lt_of_ge (appt_implies_quadB_nonneg y h v)) hv

/-- Sorted, nonnegative, trace-one negative control: a pure spectral orbit. -/
noncomputable def pureSpectrum : Fin 9 → ℝ := ![1,0,0,0,0,0,0,0,0]
noncomputable def negativeVector : Fin 3 → ℝ := ![1,1,0]

theorem pure_quadA : quadA pureSpectrum negativeVector = -2 := by
  norm_num [quadA, matA, pureSpectrum, negativeVector,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

theorem pure_pt_negative : qform (rhoA pureSpectrum) negativeVector = -1 := by
  rw [qform_rhoA, pure_quadA]
  norm_num

theorem pure_not_appt : ¬ APPTChosen pureSpectrum := by
  apply negative_quadA_not_appt pureSpectrum negativeVector
  rw [pure_quadA]
  norm_num

end QuantumBridgeMinimal
