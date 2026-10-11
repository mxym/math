import HydrologyTree.DependentBlocks

/-! Exact determinant of arbitrary heterogeneous branches attached at one root. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {C : Type*} [Fintype C] [LinearOrder C] {V : C → Type*}
  [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]

def arrowRow (r : ∀ c, V c) (a : C → ℝ) : Matrix Unit (Σ c, V c) ℝ :=
  Matrix.of fun _ z => if z.2 = r z.1 then a z.1 else 0

def arrowColumn (r : ∀ c, V c) (f : C → ℝ) : Matrix (Σ c, V c) Unit ℝ :=
  Matrix.of fun z _ => if z.2 = r z.1 then f z.1 else 0

/-- The root diagonal is d and every branch block is retained unaltered. -/
def arrowMatrix (d : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) : Matrix (Unit ⊕ (Σ c, V c)) (Unit ⊕ (Σ c, V c)) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => d) (arrowRow r a) (arrowColumn r f)
    (Matrix.blockDiagonal' B)

lemma arrowRow_mul_block (r : ∀ c, V c) (a : C → ℝ)
    (G : ∀ c, Matrix (V c) (V c) ℝ) (c : C) (i : V c) :
    (arrowRow r a * Matrix.blockDiagonal' G) () ⟨c,i⟩ = a c * G c (r c) i := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single c]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    simp [arrowRow, ite_mul]
  · intro d _ hdc
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.blockDiagonal'_apply_ne G j i hdc, mul_zero]
  · simp

lemma arrow_sandwich (r : ∀ c, V c) (a f : C → ℝ)
    (G : ∀ c, Matrix (V c) (V c) ℝ) :
    (arrowRow r a * Matrix.blockDiagonal' G * arrowColumn r f) () () =
      ∑ c, a c * G c (r c) (r c) * f c := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [arrowRow_mul_block]
  simp [arrowColumn, mul_ite]

/-- The scalar Schur formula after the actual heterogeneous inverse is proved. -/
theorem det_arrowMatrix_inverse (d : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) (hB : ∀ c, (B c).det ≠ 0) :
    (arrowMatrix d B r a f).det =
      (∏ c, (B c).det) * (d - ∑ c, a c * (B c)⁻¹ (r c) (r c) * f c) := by
  have hd : (Matrix.blockDiagonal' B).det ≠ 0 := by
    rw [det_dependent_blocks]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => hB c)
  letI : Invertible (Matrix.blockDiagonal' B) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hd)
  rw [arrowMatrix, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    inverse_dependent_blocks B hB, det_dependent_blocks, Matrix.det_unique, Matrix.sub_apply,
    Matrix.of_apply, arrow_sandwich]

/-- Denominator-free edge/cofactor formula. Nonzero determinants are needed only
for this field step and will be removed in the characteristic-polynomial theorem. -/
theorem det_arrowMatrix_cofactors (d : ℝ) (B : ∀ c, Matrix (V c) (V c) ℝ)
    (r : ∀ c, V c) (a f : C → ℝ) (hB : ∀ c, (B c).det ≠ 0) :
    (arrowMatrix d B r a f).det = d * (∏ c, (B c).det) -
      ∑ c, a c * f c * (B c).adjugate (r c) (r c) *
        ∏ j ∈ Finset.univ.erase c, (B j).det := by
  rw [det_arrowMatrix_inverse d B r a f hB, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (B j).det) (Finset.mem_univ c),
      Matrix.inv_def]
    simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    field_simp [hB c]
    <;> ring

end HydrologyTree
