import APPTReview.SingularAttainment

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Orthogonalize all rows by one actual unitary, including rank-deficient matrices. -/
theorem exists_unitary_orthogonal_rows (T : Matrix a b ℂ) :
    ∃ (U : Matrix.unitaryGroup a ℂ) (R : Matrix a b ℂ) (d : a → ℝ),
      (∀ i, 0 ≤ d i) ∧
      T = (U : Matrix a a ℂ) * R ∧
      R * Rᴴ = Matrix.diagonal (fun i => (d i : ℂ)) := by
  let hG := Matrix.posSemidef_self_mul_conjTranspose T
  let U := hG.isHermitian.eigenvectorUnitary
  let R := (U : Matrix a a ℂ)ᴴ * T
  refine ⟨U,R,hG.isHermitian.eigenvalues,hG.eigenvalues_nonneg,?_,?_⟩
  · dsimp only [R]
    have hu : (U : Matrix a a ℂ)*(U : Matrix a a ℂ)ᴴ=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  · have hd := hG.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at hd
    simpa only [R, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hd

/-- A zero diagonal entry of a row Gram matrix means the entire row is zero. -/
theorem gram_zero_row (R : Matrix a b ℂ) (i : a) (hi : (R*Rᴴ) i i=0) :
    ∀ x, R i x=0 := by
  have hz := congrArg Complex.re hi
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.zero_re] at hz
  intro x
  have hp (y : b) : 0 ≤ (R i y).re*(R i y).re+(R i y).im*(R i y).im :=
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hs : (∑ y, ((R i y).re*(R i y).re+(R i y).im*(R i y).im))=0 := by
    convert hz using 1 <;> simp
  have he := Finset.single_le_sum (fun y (_ : y∈Finset.univ) => hp y) (Finset.mem_univ x)
  rw [hs] at he
  apply Complex.ext <;> simp only [Complex.zero_re,Complex.zero_im] <;>
    nlinarith [sq_nonneg (R i x).re,sq_nonneg (R i x).im]

/-- Normalize an orthogonal row family; zero rows stay zero rather than assuming full rank. -/
noncomputable def normalizeRows (R : Matrix a b ℂ) (s : a → ℝ) : Matrix a b ℂ :=
  Matrix.diagonal (fun i => ((s i : ℂ)⁻¹)) * R

theorem normalizeRows_apply (R : Matrix a b ℂ) (s : a → ℝ) (i : a) (x : b) :
    normalizeRows R s i x = (s i : ℂ)⁻¹ * R i x := by
  simp [normalizeRows, Matrix.diagonal_mul]

end APPTReview
