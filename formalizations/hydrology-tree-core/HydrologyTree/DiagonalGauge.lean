import HydrologyTree.RootAttachment
import HydrologyTree.PhysicalStieltjes

/-! Exact diagonal similarity with nonzero real entries. Characteristic and
all diagonal cofactor identities hold even at singular matrices. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

def diagonalGauge (h : V → ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ :=
  Matrix.diagonal h * A * Matrix.diagonal (fun v => (h v)⁻¹)

@[simp] lemma diagonalGauge_apply (h : V → ℝ) (A : Matrix V V ℝ) (i j : V) :
    diagonalGauge h A i j=h i*A i j*(h j)⁻¹ := by simp [diagonalGauge]

lemma diagonalGauge_add (h : V → ℝ) (A B : Matrix V V ℝ) :
    diagonalGauge h (A+B)=diagonalGauge h A+diagonalGauge h B := by
  simp only [diagonalGauge,Matrix.mul_add,Matrix.add_mul]

lemma diagonalGauge_sub (h : V → ℝ) (A B : Matrix V V ℝ) :
    diagonalGauge h (A-B)=diagonalGauge h A-diagonalGauge h B := by
  simp only [diagonalGauge,Matrix.mul_sub,Matrix.sub_mul]

lemma diagonalGauge_smul (h : V → ℝ) (c : ℝ) (A : Matrix V V ℝ) :
    diagonalGauge h (c • A)=c • diagonalGauge h A := by
  simp only [diagonalGauge,Matrix.mul_smul,Matrix.smul_mul]

lemma diagonalGauge_sum {I : Type*} (h : V → ℝ) (s : Finset I) (A : I → Matrix V V ℝ) :
    diagonalGauge h (∑ i ∈ s, A i)=∑ i ∈ s, diagonalGauge h (A i) := by
  simp only [diagonalGauge,Matrix.mul_sum,Matrix.sum_mul]

lemma diagonalGauge_single (h : V → ℝ) (i j : V) (c : ℝ) :
    diagonalGauge h (Matrix.single i j c)=Matrix.single i j (h i*c*(h j)⁻¹) := by
  ext u v
  by_cases hi : i=u <;> by_cases hj : j=v <;>
    simp [diagonalGauge_apply,Matrix.single_apply,hi,hj]

lemma diagonalGauge_diagonal_single (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (i : V) (c : ℝ) :
    diagonalGauge h (Matrix.single i i c)=Matrix.single i i c := by
  rw [diagonalGauge_single]
  congr 1
  field_simp [hh i]

lemma invDiagonal_mul_diagonal (h : V → ℝ) (hh : ∀ v, h v ≠ 0) :
    Matrix.diagonal (fun v => (h v)⁻¹)*Matrix.diagonal h=(1 : Matrix V V ℝ) := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (hh _)]
  exact Matrix.diagonal_one

/-- No matrix nonsingularity is required: similarity preserves the entire polynomial. -/
theorem diagonalGauge_charpoly (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (A : Matrix V V ℝ) :
    (diagonalGauge h A).charpoly=A.charpoly := by
  rw [diagonalGauge,Matrix.charpoly_mul_comm,← Matrix.mul_assoc,
    invDiagonal_mul_diagonal h hh,Matrix.one_mul]

/-- A diagonal perturbation determines the cofactor, giving a purely polynomial
proof that all original diagonal cofactors are invariant, without division by det A. -/
theorem diagonalGauge_cofactor (h : V → ℝ) (hh : ∀ v, h v ≠ 0)
    (A : Matrix V V ℝ) (o : V) : diagonalCofactor (diagonalGauge h A) o=diagonalCofactor A o := by
  have he := diagonalGauge_charpoly h hh (A+Matrix.single o o 1)
  rw [diagonalGauge_add,diagonalGauge_diagonal_single h hh,
    charpoly_add_single_self,charpoly_add_single_self,diagonalGauge_charpoly h hh] at he
  norm_num only [map_one,one_mul] at he
  exact sub_right_inj.mp he

/-- Exact algebraic inverse entry, including the library's totalized singular
inverse convention. Physical comparisons below never require measurements at poles. -/
lemma inverse_diagonal_eq_cofactor (A : Matrix V V ℝ) (o : V) (s : ℝ) :
    (Matrix.scalar V s-A)⁻¹ o o=(diagonalCofactor A o).eval s/A.charpoly.eval s := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
  rw [← eval_diagonalCofactor,← Matrix.eval_charpoly]
  ring

/-- Every collocated input/output transfer is invariant under diagonal similarity. -/
theorem diagonalGauge_resolvent (h : V → ℝ) (hh : ∀ v, h v ≠ 0)
    (A : Matrix V V ℝ) (o : V) (s : ℝ) :
    (Matrix.scalar V s-diagonalGauge h A)⁻¹ o o=(Matrix.scalar V s-A)⁻¹ o o := by
  rw [inverse_diagonal_eq_cofactor,inverse_diagonal_eq_cofactor,
    diagonalGauge_cofactor h hh,diagonalGauge_charpoly h hh]

/-- Composition remains diagonal and does not depend on choices of eigenvectors. -/
theorem diagonalGauge_comp (h k : V → ℝ) (A : Matrix V V ℝ) :
    diagonalGauge k (diagonalGauge h A)=diagonalGauge (fun v => k v*h v) A := by
  ext i j
  simp only [diagonalGauge_apply,_root_.mul_inv_rev]
  ring

end HydrologyTree
