import APPTReview.Star
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing
open scoped BigOperators MatrixOrder
open Matrix
namespace APPTReview
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonnegative_matrix_quadratic_abs (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) :
    |star x ⬝ᵥ (A *ᵥ x)| ≤
      star (fun i => |x i|) ⬝ᵥ (A *ᵥ (fun i => |x i|)) := by
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
  calc
    |∑ i, ∑ j, x i * (A i j * x j)|
        ≤ ∑ i, |∑ j, x i * (A i j * x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * (A i j * x j)| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by simp [abs_mul, abs_of_nonneg (hA _ _)]

theorem nonnegative_matrix_two_sided (A : Matrix ι ι ℝ) (c : ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (hm : (c • (1 : Matrix ι ι ℝ)-A).PosSemidef) :
    (c • (1 : Matrix ι ι ℝ)+A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (show IsSelfAdjoint c by rfl)).add hA)
  intro x
  have hp := hm.dotProduct_mulVec_nonneg (fun i => |x i|)
  have habs := nonnegative_matrix_quadratic_abs A hn x
  have hlow := neg_abs_le (star x ⬝ᵥ (A *ᵥ x))
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul,
    star_trivial, smul_eq_mul] at hp ⊢
  have he : (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x := by
    simp [dotProduct, ← sq, sq_abs]
  rw [he] at hp
  simp only [star_trivial] at habs hlow
  linarith

theorem two_sided_matrix_square_bound (A : Matrix ι ι ℝ) (c : ℝ)
    (hA : A.IsHermitian)
    (hm : (c • (1 : Matrix ι ι ℝ)-A).PosSemidef)
    (hp : (c • (1 : Matrix ι ι ℝ)+A).PosSemidef) (x : ι → ℝ) :
    (∑ i, (A *ᵥ x) i ^ 2) ≤ c^2 * ∑ i, x i ^ 2 := by
  have hc : Commute (c • (1 : Matrix ι ι ℝ)-A) (c • (1 : Matrix ι ι ℝ)+A) := by
    change (c • (1 : Matrix ι ι ℝ)-A)*(c • (1 : Matrix ι ι ℝ)+A) = (c • (1 : Matrix ι ι ℝ)+A)*(c • (1 : Matrix ι ι ℝ)-A)
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  have hprod := hc.mul_nonneg hm.nonneg hp.nonneg
  have he : (c • (1 : Matrix ι ι ℝ)-A)*(c • (1 : Matrix ι ι ℝ)+A) =
      c^2 • (1 : Matrix ι ι ℝ)-A*A := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [he] at hprod
  have hq := hprod.posSemidef.dotProduct_mulVec_nonneg x
  have hv : x ᵥ* A = A *ᵥ x := by
    ext i
    simp only [Matrix.vecMul, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro j _
    have hsym : A j i = A i j := by
      have hh := congrArg (fun M => M i j) hA.eq
      simpa [Matrix.conjTranspose_apply] using hh
    change x j * A j i = A i j * x j
    rw [hsym, mul_comm]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_trivial, smul_eq_mul,
    ← Matrix.mulVec_mulVec] at hq
  rw [Matrix.dotProduct_mulVec, hv] at hq
  simpa [dotProduct, ← sq] using hq

theorem nonnegative_matrix_square_bound (A : Matrix ι ι ℝ) (c : ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (hm : (c • (1 : Matrix ι ι ℝ)-A).PosSemidef) (x : ι → ℝ) :
    (∑ i, (A *ᵥ x) i ^ 2) ≤ c^2 * ∑ i, x i ^ 2 :=
  two_sided_matrix_square_bound A c hA hm
    (nonnegative_matrix_two_sided A c hA hn hm) x

end APPTReview
