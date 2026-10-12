import HydrologyTree.BalanceWeights
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The actual weighted compartment matrix is a grounded tree Dirichlet form.
All matrix equalities and the quadratic identity are proved edge by edge. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma single_mul_weight_diagonal (i j : I) (r : ℝ) (w : I → ℝ) :
    Matrix.single i j r * Matrix.diagonal w = Matrix.single i j (r*w j) := by
  ext u v
  rw [Matrix.mul_diagonal]
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [Matrix.single_apply,hi,hj]

/-- The rank-one Laplacian form (e_i-e_j)(e_i-e_j)^T. -/
def edgeGram (i j : I) : Matrix I I ℝ :=
  Matrix.single i i 1 + Matrix.single j j 1 - Matrix.single i j 1 - Matrix.single j i 1

lemma edgeGram_transpose (i j : I) : (edgeGram i j).transpose = edgeGram i j := by
  ext u v
  simp only [edgeGram, Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_apply]
  simp [and_comm]
  <;> ring

lemma edgeGram_energy (i j : I) (z : I → ℝ) :
    z ⬝ᵥ (edgeGram i j *ᵥ z) = (z i-z j)^2 := by
  simp only [edgeGram, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    Matrix.single_mulVec_eq, dotProduct_smul, dotProduct_single_one, one_mul, smul_eq_mul]
  ring

/-- Actual weighted negative generator, not an assumed symmetric proxy. -/
def weightedNegativeGenerator {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  -(compartmentMatrix t x * Matrix.diagonal (balanceWeight t x))

lemma edge_weighted_matrix {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) (e : Fin n) :
    edgeMatrix t x e * Matrix.diagonal (balanceWeight t x) =
      -(x.2 e * balanceWeight t x (t.parent e)) • edgeGram (t.parent e) e.succ := by
  rw [edgeMatrix, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.sub_mul, Matrix.sub_mul]
  simp only [single_mul_weight_diagonal, one_mul, smul_sub, Matrix.smul_single,
    smul_eq_mul, balanceWeight_edge t x ha e]
  simp only [edgeGram, smul_sub, smul_add, Matrix.smul_single, smul_eq_mul,
    mul_one]
  simp only [← Matrix.single_neg]
  abel

/-- Edgewise exact decomposition. All positive rates will be supplied only when
needed for positivity; here inward rates merely need to be nonzero. -/
theorem weightedNegativeGenerator_decomposition {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) :
    weightedNegativeGenerator t x = x.1 0 • Matrix.single 0 0 1 +
      ∑ e : Fin n, (x.2 e * balanceWeight t x (t.parent e)) • edgeGram (t.parent e) e.succ := by
  rw [weightedNegativeGenerator, compartmentMatrix, Matrix.sub_mul,
    Finset.sum_mul, Matrix.smul_mul, single_mul_weight_diagonal, balanceWeight_zero]
  simp only [one_mul]
  simp_rw [edge_weighted_matrix t x ha, neg_smul]
  rw [Finset.sum_neg_distrib]
  abel

/-- Exact energy identity for the constructed physical matrix. -/
theorem weightedNegativeGenerator_energy {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) (z : VertexValues n) :
    z ⬝ᵥ (weightedNegativeGenerator t x *ᵥ z) = x.1 0 * (z 0)^2 +
      ∑ e : Fin n, (x.2 e * balanceWeight t x (t.parent e)) * (z (t.parent e)-z e.succ)^2 := by
  rw [weightedNegativeGenerator_decomposition t x ha, Matrix.add_mulVec, dotProduct_add]
  simp only [Matrix.smul_mulVec, Matrix.single_mulVec_eq, dotProduct_smul,
    dotProduct_single_one, one_mul, smul_eq_mul]
  congr 1
  · ring
  · rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [Matrix.smul_mulVec, dotProduct_smul, edgeGram_energy]
    rfl

/-- Symmetry is derived from the actual generator and the proved weights. -/
theorem weightedNegativeGenerator_isHermitian {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) : (weightedNegativeGenerator t x).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (weightedNegativeGenerator t x).transpose = weightedNegativeGenerator t x
  rw [weightedNegativeGenerator_decomposition t x ha]
  simp [Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
    edgeGram_transpose]

end HydrologyTree
