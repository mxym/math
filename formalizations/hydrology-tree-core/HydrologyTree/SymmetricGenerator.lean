import HydrologyTree.GroundedPositivity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual positive diagonal similarity to a negative definite symmetric matrix.
The change of basis and its inverse are explicitly constructed from rates. -/
open Matrix
noncomputable section
namespace HydrologyTree

def sqrtWeightDiagonal {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.diagonal (fun v => Real.sqrt (balanceWeight t x v))

def invSqrtWeightDiagonal {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.diagonal (fun v => (Real.sqrt (balanceWeight t x v))⁻¹)

lemma sqrtWeightDiagonal_mul_inv {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    sqrtWeightDiagonal t x * invSqrtWeightDiagonal t x = 1 := by
  rw [sqrtWeightDiagonal, invSqrtWeightDiagonal, Matrix.diagonal_mul_diagonal]
  have hpos (v : Fin (n+1)) : 0 < Real.sqrt (balanceWeight t x v) :=
    Real.sqrt_pos.2 (balanceWeight_pos t x ha hf v)
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal_apply, Matrix.one_apply, ne_of_gt (hpos i)]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

lemma invSqrtWeightDiagonal_mul_sqrt {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    invSqrtWeightDiagonal t x * sqrtWeightDiagonal t x = 1 := by
  have h := Matrix.commute_diagonal
    (fun v : Fin (n+1) => (Real.sqrt (balanceWeight t x v))⁻¹)
    (fun v : Fin (n+1) => Real.sqrt (balanceWeight t x v))
  change invSqrtWeightDiagonal t x * sqrtWeightDiagonal t x =
    sqrtWeightDiagonal t x * invSqrtWeightDiagonal t x at h
  rw [h]
  exact sqrtWeightDiagonal_mul_inv t x ha hf

lemma weight_mul_invSqrt {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    Matrix.diagonal (balanceWeight t x) * invSqrtWeightDiagonal t x = sqrtWeightDiagonal t x := by
  rw [invSqrtWeightDiagonal, sqrtWeightDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext v
  have hs : Real.sqrt (balanceWeight t x v) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (balanceWeight_pos t x ha hf v))
  have hsq := Real.sq_sqrt (balanceWeight_pos t x ha hf v).le
  change balanceWeight t x v / Real.sqrt (balanceWeight t x v) = Real.sqrt (balanceWeight t x v)
  apply (div_eq_iff hs).mpr
  nlinarith [hsq]

/-- The actual congruence form whose positivity is linked to the physical generator. -/
def symmetricNegativeGenerator {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  invSqrtWeightDiagonal t x * weightedNegativeGenerator t x * invSqrtWeightDiagonal t x

lemma invSqrtWeightDiagonal_hermitian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (invSqrtWeightDiagonal t x)ᴴ = invSqrtWeightDiagonal t x := by
  simp [invSqrtWeightDiagonal]

/-- Positivity of the actual symmetrized negative generator. -/
theorem symmetricNegativeGenerator_posDef {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (hf : ∀ e : Fin n, 0 < x.2 e) : (symmetricNegativeGenerator t x).PosDef := by
  have hinj : Function.Injective (invSqrtWeightDiagonal t x).mulVec := by
    intro z w h
    have hh := congrArg (fun v => sqrtWeightDiagonal t x *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, sqrtWeightDiagonal_mul_inv t x ha hf,
      Matrix.one_mulVec] using hh
  have h := (weightedNegativeGenerator_posDef t x hell ha hf).conjTranspose_mul_mul_same hinj
  simpa only [invSqrtWeightDiagonal_hermitian, symmetricNegativeGenerator] using h

/-- Exact similarity identity, including the explicit inverse change of basis. -/
theorem physical_negative_similarity {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    symmetricNegativeGenerator t x =
      -(invSqrtWeightDiagonal t x * compartmentMatrix t x * sqrtWeightDiagonal t x) := by
  rw [symmetricNegativeGenerator, weightedNegativeGenerator, Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  simp only [Matrix.mul_assoc, weight_mul_invSqrt t x ha hf]

/-- Actual characteristic polynomial equals that of a negative-definite symmetric
matrix. This is a proved similarity, not an assumption about real eigenvalues. -/
theorem physical_charpoly_symmetric {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    physicalCharacteristic t x = (-symmetricNegativeGenerator t x).charpoly := by
  rw [physical_negative_similarity t x ha hf, neg_neg]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, sqrtWeightDiagonal_mul_inv t x ha hf]
  simp [physicalCharacteristic]

end HydrologyTree
