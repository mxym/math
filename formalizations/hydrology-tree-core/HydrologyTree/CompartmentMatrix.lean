import HydrologyTree.RateChart
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! The actual conservative bidirected compartment matrix. Edge rates and
original boundary-exit diagonals are retained; no transfer-function reduction
is performed in these definitions. -/
open Matrix Module Polynomial
noncomputable section
namespace HydrologyTree

/-- The actual mass-conserving pair of directed transfers on one tree edge. -/
def edgeMatrix {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (e : Fin n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  x.1 e.succ • (Matrix.single (t.parent e) e.succ (1 : ℝ) - Matrix.single e.succ e.succ (1 : ℝ)) +
    x.2 e • (Matrix.single e.succ (t.parent e) (1 : ℝ) - Matrix.single (t.parent e) (t.parent e) (1 : ℝ))

/-- Edgewise construction of the actual compartment generator, with sole leak at 0. -/
def compartmentMatrix {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (∑ e : Fin n, edgeMatrix t x e) - x.1 0 • Matrix.single 0 0 (1 : ℝ)

lemma sum_single_column {n : ℕ} (i j w : Fin (n+1)) (r : ℝ) :
    (∑ v : Fin (n+1), (Matrix.single i j r) v w) = if j = w then r else 0 := by
  by_cases h : j = w
  · subst w
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h]

lemma directed_transfer_column_sum {n : ℕ} (i j w : Fin (n+1)) (c : ℝ) :
    (∑ v : Fin (n+1),
      (c • (Matrix.single i j (1 : ℝ) - Matrix.single j j (1 : ℝ))) v w) = 0 := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_single_column, sub_self]

lemma edgeMatrix_column_sum {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (e : Fin n) (w : Fin (n+1)) :
    (∑ v : Fin (n+1), edgeMatrix t x e v w) = 0 := by
  simp only [edgeMatrix, Matrix.add_apply, Finset.sum_add_distrib]
  rw [directed_transfer_column_sum, directed_transfer_column_sum, add_zero]

/-- Exact columnwise water conservation, for every real rate vector. -/
theorem compartment_column_sum {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (w : Fin (n+1)) :
    (∑ v : Fin (n+1), compartmentMatrix t x v w) = if w = 0 then -x.1 0 else 0 := by
  simp only [compartmentMatrix, Matrix.sub_apply, Matrix.sum_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [edgeMatrix_column_sum, Finset.sum_const_zero, zero_sub,
    Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_single_column]
  by_cases h : w = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- The vector field induced by the actual compartment matrix conserves total
water except for the root discharge. This is a matrix identity, not an ODE premise. -/
theorem compartment_total_flux {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (s : VertexValues n) :
    (∑ v : Fin (n+1), (compartmentMatrix t x *ᵥ s) v) = -x.1 0 * s 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, compartment_column_sum]
  simp

lemma compartment_diagonal_edge {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (e : Fin n) (v : Fin (n+1)) :
    edgeMatrix t x e v v = -(if e.succ = v then x.1 e.succ else 0) -
      (if t.parent e = v then x.2 e else 0) := by
  have hp := parent_ne_child t e
  by_cases h1 : e.succ = v <;> by_cases h2 : t.parent e = v
  · exact False.elim (hp (h2.trans h1.symm))
  all_goals simp [edgeMatrix, Matrix.single_apply, h1, h2, eq_comm]

/-- The physical chart's d coordinate is the actual negative diagonal of A. -/
theorem compartment_diagonal {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v : Fin (n+1)) :
    compartmentMatrix t x v v = -(rateChart t x).1 v := by
  simp only [compartmentMatrix, Matrix.sub_apply, Matrix.sum_apply]
  simp_rw [compartment_diagonal_edge]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [rateChart]
  change -(∑ e : Fin n, if e.succ = v then x.1 e.succ else 0) -
      (∑ e : Fin n, if t.parent e = v then x.2 e else 0) -
      (x.1 0 • Matrix.single 0 0 (1 : ℝ)) v v = -(x.1 v + parentCLM t x.2 v)
  rw [parentCLM_apply]
  refine Fin.cases ?_ (fun i => ?_) v
  · simp [Matrix.single_apply, sub_eq_add_neg]
  · have hi : (0 : Fin (n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [Matrix.single_apply, hi, sub_eq_add_neg, add_comm]

/-- Every off-diagonal rate is nonnegative whenever the physical rates are. -/
theorem compartment_offdiag_nonneg {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ v, 0 ≤ x.1 v) (hf : ∀ e, 0 ≤ x.2 e)
    (v w : Fin (n+1)) (hvw : v ≠ w) : 0 ≤ compartmentMatrix t x v w := by
  have hz : ∀ i : Fin (n+1), (Matrix.single i i (1 : ℝ)) v w = 0 := by
    intro i
    by_cases hi : i = v
    · subst i
      simp [Matrix.single_apply, hvw, Ne.symm hvw]
    · simp [Matrix.single_apply, hi, Ne.symm hi]
  simp only [compartmentMatrix, edgeMatrix, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    hz, sub_zero, mul_zero]
  apply Finset.sum_nonneg
  intro e _
  apply add_nonneg
  · apply mul_nonneg (ha _)
    simp only [Matrix.single_apply]
    split <;> norm_num
  · apply mul_nonneg (hf _)
    simp only [Matrix.single_apply]
    split <;> norm_num

/-- Unreduced characteristic polynomial of the actual physical model. -/
def physicalCharacteristic {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ[X] :=
  (compartmentMatrix t x).charpoly

/-- Actual root-principal minor, with the original diagonals retained. -/
def physicalRootCofactor {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ[X] :=
  ((compartmentMatrix t x).submatrix Fin.succ Fin.succ).charpoly

end HydrologyTree
