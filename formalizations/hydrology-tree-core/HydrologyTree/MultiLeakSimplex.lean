import HydrologyTree.DiagonalGauge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Positivity

/-! A simplex of actual nonnegative column losses inside an invertible diagonal
similarity class. The matrix inverse and every physical column sum are explicit;
there is no assumed simplex-classification or inverse-recovery conclusion. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual external loss at a vertex, directly from the matrix column sum. -/
def matrixLeak (A : Matrix V V ℝ) (j : V) : ℝ := -(∑ i, A i j)

/-- The actual zero-frequency residence matrix. -/
def residenceMatrix (B : Matrix V V ℝ) : Matrix V V ℝ := (-B)⁻¹

/-- Nonnegative loss fractions summing to one; zero fractions are retained. -/
abbrev LeakSimplex (V : Type*) [Fintype V] :=
  {p : V → ℝ // (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1}

def simplexLossWeight (R : Matrix V V ℝ) (o : V) (p : V → ℝ) : V → ℝ :=
  fun i => p i / R i o

def simplexGauge (R : Matrix V V ℝ) (o : V) (p : V → ℝ) : V → ℝ :=
  (simplexLossWeight R o p) ᵥ* R

lemma matrixLeak_diagonalGauge (B : Matrix V V ℝ) (h : V → ℝ) (j : V) :
    matrixLeak (diagonalGauge h B) j = (h ᵥ* (-B)) j / h j := by
  simp only [matrixLeak,diagonalGauge_apply,Matrix.vecMul,dotProduct,
    Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib,div_eq_mul_inv,← Finset.sum_mul,neg_mul]

lemma simplexGauge_root (R : Matrix V V ℝ) (o : V) (hR : ∀ i j, 0 < R i j)
    (p : LeakSimplex V) : simplexGauge R o p.val o=1 := by
  simp only [simplexGauge,simplexLossWeight,Matrix.vecMul,dotProduct,
    div_mul_cancel₀ _ (ne_of_gt (hR _ _))]
  exact p.property.2

lemma simplexGauge_pos (R : Matrix V V ℝ) (o : V) (hR : ∀ i j, 0 < R i j)
    (p : LeakSimplex V) (j : V) : 0 < simplexGauge R o p.val j := by
  have hex : ∃ i, 0 < p.val i := by
    by_contra hn
    have hz : ∀ i, p.val i=0 := by
      intro i
      have hi : ¬0<p.val i := fun h => hn ⟨i,h⟩
      exact le_antisymm (le_of_not_gt hi) (p.property.1 i)
    have hm := p.property.2
    simp only [hz,Finset.sum_const_zero] at hm
    norm_num at hm
  obtain ⟨i,hi⟩ := hex
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (div_nonneg (p.property.1 k) (le_of_lt (hR k o))) (le_of_lt (hR k j))
  · exact ⟨i,Finset.mem_univ i,mul_pos (div_pos hi (hR i o)) (hR i j)⟩

lemma simplexGauge_weighted_loss (B : Matrix V V ℝ) (o : V)
    (hB : (-B).det ≠ 0) (p : V → ℝ) :
    (simplexGauge (residenceMatrix B) o p) ᵥ* (-B) = simplexLossWeight (residenceMatrix B) o p := by
  rw [simplexGauge,vecMul_vecMul,residenceMatrix,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),vecMul_one]

/-- The actual external loss formula, including vanishing shares on simplex faces. -/
theorem simplexGauge_actual_leak (B : Matrix V V ℝ) (o : V)
    (hB : (-B).det ≠ 0) (p : V → ℝ) (j : V) :
    matrixLeak (diagonalGauge (simplexGauge (residenceMatrix B) o p) B) j =
      p j / (residenceMatrix B j o * simplexGauge (residenceMatrix B) o p j) := by
  rw [matrixLeak_diagonalGauge,simplexGauge_weighted_loss B o hB p]
  exact div_div _ _ _

/-- Positive normalized state scales for which the ACTUAL transformed matrix
has nonnegative external losses. No target simplex classification is assumed. -/
abbrev NonnegativeLeakGauge (B : Matrix V V ℝ) (o : V) :=
  {h : V → ℝ // (∀ i, 0 < h i) ∧ h o=1 ∧ ∀ j, 0 ≤ matrixLeak (diagonalGauge h B) j}

/-- Every simplex point yields an actual nonnegative-leak gauge. -/
def simplexToLeakGauge (B : Matrix V V ℝ) (o : V) (hB : (-B).det ≠ 0)
    (hR : ∀ i j, 0 < residenceMatrix B i j) (p : LeakSimplex V) : NonnegativeLeakGauge B o :=
  ⟨simplexGauge (residenceMatrix B) o p.val,
    simplexGauge_pos _ o hR p,simplexGauge_root _ o hR p,fun j => by
      rw [simplexGauge_actual_leak B o hB]
      exact div_nonneg (p.property.1 j)
        (le_of_lt (mul_pos (hR j o) (simplexGauge_pos _ o hR p j)))⟩

lemma leakGauge_weighted_nonneg (B : Matrix V V ℝ) (o : V)
    (h : NonnegativeLeakGauge B o) (j : V) : 0 ≤ (h.val ᵥ* (-B)) j := by
  have he := h.property.2.2 j
  rw [matrixLeak_diagonalGauge] at he
  have hm := mul_nonneg he (le_of_lt (h.property.1 j))
  simpa only [div_mul_cancel₀ _ (ne_of_gt (h.property.1 j))] using hm

lemma leakGauge_inverse_recovery (B : Matrix V V ℝ) (hB : (-B).det ≠ 0)
    (h : V → ℝ) : (h ᵥ* (-B)) ᵥ* residenceMatrix B=h := by
  rw [vecMul_vecMul,residenceMatrix,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),vecMul_one]

/-- Extract actual outgoing shares; invertibility proves their normalization. -/
def leakGaugeToSimplex (B : Matrix V V ℝ) (o : V) (hB : (-B).det ≠ 0)
    (hR : ∀ i j, 0 < residenceMatrix B i j) (h : NonnegativeLeakGauge B o) : LeakSimplex V :=
  ⟨fun j => (h.val ᵥ* (-B)) j * residenceMatrix B j o,
    fun j => mul_nonneg (leakGauge_weighted_nonneg B o h j) (le_of_lt (hR j o)),by
      change ((h.val ᵥ* (-B)) ᵥ* residenceMatrix B) o=1
      rw [leakGauge_inverse_recovery B hB]
      exact h.property.2.1⟩

/-- Complete simplex/gauge equivalence: both maps use actual matrix arithmetic,
and both inverse identities are proved, not exposed as hypotheses. -/
def leakSimplexEquivGauge (B : Matrix V V ℝ) (o : V) (hB : (-B).det ≠ 0)
    (hR : ∀ i j, 0 < residenceMatrix B i j) : LeakSimplex V ≃ NonnegativeLeakGauge B o where
  toFun := simplexToLeakGauge B o hB hR
  invFun := leakGaugeToSimplex B o hB hR
  left_inv p := by
    apply Subtype.ext
    funext j
    change (simplexGauge (residenceMatrix B) o p.val ᵥ* (-B)) j * residenceMatrix B j o=p.val j
    rw [simplexGauge_weighted_loss B o hB]
    exact div_mul_cancel₀ _ (ne_of_gt (hR j o))
  right_inv h := by
    apply Subtype.ext
    change simplexGauge (residenceMatrix B) o (fun j => (h.val ᵥ* (-B)) j * residenceMatrix B j o)=h.val
    have he : simplexLossWeight (residenceMatrix B) o
        (fun j => (h.val ᵥ* (-B)) j * residenceMatrix B j o)=h.val ᵥ* (-B) := by
      funext j
      exact mul_div_cancel_right₀ _ (ne_of_gt (hR j o))
    rw [simplexGauge,he,leakGauge_inverse_recovery B hB]

end HydrologyTree
