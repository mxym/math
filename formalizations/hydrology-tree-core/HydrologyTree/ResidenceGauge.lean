import HydrologyTree.MultiLeakSimplex

/-! Exact zero-frequency inverse transport and physical leakage shares.
The stationary inventory and conservation identities are actual matrix equations. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma residenceMatrix_gauge (B : Matrix V V ℝ) (hB : (-B).det ≠ 0)
    (h : V → ℝ) (hh : ∀ i, h i ≠ 0) :
    residenceMatrix (diagonalGauge h B)=diagonalGauge h (residenceMatrix B) := by
  have hDE : Matrix.diagonal h * Matrix.diagonal (fun i => (h i)⁻¹)=(1 : Matrix V V ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hh _)]
    exact Matrix.diagonal_one
  have hneg : -(diagonalGauge h B)=diagonalGauge h (-B) := by
    simp only [diagonalGauge,Matrix.mul_neg,Matrix.neg_mul]
  rw [residenceMatrix,hneg]
  exact similarity_inverse _ _ _ hDE (invDiagonal_mul_diagonal h hh) (isUnit_iff_ne_zero.mpr hB)

/-- Normalization at the observer and the strictly positive inverse column
remove every state-scale redundancy in the actual matrix parametrization. -/
theorem normalized_positive_gauge_injective (B : Matrix V V ℝ) (o : V)
    (hB : (-B).det ≠ 0) (hR : ∀ i, residenceMatrix B i o ≠ 0)
    (h k : V → ℝ) (hh : ∀ i, h i ≠ 0) (hk : ∀ i, k i ≠ 0)
    (ho : h o=1) (ko : k o=1) (he : diagonalGauge h B=diagonalGauge k B) : h=k := by
  have hi := congrArg residenceMatrix he
  rw [residenceMatrix_gauge B hB h hh,residenceMatrix_gauge B hB k hk] at hi
  funext i
  have hr := congrArg (fun M : Matrix V V ℝ => M i o) hi
  simp only [diagonalGauge_apply,ho,ko,inv_one,mul_one] at hr
  exact mul_right_cancel₀ (hR i) hr

/-- The actual unit-input stationary inventory is the inverse column. -/
theorem residenceColumn_stationary (B : Matrix V V ℝ) (o : V) (hB : (-B).det ≠ 0) :
    B *ᵥ (fun i => residenceMatrix B i o) + Pi.single o 1 = 0 := by
  have he := Matrix.mul_nonsing_inv (-B) (isUnit_iff_ne_zero.mpr hB)
  funext i
  have hi := congrArg (fun M : Matrix V V ℝ => M i o) he
  simp only [Matrix.mul_apply,Matrix.neg_apply,neg_mul,Finset.sum_neg_distrib,
    Matrix.one_apply] at hi
  simp only [Pi.add_apply,Pi.zero_apply,Matrix.mulVec,dotProduct,residenceMatrix,Pi.single_apply]
  by_cases h : i=o <;> simp_all <;> linarith

/-- Every actual output fraction equals its prescribed simplex coordinate.
The factor multiplying a leak is the actual stationary inventory, not a label. -/
theorem simplex_stationary_leak_fraction (B : Matrix V V ℝ) (o : V)
    (hB : (-B).det ≠ 0) (hR : ∀ i j, 0 < residenceMatrix B i j)
    (p : LeakSimplex V) (j : V) :
    let h := simplexGauge (residenceMatrix B) o p.val
    let A := diagonalGauge h B
    matrixLeak A j * residenceMatrix A j o = p.val j := by
  dsimp only
  rw [simplexGauge_actual_leak B o hB,
    residenceMatrix_gauge B hB _ (fun i => ne_of_gt (simplexGauge_pos _ o hR p i)),
    diagonalGauge_apply,simplexGauge_root _ o hR p,inv_one,mul_one]
  field_simp [ne_of_gt (hR j o),ne_of_gt (simplexGauge_pos _ o hR p j)]
  <;> ring

/-- A zero leak is exactly a zero simplex share, including all boundary faces. -/
theorem simplex_leak_zero_iff (B : Matrix V V ℝ) (o : V)
    (hB : (-B).det ≠ 0) (hR : ∀ i j, 0 < residenceMatrix B i j)
    (p : LeakSimplex V) (j : V) :
    matrixLeak (diagonalGauge (simplexGauge (residenceMatrix B) o p.val) B) j=0 ↔ p.val j=0 := by
  rw [simplexGauge_actual_leak B o hB,div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero (ne_of_gt (hR j o)) (ne_of_gt (simplexGauge_pos _ o hR p j)))

end HydrologyTree
