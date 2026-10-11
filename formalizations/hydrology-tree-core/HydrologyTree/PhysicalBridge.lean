import HydrologyTree.CompartmentMatrix

/-! Identification of the rate-coordinate Jacobian with coordinates extracted
from the actual compartment matrix, rather than a surrogate parameter map. -/
open Matrix Module
noncomputable section
namespace HydrologyTree

lemma no_reversed_tree_edges {n : ℕ} (t : OrderedTree n) (i j : Fin n) :
    ¬(j.succ = t.parent i ∧ t.parent j = i.succ) := by
  rintro ⟨h1,h2⟩
  have hpi := t.parent_le i
  have hpj := t.parent_le j
  have h1v := congrArg Fin.val h1
  have h2v := congrArg Fin.val h2
  simp only [Fin.val_succ] at h1v h2v
  omega

lemma single_diagonal_offdiag {n : ℕ} (v w i : Fin (n+1)) (hvw : v ≠ w) :
    (Matrix.single i i (1 : ℝ)) v w = 0 := by
  apply Matrix.single_apply_of_ne
  rintro ⟨hi,hj⟩
  exact hvw (hi.symm.trans hj)

lemma compartment_offdiag_formula {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v w : Fin (n+1)) (hvw : v ≠ w) :
    compartmentMatrix t x v w =
      ∑ e : Fin n, (x.1 e.succ * (if t.parent e = v ∧ e.succ = w then 1 else 0) +
        x.2 e * (if e.succ = v ∧ t.parent e = w then 1 else 0)) := by
  simp only [compartmentMatrix, edgeMatrix, Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, single_diagonal_offdiag v w _ hvw,
    mul_zero, sub_zero, Matrix.single_apply]

/-- The entry toward the parent is exactly its physical inward rate. -/
theorem compartment_inward_entry {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (i : Fin n) :
    compartmentMatrix t x (t.parent i) i.succ = x.1 i.succ := by
  rw [compartment_offdiag_formula t x _ _ (parent_ne_child t i), Finset.sum_eq_single i]
  · simp [parent_ne_child t i, Ne.symm (parent_ne_child t i)]
  · intro j _ hji
    have hs : j.succ ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
    simp [hs, no_reversed_tree_edges t i j]
  · simp

/-- The entry away from the parent is exactly its physical outward rate. -/
theorem compartment_outward_entry {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (i : Fin n) :
    compartmentMatrix t x i.succ (t.parent i) = x.2 i := by
  rw [compartment_offdiag_formula t x _ _ (Ne.symm (parent_ne_child t i)),
    Finset.sum_eq_single i]
  · simp [parent_ne_child t i, Ne.symm (parent_ne_child t i)]
  · intro j _ hji
    have hs : j.succ ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
    have hr : ¬(t.parent j = i.succ ∧ j.succ = t.parent i) := by
      rintro ⟨h1,h2⟩
      exact no_reversed_tree_edges t i j ⟨h2,h1⟩
    simp [hs,hr]
  · simp

/-- Diagonal and edge-product coordinates read from the actual matrix. -/
def matrixRateCoordinates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : TreeRates n :=
  (fun v => -compartmentMatrix t x v v,
    fun i => compartmentMatrix t x (t.parent i) i.succ *
      compartmentMatrix t x i.succ (t.parent i))

/-- No physical-coordinate identification is left as an assumption. -/
theorem matrixRateCoordinates_eq {n : ℕ} (t : OrderedTree n) :
    matrixRateCoordinates t = rateChart t := by
  funext x
  apply Prod.ext
  · funext v
    simp [matrixRateCoordinates, compartment_diagonal]
  · funext i
    simp [matrixRateCoordinates, compartment_inward_entry, compartment_outward_entry, rateChart]

theorem hasFDerivAt_matrixRateCoordinates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    HasFDerivAt (matrixRateCoordinates t) (rateChartDerivative t x) x := by
  rw [matrixRateCoordinates_eq]
  exact hasFDerivAt_rateChart t x

def matrixCoordinateJacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  (LinearMap.toMatrix ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
    ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
    (fderiv ℝ (matrixRateCoordinates t) x).toLinearMap).det

/-- Actual matrix-coordinate Jacobian, all finite topologically numbered trees,
all real rates, including zero-rate degenerations and the one-vertex case. -/
theorem matrixCoordinateJacobian_eq {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    matrixCoordinateJacobian t x = ∏ i : Fin n, x.1 i.succ := by
  rw [matrixCoordinateJacobian, (hasFDerivAt_matrixRateCoordinates t x).fderiv,
    det_rateChartDerivative]

/-- The parent function fixes the root and follows the unique inward edge elsewhere. -/
def parentVertex {n : ℕ} (t : OrderedTree n) : Fin (n+1) → Fin (n+1) :=
  Fin.cases 0 t.parent

lemma parentVertex_lt {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) (hv : v ≠ 0) :
    (parentVertex t v).val < v.val := by
  revert hv
  refine Fin.cases ?_ (fun i _ => ?_) v
  · intro h
    exact False.elim (h rfl)
  · exact Nat.lt_succ_of_le (t.parent_le i)

/-- The parent encoding really is connected to the root: no disconnected
component or directed cycle can enter the theorem through its hypotheses. -/
theorem parent_reaches_root {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) :
    ∃ k : ℕ, (parentVertex t)^[k] v = 0 := by
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hv : v = 0
    · exact ⟨0, by simpa using hv⟩
    · obtain ⟨k,hk⟩ := ih (parentVertex t v) (parentVertex_lt t v hv)
      refine ⟨k+1, ?_⟩
      simpa only [Function.iterate_succ_apply] using hk

end HydrologyTree
