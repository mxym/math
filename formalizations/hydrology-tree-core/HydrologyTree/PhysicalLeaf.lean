import HydrologyTree.PhysicalBridge
import HydrologyTree.LeafRecursion

/-! A genuine all-size characteristic recurrence for the existing physical
OrderedTree matrix. Leaf sparsity and every matrix-coordinate identification
are proved here, not imported as hypotheses. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

def terminalVertex (n : ℕ) : Fin (n+2) := (Fin.last n).succ

lemma parent_ne_terminal {n : ℕ} (t : OrderedTree (n+1)) (e : Fin (n+1)) :
    t.parent e ≠ terminalVertex n := by
  intro h
  have hp := t.parent_le e
  have he := e.isLt
  have hh := congrArg Fin.val h
  simp [terminalVertex] at hh
  omega

lemma succ_ne_terminal {n : ℕ} (e : Fin (n+1)) (he : e ≠ Fin.last n) :
    e.succ ≠ terminalVertex n := by
  intro h
  exact he (Fin.succ_injective _ h)

/-- The last numbered vertex has only its parent as a possible recipient. -/
theorem compartment_terminal_column {n : ℕ} (t : OrderedTree (n+1)) (x : TreeRates (n+1))
    (v : Fin (n+2)) (hv : v ≠ terminalVertex n) :
    compartmentMatrix t x v (terminalVertex n) =
      if v = t.parent (Fin.last n) then x.1 (terminalVertex n) else 0 := by
  rw [compartment_offdiag_formula t x _ _ hv]
  have hparent := parent_ne_terminal t
  simp only [hparent, and_false, ite_false, mul_zero, add_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [terminalVertex, eq_comm]
  · intro e _ he
    simp [succ_ne_terminal e he]
  · simp

/-- The last numbered vertex can receive water only from its parent. -/
theorem compartment_terminal_row {n : ℕ} (t : OrderedTree (n+1)) (x : TreeRates (n+1))
    (v : Fin (n+2)) (hv : v ≠ terminalVertex n) :
    compartmentMatrix t x (terminalVertex n) v =
      if v = t.parent (Fin.last n) then x.2 (Fin.last n) else 0 := by
  rw [compartment_offdiag_formula t x _ _ (Ne.symm hv)]
  have hparent := parent_ne_terminal t
  simp only [hparent, false_and, ite_false, mul_zero, zero_add]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [terminalVertex, eq_comm]
  · intro e _ he
    simp [succ_ne_terminal e he]
  · simp

lemma compartment_terminal_diagonal {n : ℕ} (t : OrderedTree (n+1)) (x : TreeRates (n+1)) :
    compartmentMatrix t x (terminalVertex n) (terminalVertex n) = -x.1 (terminalVertex n) := by
  rw [compartment_diagonal]
  change -(x.1 (terminalVertex n) + parentCLM t x.2 (terminalVertex n)) = _
  rw [parentCLM_apply]
  simp [parent_ne_terminal]

def terminalMinor {n : ℕ} (t : OrderedTree (n+1)) (x : TreeRates (n+1)) :=
  deletedMatrix (compartmentMatrix t x) (terminalVertex n)

/-- Full characteristic recurrence for every physical topologically numbered
tree with at least one edge, at all real rate vectors including zero rates.
The retained matrix is the actual principal minor with original diagonals. -/
theorem physicalCharacteristic_terminal_recursion {n : ℕ}
    (t : OrderedTree (n+1)) (x : TreeRates (n+1)) :
    physicalCharacteristic t x =
      (X + C (x.1 (terminalVertex n))) * (terminalMinor t x).charpoly -
      C (x.1 (terminalVertex n) * x.2 (Fin.last n)) *
        diagonalCofactor (terminalMinor t x)
          ⟨t.parent (Fin.last n), parent_ne_terminal t (Fin.last n)⟩ := by
  have hrow : ∀ v, v ≠ terminalVertex n →
      compartmentMatrix t x (terminalVertex n) v =
        if v = t.parent (Fin.last n) then
          compartmentMatrix t x (terminalVertex n) (t.parent (Fin.last n)) else 0 := by
    intro v hv
    rw [compartment_terminal_row t x v hv]
    simp only [terminalVertex, compartment_outward_entry]
  have hcol : ∀ v, v ≠ terminalVertex n →
      compartmentMatrix t x v (terminalVertex n) =
        if v = t.parent (Fin.last n) then
          compartmentMatrix t x (t.parent (Fin.last n)) (terminalVertex n) else 0 := by
    intro v hv
    rw [compartment_terminal_column t x v hv]
    simp only [terminalVertex, compartment_inward_entry]
  have h := charpoly_delete_leaf (compartmentMatrix t x) (terminalVertex n)
    (t.parent (Fin.last n)) (parent_ne_terminal t (Fin.last n)) hrow hcol
  rw [compartment_terminal_diagonal] at h
  simpa only [physicalCharacteristic, terminalMinor,
    terminalVertex, compartment_inward_entry, compartment_outward_entry,
    map_neg, sub_neg_eq_add] using h

end HydrologyTree
