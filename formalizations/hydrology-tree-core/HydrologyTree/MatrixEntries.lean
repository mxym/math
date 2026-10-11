import HydrologyTree.PhysicalBridge

/-! Pointwise formulas for actual physical transfer entries, including the root.
No invertibility, positivity or nonzero transfer rate is assumed. -/
open Matrix
noncomputable section
namespace HydrologyTree

/-- Extend edge data to vertices by assigning zero to the original root. -/
def outwardByVertex {n : ℕ} (f : EdgeValues n) : VertexValues n := Fin.cases 0 f

@[simp] lemma outwardByVertex_zero {n : ℕ} (f : EdgeValues n) : outwardByVertex f 0 = 0 := rfl
@[simp] lemma outwardByVertex_succ {n : ℕ} (f : EdgeValues n) (i : Fin n) :
    outwardByVertex f i.succ = f i := rfl

lemma sum_inward_transfer {n : ℕ} (t : OrderedTree n) (a : VertexValues n)
    (v w : Fin (n+1)) :
    (∑ e : Fin n, a e.succ * (if t.parent e = v ∧ e.succ = w then 1 else 0)) =
      if w = 0 then 0 else if parentVertex t w = v then a w else 0 := by
  refine Fin.cases ?_ (fun i => ?_) w
  · simp [Fin.succ_ne_zero]
  · rw [Finset.sum_eq_single i]
    · simp [parentVertex, mul_ite] <;> rfl
    · intro j _ hji
      have hs : j.succ ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
      simp [hs]
    · simp

lemma sum_outward_transfer {n : ℕ} (t : OrderedTree n) (f : EdgeValues n)
    (v w : Fin (n+1)) :
    (∑ e : Fin n, f e * (if e.succ = v ∧ t.parent e = w then 1 else 0)) =
      if v = 0 then 0 else if parentVertex t v = w then outwardByVertex f v else 0 := by
  refine Fin.cases ?_ (fun i => ?_) v
  · simp [Fin.succ_ne_zero]
  · rw [Finset.sum_eq_single i]
    · simp [parentVertex, mul_ite] <;> rfl
    · intro j _ hji
      have hs : j.succ ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
      simp [hs]
    · simp

/-- Only the two directed edges relating a vertex and its parent contribute. -/
theorem compartment_offdiag_parent_formula {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v w : Fin (n+1)) (hvw : v ≠ w) :
    compartmentMatrix t x v w =
      (if w = 0 then 0 else if parentVertex t w = v then x.1 w else 0) +
      (if v = 0 then 0 else if parentVertex t v = w then outwardByVertex x.2 v else 0) := by
  rw [compartment_offdiag_formula t x v w hvw, Finset.sum_add_distrib,
    sum_inward_transfer, sum_outward_transfer]

end HydrologyTree
