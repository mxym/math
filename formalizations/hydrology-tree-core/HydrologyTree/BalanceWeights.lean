import HydrologyTree.MatrixEntries

/-! Constructed detailed-balance weights of the actual finite physical tree.
These weights are not added as an existence hypothesis. -/
open Matrix
noncomputable section
namespace HydrologyTree

def balanceWeight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (v : Fin (n+1)) : ℝ :=
  if hv : v = 0 then 1 else
    balanceWeight t x (parentVertex t v) * outwardByVertex x.2 v / x.1 v
termination_by v.val
decreasing_by exact parentVertex_lt t v hv

@[simp] theorem balanceWeight_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    balanceWeight t x 0 = 1 := by
  rw [balanceWeight]
  simp

lemma balanceWeight_succ {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (e : Fin n) :
    balanceWeight t x e.succ = balanceWeight t x (t.parent e) * x.2 e / x.1 e.succ := by
  rw [balanceWeight]
  simp only [Fin.succ_ne_zero, dite_false]
  rfl

/-- Every constructed weight is strictly positive for positive internal rates;
the root leak need not be positive or nonzero. -/
theorem balanceWeight_pos {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (v : Fin (n+1)) : 0 < balanceWeight t x v := by
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hv : v = 0
    · subst v
      rw [balanceWeight_zero]
      norm_num
    · let e : Fin n := v.pred hv
      have he : e.succ = v := Fin.succ_pred v hv
      have hlt : (t.parent e).val < v.val := by
        rw [← he]
        exact Nat.lt_succ_of_le (t.parent_le e)
      rw [← he, balanceWeight_succ]
      exact div_pos (mul_pos (ih (t.parent e) hlt) (hf e)) (ha e)

/-- Exact opposed-edge detailed balance, supplied by the construction. -/
theorem balanceWeight_edge {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) (e : Fin n) :
    x.1 e.succ * balanceWeight t x e.succ = x.2 e * balanceWeight t x (t.parent e) := by
  rw [balanceWeight_succ]
  field_simp [ha e]
  <;> ring

end HydrologyTree
