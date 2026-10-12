import HydrologyTree.PhysicalRecursion
import HydrologyTree.CouplingSemantics

/-! Exact zero-frequency determinant and cofactor formulas of the original
physical tree matrix. Valid at all real rates, including zero-rate boundaries;
no steady-state, stability or noncancellation premise is inserted. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Conservation forces the full characteristic constant to be the root leak
 times its original root cofactor constant. No divisions by edge rates occur. -/
theorem physicalCharacteristic_eval_zero_leak {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).eval 0 = x.1 0 * (physicalRootCofactor t x).eval 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc (c : RootChild t) :
        (childCharacteristic t x c).eval 0 = x.1 c.val * (childCofactor t x c).eval 0 := by
      have h := ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) (childRates t c x)
      simpa only [childCharacteristic, childCofactor, childRates_leak] using h
    rw [physicalCharacteristic_child_recursion, physicalRootCofactor_child_product]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add, Polynomial.eval_prod, Polynomial.eval_finset_sum]
    have hterm (c : RootChild t) :
        (x.1 c.val * outwardByVertex x.2 c.val) * (childCofactor t x c).eval 0 *
          (∏ j ∈ Finset.univ.erase c, (childCharacteristic t x j).eval 0) =
        outwardByVertex x.2 c.val * ∏ j : RootChild t, (childCharacteristic t x j).eval 0 := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => (childCharacteristic t x j).eval 0)
        (Finset.mem_univ c), hc c]
      ring
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    change (x.1 0 + parentCLM t x.2 0) * _ - _ = _
    rw [rootConnectors_sum]
    ring

/-- Each inward coordinate appears exactly once in the physical child partition. -/
lemma child_inward_product {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (∏ c : RootChild t, ∏ i : Fin (childEdgeCount t c+1), (childRates t c x).1 i) =
      ∏ e : Fin n, x.1 e.succ := by
  change (∏ c : RootChild t, ∏ i : Fin (childEdgeCount t c+1),
    x.1 (childEnumeration t c i).val) = _
  rw [← Fintype.prod_sigma (f := fun z : NumberedChildNodes t =>
    x.1 (childEnumeration t z.1 z.2).val)]
  apply Fintype.prod_equiv (numberedEdgeEquiv t)
  intro z
  change x.1 (childEnumeration t z.1 z.2).val = x.1 (numberedEdgeIndex t z).succ
  rw [numberedEdgeIndex_succ]

/-- The actual root principal cofactor constant is the product of all inward
rates. In particular this identity remains valid when one or more rates vanish. -/
theorem physicalRootCofactor_eval_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalRootCofactor t x).eval 0 = ∏ e : Fin n, x.1 e.succ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [physicalRootCofactor_child_product, Polynomial.eval_prod, ← child_inward_product t x]
    apply Finset.prod_congr rfl
    intro c _
    rw [childCharacteristic, physicalCharacteristic_eval_zero_leak,
      ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) (childRates t c x),
      Fin.prod_univ_succ]

/-- Exact all-tree characteristic constant, at arbitrary real physical rates. -/
theorem physicalCharacteristic_eval_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).eval 0 = x.1 0 * ∏ e : Fin n, x.1 e.succ := by
  rw [physicalCharacteristic_eval_zero_leak, physicalRootCofactor_eval_zero]

/-- Exact noncancellation at zero requires only nonzero inward rates. -/
theorem physicalRootCofactor_eval_zero_ne_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) : (physicalRootCofactor t x).eval 0 ≠ 0 := by
  rw [physicalRootCofactor_eval_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => ha e)

/-- Positive inward rates yield a strictly positive cofactor constant, independently
of the outward rates and the root leak. -/
theorem physicalRootCofactor_eval_zero_pos {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) : 0 < (physicalRootCofactor t x).eval 0 := by
  rw [physicalRootCofactor_eval_zero]
  exact Finset.prod_pos (fun e _ => ha e)

/-- The root leak is an actual coefficient invariant on the nonzero-inward domain. -/
theorem physical_root_leak_eq_ratio {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, x.1 e.succ ≠ 0) :
    x.1 0 = (physicalCharacteristic t x).eval 0 / (physicalRootCofactor t x).eval 0 := by
  rw [physicalCharacteristic_eval_zero_leak]
  exact (mul_div_cancel_right₀ _ (physicalRootCofactor_eval_zero_ne_zero t x ha)).symm

end HydrologyTree
