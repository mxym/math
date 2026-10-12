import HydrologyTree.AllTreeResultant

/-! Full real-rate boundary distinction between response cancellation and
singularity of the unreduced coefficient map. No positivity assumption. -/
noncomputable section
namespace HydrologyTree

lemma resultantJacobianOrientation_ne_zero {n : ℕ} (t : OrderedTree n) :
    resultantJacobianOrientation t ≠ 0 := by
  rcases resultantJacobianOrientation_sign t with h | h <;> rw [h] <;> norm_num

/-- Exact cancellation-resultant zero set, including every zero outward rate. -/
theorem physicalResultant_zero_iff_all_rates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).resultant (physicalRootCofactor t x) = 0 ↔
      (∃ e : Fin n, x.2 e = 0) ∨ treeCanonicalJacobian t x = 0 := by
  rw [physicalResultant_eq_signed_jacobian,mul_eq_zero,mul_eq_zero]
  simp only [resultantJacobianOrientation_ne_zero, false_or,Finset.prod_eq_zero_iff,
    Finset.mem_univ,true_and]

/-- The actual unreduced characteristic/cofactor pair is coprime exactly when
all outward rates are nonzero AND the actual coefficient Jacobian is regular. -/
theorem physicalPair_coprime_iff_all_rates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    IsCoprime (physicalCharacteristic t x) (physicalRootCofactor t x) ↔
      (∀ e : Fin n, x.2 e ≠ 0) ∧ treeCanonicalJacobian t x ≠ 0 := by
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (physicalCharacteristic_monic t x),
    isUnit_iff_ne_zero]
  simpa only [not_or,not_exists,ne_eq] using not_congr (physicalResultant_zero_iff_all_rates t x)

/-- A vanishing outward edge causes actual polynomial cancellation even when
that edge is a leaf and its exponent in the coefficient Jacobian is zero. -/
theorem zero_outward_implies_not_coprime {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (e : Fin n) (he : x.2 e = 0) :
    ¬IsCoprime (physicalCharacteristic t x) (physicalRootCofactor t x) := by
  intro hc
  exact ((physicalPair_coprime_iff_all_rates t x).mp hc).1 e he

end HydrologyTree
