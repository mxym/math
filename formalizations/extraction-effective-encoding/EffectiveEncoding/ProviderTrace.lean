import EffectiveEncoding.ProviderTraceCore

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

theorem extraction_trace_subtree_polynomial {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (e : ScalarExpression) (hmem : e∈(cachedArithmeticRun (fun j => dyadicQuaternionOracle (entry j))
      inverseLabel table L (extractionPrecision k p) u.quaternionOracle).expressions) :
    e.IntegerSubtreeBound (extractionOperandPolynomial n L k p) := by
  apply ScalarExpression.integerSubtreeBound
  have h := (List.le_sum_of_mem (List.mem_map.mpr ⟨e,hmem,rfl⟩)).trans
    (actualDescriptorTrace_polynomial entry G he inverseLabel table L (extractionPrecision k p) hL hu)
  have hp : (extractionPrecision k p+1)^137≤(pipelinePrecisionPolynomial k p+1)^137 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (extractionPrecision_polynomial k p) 1) 137
  exact (h.trans (Nat.mul_le_mul_left _ hp)).trans (Nat.le_add_right _ _)


end EffectiveEncoding
