import ConcreteNativeExtraction.Program

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
open RationalGateInterface RationalGateBinary EffectiveEncoding

namespace ConcreteNativeExtraction

def gateHeightCoefficient (L : ℕ) : ℕ := 51200000 * (L + 1) + 1

/-- Height of every actual eager library query, derived from the concrete
binary program and the internally proved cache-precision demand. -/
theorem queried_gate_height (L q : ℕ) (i : Fin 4) (r : ℕ)
    (hr : r ≤ numericalDemand L (Nat.clog 2 (q + 1))) :
    IntegerPacketHeight (nativeEntry i r).decode
      (gateHeightCoefficient L * (q + 1)^9) := by
  apply IntegerPacketHeight.mono _ _ _ (nativeEntry_height i r)
  have hd := numericalDemand_precision_bound L q
  have hx : 1 ≤ (q + 1)^9 := Nat.one_le_pow _ _ (by omega)
  calc
    r + 1 ≤ cachePrecisionBudget L q + 1 :=
      Nat.add_le_add_right (hr.trans hd) 1
    _ ≤ gateHeightCoefficient L * (q + 1)^9 := by
      unfold cachePrecisionBudget gateHeightCoefficient
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left hx _

/-- Bound for the precisely retained rank-bit, literal-preparation,
target-provider and online numerical primitive traces. Fixed-library
emission/normalization and whole structural/control machine time remain
outside this inherited counter. -/
def primitiveBound (net : OfflineNet) (k p : ℕ) : ℕ :=
  306*k*(k+4)^9 + actualGatePolynomial k *
    (200*(4*k+2)^2 + nativeProviderCachePolynomialConstant net.lengthBound*(k+3)^15 +
      actualNativeBooleanCoefficient net.lastIndex net.lengthBound k
        (gateHeightCoefficient net.lengthBound)) * (logarithmicPrecision k p+1)^338

theorem run_accounted_actions (net : OfflineNet) (k p : ℕ) :
    (run net k p).accountedPrimitiveActions ≤ primitiveBound net k p := by
  exact binaryNativeExtractionRun_accountedPrimitiveActions nativeEntry inverseLabel
    net.table net.lengthBound k p (gateHeightCoefficient net.lengthBound) net.lengths
      (fun i r hr => queried_gate_height net.lengthBound (extractionPrecision k p) i r hr)

/-- A single fixed offline table works for all k, all accuracies, and all
unknown unit input vectors. No oracle, density or queried-height premise is
left to a caller. The resource conclusion is the specified partial counter. -/
theorem concrete_compiler_exists :
    ∃ net : OfflineNet,
      (∀ (k p : ℕ) (z : Fin 4 → ℂ), IsUnitVector z →
        1 - (1/2 : ℝ)^p ≤
          (Extraction.bellProjector (d := Bits (bellPairYield k)) *
            approximateExtractionOutput k (denote (labelCircuit rationalGate
              (run net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re) ∧
      (∀ k p : ℕ, (run net k p).accountedPrimitiveActions ≤ primitiveBound net k p) ∧
      (∀ k p : ℕ, (run net k p).compilation.word.length ≤ actualGatePolynomial k *
        (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5)) ∧
      (∀ k p : ℕ, ∀ g ∈ labelCircuit rationalGate (run net k p).compilation.word,
        usesFiniteLibrary rationalGate g) := by
  obtain ⟨net⟩ := offlineNet_exists
  exact ⟨net, run_fidelity net, run_accounted_actions net,
    run_length net, run_uses_finite_library net⟩

end ConcreteNativeExtraction
