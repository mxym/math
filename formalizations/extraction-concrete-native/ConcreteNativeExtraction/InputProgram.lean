import ConcreteNativeExtraction.Resources
import EffectiveEncoding.FullyInputNativeExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
open RationalGateInterface RationalGateBinary EffectiveEncoding

namespace ConcreteNativeExtraction

/-- Successor execution: actual cached input references retain both numerical
and cache-read traces. The earlier run remains unchanged as a fixed endpoint. -/
def inputRun (net : OfflineNet) (k p : ℕ) :
    FullyInputNativeResult 4 (originalWireCount k) net.lengthBound :=
  fullyInputNativeRun nativeEntry inverseLabel net.table net.lengthBound k p

theorem inputRun_word (net : OfflineNet) (k p : ℕ) :
    (inputRun net k p).compilation.word =
      numericalExtractionCode (fun i => nativePacketDataOracle (nativeEntry i))
        inverseLabel net.table net.lengthBound k p := by
  exact fullyInputNativeRun_word nativeEntry inverseLabel net.table
    net.lengthBound k p net.lengths

/-- Output compatibility transports physical specifications, never costs
from a different execution. The new cost theorem below uses the new record. -/
theorem inputRun_word_eq_run (net : OfflineNet) (k p : ℕ) :
    (inputRun net k p).compilation.word = (run net k p).compilation.word := by
  rw [inputRun_word, run_word]

theorem inputRun_uses_finite_library (net : OfflineNet) (k p : ℕ) :
    ∀ g ∈ labelCircuit rationalGate (inputRun net k p).compilation.word,
      usesFiniteLibrary rationalGate g := by
  rw [inputRun_word_eq_run]
  exact run_uses_finite_library net k p

theorem inputRun_length (net : OfflineNet) (k p : ℕ) :
    (inputRun net k p).compilation.word.length ≤ actualGatePolynomial k *
      (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5) := by
  rw [inputRun_word_eq_run]
  exact run_length net k p

theorem inputRun_fidelity (net : OfflineNet) (k p : ℕ) (z : Fin 4 → ℂ)
    (hz : IsUnitVector z) :
    1 - (1/2 : ℝ)^p ≤ (Extraction.bellProjector (d := Bits (bellPairYield k)) *
      approximateExtractionOutput k (denote (labelCircuit rationalGate
        (inputRun net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re := by
  rw [inputRun_word_eq_run]
  exact run_fidelity net k p z hz

def inputPrimitiveBound (net : OfflineNet) (k p : ℕ) : ℕ :=
  306*k*(k+4)^9 + actualGatePolynomial k *
    (200*(4*k+2)^2 + nativeProviderCachePolynomialConstant net.lengthBound*(k+3)^15 +
      actualInputOnlineCoefficient 4 net.lastIndex net.lengthBound k
        (gateHeightCoefficient net.lengthBound)) * (logarithmicPrecision k p+1)^338

/-- The bound is applied directly to FullyInputNativeRun's actual retained
records. Numeric338 and read73 belong to this same execution, not the earlier
native-only run that merely emits the same output word. -/
theorem inputRun_accounted_actions (net : OfflineNet) (k p : ℕ) :
    (inputRun net k p).accountedPrimitiveActions ≤ inputPrimitiveBound net k p := by
  exact fullyInputNativeRun_accountedPrimitiveActions nativeEntry inverseLabel
    net.table net.lengthBound k p (gateHeightCoefficient net.lengthBound) net.lengths
      (fun i r hr => queried_gate_height net.lengthBound (extractionPrecision k p) i r hr)

theorem concrete_input_compiler_exists :
    ∃ net : OfflineNet,
      (∀ (k p : ℕ) (z : Fin 4 → ℂ), IsUnitVector z →
        1 - (1/2 : ℝ)^p ≤
          (Extraction.bellProjector (d := Bits (bellPairYield k)) *
            approximateExtractionOutput k (denote (labelCircuit rationalGate
              (inputRun net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re) ∧
      (∀ k p : ℕ, (inputRun net k p).accountedPrimitiveActions ≤ inputPrimitiveBound net k p) ∧
      (∀ k p : ℕ, (inputRun net k p).compilation.word.length ≤ actualGatePolynomial k *
        (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5)) ∧
      (∀ k p : ℕ, ∀ g ∈ labelCircuit rationalGate (inputRun net k p).compilation.word,
        usesFiniteLibrary rationalGate g) := by
  obtain ⟨net⟩ := offlineNet_exists
  exact ⟨net, inputRun_fidelity net, inputRun_accounted_actions net,
    inputRun_length net, inputRun_uses_finite_library net⟩

end ConcreteNativeExtraction
