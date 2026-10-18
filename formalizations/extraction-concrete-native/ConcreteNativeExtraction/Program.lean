import EffectiveEncoding.BinaryNativeExtraction
import RationalGateBinary.Provider
import RationalGateUniversality.Density

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
open RationalGateInterface RationalGateBinary EffectiveEncoding

namespace ConcreteNativeExtraction

/-- One fixed finite offline table for the actual four-gate alphabet. The
coverage fields are erased proofs; the program stores only finite data.
Existence does not bound discovering the table or its fixed size. -/
structure OfflineNet where
  lengthBound : ℕ
  lastIndex : ℕ
  table : Fin (lastIndex + 1) → List (Fin 4)
  lengths : ∀ j, (table j).length ≤ lengthBound
  covers : ∀ U : SU2, ∃ j, unitaryDistance (su2AsUnitary U)
    (su2AsUnitary (instructionWordValue rationalGate (table j))) ≤ 1/576

theorem offlineNet_exists : Nonempty OfflineNet := by
  obtain ⟨L, n, table, hL, hcover⟩ := RationalGateUniversality.rationalGate_precomputedNet
  exact ⟨⟨L, n, table, hL, hcover⟩⟩

/-- Actual native extraction with the concrete bit provider. No correctness,
universality, or library-height certificate is supplied to this program. -/
def run (net : OfflineNet) (k p : ℕ) :
    BinaryNativeExtractionResult 4 (originalWireCount k) net.lengthBound :=
  binaryNativeExtractionRun nativeEntry inverseLabel net.table net.lengthBound k p

theorem run_word (net : OfflineNet) (k p : ℕ) :
    (run net k p).compilation.word =
      numericalExtractionCode (fun i => nativePacketDataOracle (nativeEntry i))
        inverseLabel net.table net.lengthBound k p := by
  exact binaryNativeExtractionRun_word nativeEntry inverseLabel net.table
    net.lengthBound k p net.lengths

theorem run_uses_finite_library (net : OfflineNet) (k p : ℕ) :
    ∀ g ∈ labelCircuit rationalGate (run net k p).compilation.word,
      usesFiniteLibrary rationalGate g := by
  rw [run_word]
  exact numericalExtractionCode_uses rationalGate _ inverseLabel net.table net.lengthBound k p

/-- Polynomial output-gate count with the actual logarithmic global error
budget. This is an output-length assertion, separate from classical time. -/
theorem run_length (net : OfflineNet) (k p : ℕ) :
    (run net k p).compilation.word.length ≤ actualGatePolynomial k *
      (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5) := by
  rw [run_word]
  apply (numericalExtractionCode_length rationalGate _ nativeEntry_correct
    inverseLabel rationalGate_inverse net.table net.lengthBound net.lengths net.covers k p).trans
  exact Nat.mul_le_mul (extractionCode_length_polynomial k)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 5))

/-- The original physical discard/Bell test on all unknown pure inputs,
on the original 2k wires. No caller gate-approximation assumption remains. -/
theorem run_fidelity (net : OfflineNet) (k p : ℕ) (z : Fin 4 → ℂ)
    (hz : IsUnitVector z) :
    1 - (1/2 : ℝ)^p ≤ (Extraction.bellProjector (d := Bits (bellPairYield k)) *
      approximateExtractionOutput k (denote (labelCircuit rationalGate
        (run net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re := by
  exact binaryNativeExtractionRun_fidelity rationalGate nativeEntry nativeEntry_correct
    inverseLabel rationalGate_inverse net.table net.lengthBound net.lengths net.covers k p z hz

end ConcreteNativeExtraction
