import ConcreteNativeExtraction.InputProgram
import EffectiveEncoding.FullyAssembledInputExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
open RationalGateInterface RationalGateBinary EffectiveEncoding

namespace ConcreteNativeExtraction

/-- One actual run of binary rank scanning/generation, target preparation,
retained target-provider evaluation, input-cache numerical/read execution,
and list-spine word/trace assembly, with the concrete four-gate provider. -/
def assembledRun (net : OfflineNet) (k p : ℕ) :
    FullyAssembledInputResult 4 (originalWireCount k) net.lengthBound :=
  fullyAssembledInputRun nativeEntry inverseLabel net.table net.lengthBound k p

theorem assembledRun_word (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).compilation.word =
      numericalExtractionCode (fun i => nativePacketDataOracle (nativeEntry i))
        inverseLabel net.table net.lengthBound k p := by
  exact fullyAssembledInputRun_word nativeEntry inverseLabel net.table
    net.lengthBound k p net.lengths

theorem assembledRun_erase (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).erase.erase = inputRun net k p := by
  unfold assembledRun inputRun
  rw [fullyAssembledInputRun_erase, fullyScannedInputRun_erase]

theorem assembledRun_word_eq_inputRun (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).compilation.word = (inputRun net k p).compilation.word := by
  rw [assembledRun_word, inputRun_word]

theorem assembledRun_uses_finite_library (net : OfflineNet) (k p : ℕ) :
    ∀ g ∈ labelCircuit rationalGate (assembledRun net k p).compilation.word,
      usesFiniteLibrary rationalGate g := by
  rw [assembledRun_word_eq_inputRun]
  exact inputRun_uses_finite_library net k p

theorem assembledRun_length (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).compilation.word.length ≤ actualGatePolynomial k *
      (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5) := by
  rw [assembledRun_word_eq_inputRun]
  exact inputRun_length net k p

theorem assembledRun_fidelity (net : OfflineNet) (k p : ℕ) (z : Fin 4 → ℂ)
    (hz : IsUnitVector z) :
    1 - (1/2 : ℝ)^p ≤ (Extraction.bellProjector (d := Bits (bellPairYield k)) *
      approximateExtractionOutput k (denote (labelCircuit rationalGate
        (assembledRun net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re := by
  rw [assembledRun_word_eq_inputRun]
  exact inputRun_fidelity net k p z hz

def assembledPrimitiveBound (net : OfflineNet) (k p : ℕ) : ℕ :=
  (1800*k*(k+3)^8 + inputPrimitiveBound net k p) +
    actualGatePolynomial k * ((8192*(net.lengthBound + 2*(net.lastIndex+1)+2)) *
      (logarithmicPrecision k p+1)^13)

/-- Apply the fully assembled program's actual-record theorem directly.
Output erasure is used only for specifications, not to invent cost equality. -/
theorem assembledRun_accounted_actions (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).accountedPrimitiveActions ≤ assembledPrimitiveBound net k p := by
  exact fullyAssembledInputRun_accountedPrimitiveActions nativeEntry inverseLabel
    net.table net.lengthBound k p (gateHeightCoefficient net.lengthBound) net.lengths
      (fun i r hr => queried_gate_height net.lengthBound (extractionPrecision k p) i r hr)

theorem assembledRun_inverse_calls (net : OfflineNet) (k p : ℕ) :
    (assembledRun net k p).compilation.inverseCalls ≤ actualGatePolynomial k *
      ((8192*(net.lengthBound + 2*(net.lastIndex+1)+2)) * (logarithmicPrecision k p+1)^13) := by
  exact fullyAssembledInputRun_inverseCalls nativeEntry inverseLabel net.table
    net.lengthBound k p net.lengths

/-- Single fixed finite table, before all sizes/accuracies/unknown inputs.
The bound covers exactly the specified retained primitive model; complete
provider, Nat/control/AST/index/allocation/counter machine costs stay open. -/
theorem concrete_assembled_compiler_exists :
    ∃ net : OfflineNet,
      (∀ (k p : ℕ) (z : Fin 4 → ℂ), IsUnitVector z →
        1 - (1/2 : ℝ)^p ≤
          (Extraction.bellProjector (d := Bits (bellPairYield k)) *
            approximateExtractionOutput k (denote (labelCircuit rationalGate
              (assembledRun net k p).compilation.word)) (pureMatrix (bitPurePower k z))).trace.re) ∧
      (∀ k p : ℕ, (assembledRun net k p).accountedPrimitiveActions ≤ assembledPrimitiveBound net k p) ∧
      (∀ k p : ℕ, (assembledRun net k p).compilation.word.length ≤ actualGatePolynomial k *
        (32 * (net.lengthBound + 1) * (logarithmicPrecision k p + 1)^5)) ∧
      (∀ k p : ℕ, ∀ g ∈ labelCircuit rationalGate (assembledRun net k p).compilation.word,
        usesFiniteLibrary rationalGate g) := by
  obtain ⟨net⟩ := offlineNet_exists
  exact ⟨net, assembledRun_fidelity net, assembledRun_accounted_actions net,
    assembledRun_length net, assembledRun_uses_finite_library net⟩

end ConcreteNativeExtraction
