import EffectiveEncoding.PlannedCandidateGeneration
import EffectiveEncoding.MaskedSerializedRun

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure PlannedSerializedResult (m wires L : ℕ) where
  common : MaskedSerializedResult m wires L
  contexts : List BooleanContextRecord

/-- One genuine new forward execution: build every stage's Boolean/list plan
context once, retain it, and pass the same generated word to target/numeric/
read/assembly/materialization and Boolean serialization. Old terminal/context
calls occur only in correctness proofs, not in this value definition. -/
def plannedSerializedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : PlannedSerializedResult m (originalWireCount k) L :=
  let generated:=plannedCandidateDescriptorRun k
  let precision:=dyadicCircuitPrecision generated.common.generation.word.length (p+1)
  let compilation:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L precision)
    generated.common.generation.word
  let stream:=binaryLabelStream compilation.value.word
  ⟨⟨⟨precision,generated.common.generation,compilation,stream⟩,generated.common.masks⟩,generated.contexts⟩

/-- Exact full common retained record: generation/rank/table/mask/provider/
numeric/read/assembly/outer/output fields all agree. This is derived from the
whole generation-record refinement, not merely equal words. Newly executed
plan-table records remain separately retained and charged once. -/
theorem plannedSerializedRun_common {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (plannedSerializedRun entry inverseLabel table L k p).common=
      maskedSerializedRun entry inverseLabel table L k p := by
  simp only [plannedSerializedRun,plannedCandidateDescriptorRun_common,maskedSerializedRun]
  rw [plannedCandidateDescriptorRun_common]


def PlannedSerializedResult.decoded {m wires L : ℕ} (r : PlannedSerializedResult m wires L) :
    List (LabelGate m wires) := r.common.decoded


theorem plannedSerializedRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((plannedSerializedRun entry inverseLabel table L k p).common.execution.stream.bits++tail)=
      some ((plannedSerializedRun entry inverseLabel table L k p).common.execution.compilation.value.word,tail) := by
  rw [plannedSerializedRun_common]
  exact maskedSerializedRun_suffix_roundtrip entry inverseLabel table L k p tail


theorem plannedSerializedRun_decoded_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (plannedSerializedRun entry inverseLabel table L k p).decoded=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  unfold PlannedSerializedResult.decoded
  rw [plannedSerializedRun_common]
  exact maskedSerializedRun_decoded_word entry inverseLabel table L k p hL


def PlannedSerializedResult.planActions {m wires L : ℕ} (r : PlannedSerializedResult m wires L) : ℕ :=
  (r.contexts.map (fun p => p.2.planActions)).sum


theorem plannedSerializedRun_planActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (plannedSerializedRun entry inverseLabel table L k p).planActions≤1553*k*(k+3)^6 :=
  plannedCandidateDescriptorRun_planActions k

/-- Same-execution common partial primitive model and actual additional
plan-construction records. Common range/copy traces are not counted twice. -/
def PlannedSerializedResult.accountedPrimitiveActions {m wires L : ℕ} (r : PlannedSerializedResult m wires L) : ℕ :=
  r.common.accountedPrimitiveActions+r.planActions


theorem plannedGeneration_uniform (k p : ℕ) :
    1553*k*(k+3)^6≤1553*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  generalize hbdef : k+3=b
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  calc
    _≤1553*b*b^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _=1553*b^7 := by ring
    _≤_ := by
      simpa only [pow_zero,Nat.mul_one] using
        serializedMonomial_le b Q 1553 7 0 24 338 hb hQ (by decide) (by decide)


def plannedSerializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  maskedSerializedPolynomialConstant m n L gateB+1553

/-- Local primitive polynomial for the actual complete new terminal. Library
queried packet-height is the only supplied arithmetic contract; actual target
height and plan/preparation/provider/numeric/read/assembly traces are internal.
The remaining unmodeled source and machine costs are not claimed here. -/
theorem plannedSerializedRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (plannedSerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      plannedSerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  unfold PlannedSerializedResult.accountedPrimitiveActions
  rw [plannedSerializedRun_common]
  have hp:=(plannedSerializedRun_planActions entry inverseLabel table L k p).trans (plannedGeneration_uniform k p)
  exact (Nat.add_le_add (maskedSerializedRun_accountedPrimitiveActions_polynomial
    entry inverseLabel table L k p gateB hL he) hp).trans_eq (by
      unfold plannedSerializedPolynomialConstant
      rw [Nat.add_mul,Nat.add_mul])

/-- Original 2k-register all-pure-input fidelity of the actual decoded Bool
stream from the terminal that executes the new plan constructor. -/
theorem plannedSerializedRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (plannedSerializedRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [plannedSerializedRun_decoded_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
