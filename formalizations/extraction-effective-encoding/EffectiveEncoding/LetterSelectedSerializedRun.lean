import EffectiveEncoding.LetterSelectedGeneration
import EffectiveEncoding.PlannedSerializedRun

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure LetterSelectedSerializedResult (m wires L : ℕ) where
  common : PlannedSerializedResult m wires L
  tables : List AcceptedOccupationTableRecord

/-- One actual generator execution supplies one word to actual retained target/
 numeric/read/assembly compilation and then actual Boolean output. The very
 same generation's accepted count/test/letter-selector tables are retained. -/
def letterSelectedSerializedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : LetterSelectedSerializedResult m (originalWireCount k) L :=
  let generated:=letterSelectedDescriptorRun k
  let precision:=dyadicCircuitPrecision generated.common.common.generation.word.length (p+1)
  let compilation:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L precision)
    generated.common.common.generation.word
  let stream:=binaryLabelStream compilation.value.word
  ⟨⟨⟨⟨precision,generated.common.common.generation,compilation,stream⟩,generated.common.common.masks⟩,
    generated.common.contexts⟩,generated.tables⟩

/-- Exact complete common retained record, not a reconstruction from semantic
 word equivalence. New selector records belong to this same forward run. -/
theorem letterSelectedSerializedRun_common {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (letterSelectedSerializedRun entry inverseLabel table L k p).common=
      plannedSerializedRun entry inverseLabel table L k p := by
  simp only [letterSelectedSerializedRun,letterSelectedDescriptorRun_common,plannedSerializedRun]
  rw [letterSelectedDescriptorRun_common]


def LetterSelectedSerializedResult.decoded {m wires L : ℕ} (r : LetterSelectedSerializedResult m wires L) :
    List (LabelGate m wires) := r.common.decoded


theorem letterSelectedSerializedRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((letterSelectedSerializedRun entry inverseLabel table L k p).common.common.execution.stream.bits++tail)=
      some ((letterSelectedSerializedRun entry inverseLabel table L k p).common.common.execution.compilation.value.word,tail) := by
  rw [letterSelectedSerializedRun_common]
  exact plannedSerializedRun_suffix_roundtrip entry inverseLabel table L k p tail


theorem letterSelectedSerializedRun_decoded_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (letterSelectedSerializedRun entry inverseLabel table L k p).decoded=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  unfold LetterSelectedSerializedResult.decoded
  rw [letterSelectedSerializedRun_common]
  exact plannedSerializedRun_decoded_word entry inverseLabel table L k p hL


def LetterSelectedSerializedResult.letterActions {m wires L : ℕ} (r : LetterSelectedSerializedResult m wires L) : ℕ :=
  (r.tables.map (fun p => p.2.letterActions)).sum


theorem letterSelectedSerializedRun_letterActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (letterSelectedSerializedRun entry inverseLabel table L k p).letterActions≤55*k*(k+5)^4 :=
  letterSelectedDescriptorRun_letterActions k


def LetterSelectedSerializedResult.accountedPrimitiveActions {m wires L : ℕ} (r : LetterSelectedSerializedResult m wires L) : ℕ :=
  r.common.accountedPrimitiveActions+r.letterActions


theorem letterSelectedGeneration_uniform (k p : ℕ) :
    55*k*(k+5)^4≤880*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  generalize hbdef : k+3=b
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  calc
    _≤55*b*(2*b)^4 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (Nat.pow_le_pow_left (by omega : k+5≤2*b) 4)
    _=880*b^5 := by ring
    _≤_ := by
      simpa only [pow_zero,Nat.mul_one] using
        serializedMonomial_le b Q 880 5 0 24 338 hb hQ (by decide) (by decide)


def letterSelectedSerializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  plannedSerializedPolynomialConstant m n L gateB+880

/-- Internal bound for actual same-record local primitives, with the fixed
 library's finite queried-height contract explicit. This does not charge the
 remaining host/Gray/index/decoder/control or library-provider runtime. -/
theorem letterSelectedSerializedRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (letterSelectedSerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      letterSelectedSerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  unfold LetterSelectedSerializedResult.accountedPrimitiveActions
  rw [letterSelectedSerializedRun_common]
  have hp:=(letterSelectedSerializedRun_letterActions entry inverseLabel table L k p).trans
    (letterSelectedGeneration_uniform k p)
  exact (Nat.add_le_add (plannedSerializedRun_accountedPrimitiveActions_polynomial
    entry inverseLabel table L k p gateB hL he) hp).trans_eq (by
      unfold letterSelectedSerializedPolynomialConstant
      rw [Nat.add_mul,Nat.add_mul])


theorem letterSelectedSerializedRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (letterSelectedSerializedRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [letterSelectedSerializedRun_decoded_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
