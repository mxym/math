import RationalGateInterface.Library
import CircuitNumerical.NativeBinaryPacketInput
import CircuitNumerical.NativeCachedSynthesis

open CircuitRecursion RationalGateProvider RationalGateInterface
namespace RationalGateBinary

theorem binaryWordValue_eq_bitValue (bits : List Bool) :
    binaryWordValue bits = bitValue bits := by
  induction bits with
  | nil => rfl
  | cons b tail ih =>
      cases b <;> simp [binaryWordValue, binaryBitValue, bitValue, ih]

/-- The stored coordinate bit vector is built once. No integer or rational
materialization occurs in this input data program. -/
def binaryEntry (i : Fin 4) (precision : ℕ) : BinaryPacketInput :=
  let bits := entryBits i precision
  ⟨bits.map SignedBits.negative, bits.map SignedBits.magnitude,
    denominatorBits precision, by
      rw [binaryWordValue_eq_bitValue]
      exact denominator_positive precision⟩

theorem binaryEntry_decode (i : Fin 4) (precision : ℕ) :
    (binaryEntry i precision).decode = dyadicIntegerPacket (dyadicEntry i) precision := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro j
    simp [binaryEntry, BinaryPacketInput.decode, BinaryPacketInput.scalarWord,
      SignedBinaryWord.value, SignedBits.value, binaryWordValue_eq_bitValue,
      dyadicIntegerPacket, dyadicEntry]
  · simp [binaryEntry, BinaryPacketInput.decode, dyadicIntegerPacket,
      binaryWordValue_eq_bitValue, denominator_value]

def nativeEntryProgram (i : Fin 4) (precision : ℕ) : BinaryPacketInputResult :=
  binaryPacketInputProgram (binaryEntry i precision)

def nativeEntry (i : Fin 4) : NativePacketDataOracle := fun precision =>
  (nativeEntryProgram i precision).packet

theorem nativeEntry_decode (i : Fin 4) (precision : ℕ) :
    (nativeEntry i precision).decode = dyadicIntegerPacket (dyadicEntry i) precision := by
  exact (binaryPacketInputProgram_decode (binaryEntry i precision)).trans
    (binaryEntry_decode i precision)

theorem nativeEntry_oracle (i : Fin 4) :
    nativePacketDataOracle (nativeEntry i) = dyadicQuaternionOracle (dyadicEntry i) := by
  funext precision
  change (nativeEntry i precision).decode.value = _
  rw [nativeEntry_decode, dyadicIntegerPacket_value]

theorem nativeEntry_correct (i : Fin 4) :
    QApproximates (nativePacketDataOracle (nativeEntry i)) (rationalGate i) := by
  rw [nativeEntry_oracle]
  exact dyadicEntry_correct i

theorem nativeEntry_height (i : Fin 4) (precision : ℕ) :
    IntegerPacketHeight (nativeEntry i precision).decode (precision + 1) := by
  rw [nativeEntry_decode]
  exact dyadicIntegerPacket_height (dyadicEntry i) (rationalGate i)
    (dyadicEntry_correct i) precision

theorem nativeEntry_height_ninth (i : Fin 4) (precision : ℕ) :
    IntegerPacketHeight (nativeEntry i precision).decode ((precision + 1) ^ 9) := by
  apply IntegerPacketHeight.mono _ _ _ (nativeEntry_height i precision)
  simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ precision + 1)
    (by decide : 1 ≤ 9))

theorem nativeEntryProgram_normalization_actions (i : Fin 4) (precision : ℕ) :
    (nativeEntryProgram i precision).actions ≤ 64 * (precision + 2) := by
  have hn : ∀ j, ((binaryEntry i precision).numerators.get j).length ≤ precision + 1 := by
    intro j
    simp only [binaryEntry, List.Vector.get_map, entryBits_length]
    omega
  have hd : (binaryEntry i precision).denominator.length ≤ precision + 1 := by
    simp only [binaryEntry, denominator_length]
    exact le_refl _
  exact binaryPacketInputProgram_actions (binaryEntry i precision) (precision + 1) hn hd

end RationalGateBinary
