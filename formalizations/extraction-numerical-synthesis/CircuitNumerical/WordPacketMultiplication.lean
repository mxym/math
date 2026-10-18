import CircuitNumerical.WordQuaternionCoordinates

namespace CircuitRecursion

structure WordIntegerPacket where
  numerators : List.Vector SignedBinaryWord 4
  denominator : List Bool
  numerators_canonical : ∀ i,(numerators.get i).Canonical
  denominator_canonical : BinaryWordCanonical denominator
  denominator_pos : 0<binaryWordValue denominator

def WordIntegerPacket.decode (a : WordIntegerPacket) : IntegerPacket :=
  ⟨a.numerators.map SignedBinaryWord.value,binaryWordValue a.denominator,a.denominator_pos⟩

theorem integerPacket_eq_components (a b : IntegerPacket)
    (hn : a.numerators=b.numerators) (hd : a.denominator=b.denominator) : a=b := by
  cases a
  cases b
  cases hn
  cases hd
  rfl

theorem WordIntegerPacket.height_width (a : WordIntegerPacket) (B : ℕ)
    (h : IntegerPacketHeight a.decode B) :
    (∀ i,(a.numerators.get i).bits.length≤B+1) ∧ a.denominator.length≤B+1 := by
  constructor
  · intro i
    apply SignedBinaryWord.canonical_width _ (a.numerators_canonical i) B
    simpa only [WordIntegerPacket.decode,List.Vector.get_map] using h.2 i
  · exact binaryWordCanonical_width _ a.denominator_canonical B h.1

def WordIntegerPacket.coordinate (a : WordIntegerPacket) (i : Fin 4) : WordIntegerScalar :=
  ⟨a.numerators.get i,a.denominator,a.numerators_canonical i,a.denominator_canonical,a.denominator_pos⟩

theorem WordIntegerPacket.coordinate_decode (a : WordIntegerPacket) (i : Fin 4) :
    (a.coordinate i).decode=a.decode.coordinate i := by
  apply integerScalar_eq_components
  · change (a.numerators.get i).value=(a.numerators.map SignedBinaryWord.value).get i
    exact (List.Vector.get_map _ _ _).symm
  · rfl

structure WordPacketMultiplicationResult where
  packet : WordIntegerPacket
  coordinates : List.Vector WordQuaternionCoordinateResult 4
  denominatorRun : NaturalWordMultiplicationResult

/-- One stored four-coordinate vector, with one stored denominator product. -/
def wordPacketMultiplyProgram (a b : WordIntegerPacket) : WordPacketMultiplicationResult :=
  let coordinates:=List.Vector.ofFn (wordQuaternionCoordinateProgram a.numerators b.numerators)
  let denominator:=naturalMultiplyProgram a.denominator b.denominator
  ⟨⟨coordinates.map WordQuaternionCoordinateResult.word,denominator.bits,by
      intro i
      simpa only [coordinates,List.Vector.get_map,List.Vector.get_ofFn] using
        wordQuaternionCoordinateProgram_canonical a.numerators b.numerators i,
    naturalMultiplyProgram_canonical _ _,by
      rw [naturalMultiplyProgram_value]
      exact Nat.mul_pos a.denominator_pos b.denominator_pos⟩,coordinates,denominator⟩

theorem wordPacketMultiplyProgram_decode (a b : WordIntegerPacket) :
    (wordPacketMultiplyProgram a b).packet.decode=a.decode.mul b.decode := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro i
    simpa only [wordPacketMultiplyProgram,WordIntegerPacket.decode,IntegerPacket.mul,
      List.Vector.get_map,List.Vector.get_ofFn,quaternionProduct] using
      wordQuaternionCoordinateProgram_value a.numerators b.numerators i
  · exact naturalMultiplyProgram_value a.denominator b.denominator

def WordPacketMultiplicationResult.actions (result : WordPacketMultiplicationResult) : ℕ :=
  (∑ i : Fin 4,(result.coordinates.get i).actions)+result.denominatorRun.actions+16

theorem wordPacketMultiplyProgram_uniform_actions (a b : WordIntegerPacket) (B : ℕ)
    (ha : (∀ i,(a.numerators.get i).bits.length≤B) ∧ a.denominator.length≤B)
    (hb : (∀ i,(b.numerators.get i).bits.length≤B) ∧ b.denominator.length≤B) :
    (wordPacketMultiplyProgram a b).actions≤6200*(B+1)^2 := by
  have hc:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) =>
    wordQuaternionCoordinateProgram_uniform_actions a.numerators b.numerators i B ha.1 hb.1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hc
  have hd:=naturalMultiplyProgram_uniform_actions a.denominator b.denominator B ha.2 hb.2
  simp only [wordPacketMultiplyProgram,WordPacketMultiplicationResult.actions,List.Vector.get_ofFn]
  nlinarith

theorem wordPacketMultiplyProgram_height_actions (a b : WordIntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a.decode B) (hb : IntegerPacketHeight b.decode B) :
    (wordPacketMultiplyProgram a b).actions≤6200*(B+2)^2 := by
  simpa only [Nat.add_assoc] using wordPacketMultiplyProgram_uniform_actions a b (B+1)
    (a.height_width B ha) (b.height_width B hb)

end CircuitRecursion
