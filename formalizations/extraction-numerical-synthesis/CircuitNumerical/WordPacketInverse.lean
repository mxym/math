import CircuitNumerical.WordPacketMultiplication

namespace CircuitRecursion

structure WordPacketInverseResult where
  packet : WordIntegerPacket
  coordinates : List.Vector SignedBinaryNormalizationResult 4

/-- Materialize the four normalizers once. A finite coordinate test chooses
whether to flip the sign, and every output has canonical zero sign. -/
def wordPacketInverseProgram (a : WordIntegerPacket) : WordPacketInverseResult :=
  let coordinates:=List.Vector.ofFn (fun i : Fin 4 => signedBinaryNormalizeProgram
    (if i=0 then a.numerators.get i else (a.numerators.get i).negate))
  ⟨⟨coordinates.map SignedBinaryNormalizationResult.word,a.denominator,by
      intro i
      simp only [coordinates,List.Vector.get_map,List.Vector.get_ofFn]
      exact signedBinaryNormalizeProgram_canonical _,
    a.denominator_canonical,a.denominator_pos⟩,coordinates⟩

theorem wordPacketInverseProgram_decode (a : WordIntegerPacket) :
    (wordPacketInverseProgram a).packet.decode=a.decode.inverse := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro i
    simp only [wordPacketInverseProgram,WordIntegerPacket.decode,IntegerPacket.inverse,List.Vector.get_map,
      List.Vector.get_ofFn,signedBinaryNormalizeProgram_value]
    split_ifs <;> simp only [SignedBinaryWord.negate_value]
  · rfl

def WordPacketInverseResult.actions (result : WordPacketInverseResult) : ℕ :=
  (∑ i : Fin 4,(result.coordinates.get i).actions)+16

theorem wordPacketInverseProgram_uniform_actions (a : WordIntegerPacket) (B : ℕ)
    (ha : ∀ i,(a.numerators.get i).bits.length≤B) :
    (wordPacketInverseProgram a).actions≤40*(B+2) := by
  have hcoord : ∀ i : Fin 4,
      (signedBinaryNormalizeProgram
        (if i=0 then a.numerators.get i else (a.numerators.get i).negate)).actions≤6*(B+1)+4 := by
    intro i
    have h:=signedBinaryNormalizeProgram_actions
      (if i=0 then a.numerators.get i else (a.numerators.get i).negate)
    split_ifs at h ⊢
    all_goals
      try simp only [SignedBinaryWord.negate] at h ⊢
      have hi:=ha i
      omega
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hcoord i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  simp only [wordPacketInverseProgram,WordPacketInverseResult.actions,List.Vector.get_ofFn]
  omega

theorem wordPacketInverseProgram_height_actions (a : WordIntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a.decode B) :
    (wordPacketInverseProgram a).actions≤40*(B+3) := by
  simpa only [Nat.add_assoc] using wordPacketInverseProgram_uniform_actions a (B+1) (a.height_width B ha).1

end CircuitRecursion
