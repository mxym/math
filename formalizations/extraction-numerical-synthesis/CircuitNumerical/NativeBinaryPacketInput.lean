import CircuitNumerical.NativeWordEvaluation

namespace CircuitRecursion

/-- Actual input bits, with only positivity of the supplied denominator as
an invariant. Numerator and denominator padding is allowed at this boundary. -/
structure BinaryPacketInput where
  signs : List.Vector Bool 4
  numerators : List.Vector (List Bool) 4
  denominator : List Bool
  denominator_pos : 0<binaryWordValue denominator

def BinaryPacketInput.scalarWord (a : BinaryPacketInput) (i : Fin 4) : SignedBinaryWord :=
  ⟨a.signs.get i,a.numerators.get i⟩

/-- Semantic decoding is not used by the input normalization program. -/
def BinaryPacketInput.decode (a : BinaryPacketInput) : IntegerPacket :=
  ⟨List.Vector.ofFn (fun i => (a.scalarWord i).value),binaryWordValue a.denominator,a.denominator_pos⟩

structure BinaryPacketInputResult where
  packet : WordIntegerPacket
  numerators : List.Vector SignedBinaryNormalizationResult 4
  denominator : BinaryWordTrimResult

/-- Direct binary-data adapter: four stored sign/trim normalizers and one
stored denominator trim. There is no Nat.bits or rational conversion. -/
def binaryPacketInputProgram (a : BinaryPacketInput) : BinaryPacketInputResult :=
  let numerators:=List.Vector.ofFn (fun i => signedBinaryNormalizeProgram (a.scalarWord i))
  let denominator:=binaryTrimProgram a.denominator
  ⟨⟨numerators.map SignedBinaryNormalizationResult.word,denominator.bits,by
      intro i
      simp only [numerators,List.Vector.get_map,List.Vector.get_ofFn]
      exact signedBinaryNormalizeProgram_canonical _,
    binaryTrimProgram_canonical _,by simpa only [denominator,binaryTrimProgram_value] using a.denominator_pos⟩,
    numerators,denominator⟩

theorem binaryPacketInputProgram_decode (a : BinaryPacketInput) :
    (binaryPacketInputProgram a).packet.decode=a.decode := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro i
    simp only [binaryPacketInputProgram,WordIntegerPacket.decode,BinaryPacketInput.decode,
      List.Vector.get_map,List.Vector.get_ofFn,signedBinaryNormalizeProgram_value]
  · exact binaryTrimProgram_value a.denominator

def BinaryPacketInputResult.actions (result : BinaryPacketInputResult) : ℕ :=
  (∑ i : Fin 4,(result.numerators.get i).actions)+result.denominator.trace.actions+16

theorem binaryPacketInputProgram_actions (a : BinaryPacketInput) (B : ℕ)
    (hn : ∀ i,(a.numerators.get i).length≤B) (hd : a.denominator.length≤B) :
    (binaryPacketInputProgram a).actions≤64*(B+1) := by
  have hnum : ∀ i,(signedBinaryNormalizeProgram (a.scalarWord i)).actions≤6*(B+1)+4 := by
    intro i
    have h:=signedBinaryNormalizeProgram_actions (a.scalarWord i)
    change (signedBinaryNormalizeProgram (a.scalarWord i)).actions≤6*((a.numerators.get i).length+1)+4 at h
    have hi:=hn i
    omega
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hnum i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have hden:=binaryTrimProgram_actions a.denominator
  simp only [binaryPacketInputProgram,BinaryPacketInputResult.actions,List.Vector.get_ofFn]
  omega

end CircuitRecursion
