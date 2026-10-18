import CircuitNumerical.NaturalWordFourProduct

namespace CircuitRecursion

def wordTupleDenominators (s : List.Vector WordIntegerScalar 4) : List.Vector (List Bool) 4 :=
  s.map WordIntegerScalar.denominator

def wordTupleComplement (s : List.Vector WordIntegerScalar 4) (i : Fin 4) : List.Vector (List Bool) 4 :=
  List.Vector.ofFn (fun j => if j=i then [true] else (s.get j).denominator)

theorem wordTupleComplement_value (s : List.Vector WordIntegerScalar 4) (i : Fin 4) :
    binaryWordValue (naturalFourProductProgram (wordTupleComplement s i)).bits=
      ∏ j∈Finset.univ.erase i,(s.get j).decode.denominator := by
  rw [naturalFourProductProgram_value]
  have h : (fun j => binaryWordValue ((wordTupleComplement s i).get j))=
      (fun j => if j=i then 1 else (s.get j).decode.denominator) := by
    funext j
    simp only [wordTupleComplement,List.Vector.get_ofFn]
    split_ifs <;> rfl
  rw [h,naturalProduct_replace_one]

structure WordPacketTupleResult where
  packet : WordIntegerPacket
  denominatorRun : NaturalWordFourProductResult
  complements : List.Vector NaturalWordFourProductResult 4
  numerators : List.Vector SignedWordMultiplicationResult 4

/-- All four scalar children are supplied as an already stored vector. This
program materializes its denominator, four complementary products and four
numerator products once each; no recursive scalar evaluator is called here. -/
def wordPacketTupleProgram (s : List.Vector WordIntegerScalar 4) : WordPacketTupleResult :=
  let denominator:=naturalFourProductProgram (wordTupleDenominators s)
  let complements:=List.Vector.ofFn (fun i => naturalFourProductProgram (wordTupleComplement s i))
  let numerators:=List.Vector.ofFn (fun i => signedMultiplyProgram (s.get i).numerator
    ⟨false,(complements.get i).bits⟩)
  ⟨⟨numerators.map SignedWordMultiplicationResult.word,denominator.bits,by
      intro i
      simp only [numerators,List.Vector.get_map,List.Vector.get_ofFn]
      exact signedMultiplyProgram_canonical _ _,
    naturalFourProductProgram_canonical _,by
      rw [naturalFourProductProgram_value]
      apply Finset.prod_pos
      intro i _
      simpa only [wordTupleDenominators,List.Vector.get_map] using (s.get i).denominator_pos⟩,
    denominator,complements,numerators⟩

theorem wordPacketTupleProgram_decode (s : List.Vector WordIntegerScalar 4) :
    (wordPacketTupleProgram s).packet.decode=IntegerPacket.ofScalars (fun i => (s.get i).decode) := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro i
    simp only [wordPacketTupleProgram,WordIntegerPacket.decode,List.Vector.get_map,List.Vector.get_ofFn,
      IntegerPacket.ofScalars]
    rw [signedMultiplyProgram_value]
    change (s.get i).numerator.value*(binaryWordValue
      (naturalFourProductProgram (wordTupleComplement s i)).bits:ℤ)=_
    rw [wordTupleComplement_value]
    rfl
  · change binaryWordValue (naturalFourProductProgram (wordTupleDenominators s)).bits=_
    rw [naturalFourProductProgram_value]
    simp only [IntegerPacket.ofScalars,wordTupleDenominators,List.Vector.get_map,WordIntegerScalar.decode]

def WordPacketTupleResult.actions (result : WordPacketTupleResult) : ℕ :=
  result.denominatorRun.actions+(∑ i : Fin 4,(result.complements.get i).actions)+
    (∑ i : Fin 4,(result.numerators.get i).actions)+24

theorem wordPacketTupleProgram_height_actions (s : List.Vector WordIntegerScalar 4) (B : ℕ)
    (hs : ∀ i,IntegerScalarHeight (s.get i).decode B) :
    (wordPacketTupleProgram s).actions≤13000*(B+2)^2 := by
  have hw:=fun i => (s.get i).height_width B (hs i)
  have hden:=naturalFourProductProgram_uniform_actions (wordTupleDenominators s) (B+1) (by
    intro i
    simpa only [wordTupleDenominators,List.Vector.get_map] using (hw i).2)
  have hc : ∀ i,(naturalFourProductProgram (wordTupleComplement s i)).actions≤1200*(B+2)^2 := by
    intro i
    apply naturalFourProductProgram_uniform_actions
    intro j
    simp only [wordTupleComplement,List.Vector.get_ofFn]
    split_ifs
    · simp only [List.length_cons,List.length_nil];omega
    · exact (hw j).2
  have hcl : ∀ i,(naturalFourProductProgram (wordTupleComplement s i)).bits.length≤4*B+1 := by
    intro i
    apply binaryWordCanonical_width _ (naturalFourProductProgram_canonical _) (4*B)
    apply naturalFourProductProgram_height
    intro j
    simp only [wordTupleComplement,List.Vector.get_ofFn]
    split_ifs
    · simp only [binaryWordValue,binaryBitValue,mul_zero,add_zero]
      exact Nat.one_le_pow _ _ (by decide)
    · exact (hs j).1
  have hn : ∀ i,(signedMultiplyProgram (s.get i).numerator
      ⟨false,(naturalFourProductProgram (wordTupleComplement s i)).bits⟩).actions≤100*(4*B+2)^2 := by
    intro i
    exact signedMultiplyProgram_uniform_actions _ _ (4*B+1) (by have hi:=(hw i).1;omega) (hcl i)
  have hcs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hc i)
  have hns:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hn i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hcs hns
  simp only [Nat.add_assoc] at hden
  norm_num only at hden
  simp only [wordPacketTupleProgram,WordPacketTupleResult.actions,List.Vector.get_ofFn]
  calc
    _≤1200*(B+2)^2+4*(1200*(B+2)^2)+4*(100*(4*B+2)^2)+24 := by omega
    _≤(1200*(B+2)^2+4*(1200*(B+2)^2)+4*(100*(4*B+2)^2)+24)+
        (600*B^2+21600*B+26376) := Nat.le_add_right _ _
    _=13000*(B+2)^2 := by ring

end CircuitRecursion
