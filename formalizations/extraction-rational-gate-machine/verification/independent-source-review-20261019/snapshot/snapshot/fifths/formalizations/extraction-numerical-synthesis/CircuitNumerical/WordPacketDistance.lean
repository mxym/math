import CircuitNumerical.SignedFourSum

namespace CircuitRecursion

structure WordDistanceCoordinateResult where
  leftRun : SignedWordMultiplicationResult
  rightRun : SignedWordMultiplicationResult
  differenceRun : SignedWordAdditionResult
  squareRun : SignedWordMultiplicationResult

def WordDistanceCoordinateResult.word (result : WordDistanceCoordinateResult) : SignedBinaryWord :=
  result.squareRun.word

def wordDistanceCoordinateProgram (a b : WordIntegerPacket) (i : Fin 4) : WordDistanceCoordinateResult :=
  let left:=signedMultiplyProgram (a.numerators.get i) ⟨false,b.denominator⟩
  let right:=signedMultiplyProgram (b.numerators.get i) ⟨false,a.denominator⟩
  let difference:=signedSubtractProgram left.word right.word
  let square:=signedMultiplyProgram difference.word difference.word
  ⟨left,right,difference,square⟩

theorem wordDistanceCoordinateProgram_value (a b : WordIntegerPacket) (i : Fin 4) :
    (wordDistanceCoordinateProgram a b i).word.value=(a.decode.distanceNumerator b.decode i)^2 := by
  simp only [wordDistanceCoordinateProgram,WordDistanceCoordinateResult.word,signedMultiplyProgram_value,
    signedSubtractProgram_value,IntegerPacket.distanceNumerator,WordIntegerPacket.decode,List.Vector.get_map]
  change ((a.numerators.get i).value*(binaryWordValue b.denominator:ℤ)-
    (b.numerators.get i).value*(binaryWordValue a.denominator:ℤ))*
    ((a.numerators.get i).value*(binaryWordValue b.denominator:ℤ)-
    (b.numerators.get i).value*(binaryWordValue a.denominator:ℤ))=_
  ring

theorem wordDistanceCoordinateProgram_canonical (a b : WordIntegerPacket) (i : Fin 4) :
    (wordDistanceCoordinateProgram a b i).word.Canonical := signedMultiplyProgram_canonical _ _

def WordDistanceCoordinateResult.actions (result : WordDistanceCoordinateResult) : ℕ :=
  result.leftRun.actions+result.rightRun.actions+result.differenceRun.actions+result.squareRun.actions+18

theorem wordDistanceCoordinateProgram_width_actions (a b : WordIntegerPacket) (i : Fin 4) (B : ℕ)
    (ha : (∀ j,(a.numerators.get j).bits.length≤B) ∧ a.denominator.length≤B)
    (hb : (∀ j,(b.numerators.get j).bits.length≤B) ∧ b.denominator.length≤B) :
    (wordDistanceCoordinateProgram a b i).word.bits.length≤9*B+3 ∧
    (wordDistanceCoordinateProgram a b i).actions≤2000*(B+1)^2 := by
  let left:=signedMultiplyProgram (a.numerators.get i) ⟨false,b.denominator⟩
  let right:=signedMultiplyProgram (b.numerators.get i) ⟨false,a.denominator⟩
  let difference:=signedSubtractProgram left.word right.word
  have hl:=signedMultiplyProgram_uniform_actions (a.numerators.get i) ⟨false,b.denominator⟩ B (ha.1 i) hb.2
  have hr:=signedMultiplyProgram_uniform_actions (b.numerators.get i) ⟨false,a.denominator⟩ B (hb.1 i) ha.2
  have hll:=signedMultiplyProgram_length (a.numerators.get i) ⟨false,b.denominator⟩
  have hrl:=signedMultiplyProgram_length (b.numerators.get i) ⟨false,a.denominator⟩
  have hleft : left.word.bits.length≤3*B := by
    have hi:=ha.1 i;dsimp only [left];simp only at hll;omega
  have hright : right.word.bits.length≤3*B := by
    have hi:=hb.1 i;dsimp only [right];simp only at hrl;omega
  have hd:=signedSubtractProgram_actions left.word right.word
  have hdl:=signedAddProgram_length left.word right.word.negate
  have hdiff : difference.word.bits.length≤3*B+1 := by
    have hneg : right.word.negate.bits.length=right.word.bits.length := rfl
    dsimp only [difference,signedSubtractProgram]
    omega
  have hmax : max left.word.bits.length right.word.bits.length≤3*B := by omega
  have hsq:=signedMultiplyProgram_uniform_actions difference.word difference.word (3*B+1) hdiff hdiff
  have hsql:=signedMultiplyProgram_length difference.word difference.word
  change left.actions≤_ at hl
  change right.actions≤_ at hr
  change difference.actions+2≤_ at hd
  simp only [Nat.add_assoc] at hsq
  norm_num only at hsq
  constructor
  · change (signedMultiplyProgram difference.word difference.word).word.bits.length≤_
    omega
  · change left.actions+right.actions+difference.actions+
      (signedMultiplyProgram difference.word difference.word).actions+18≤_
    calc
      _≤100*(B+1)^2+100*(B+1)^2+50*(3*B+2)+100*(3*B+2)^2+18 := by omega
      _≤(100*(B+1)^2+100*(B+1)^2+50*(3*B+2)+100*(3*B+2)^2+18)+
          (900*B^2+2250*B+1282) := Nat.le_add_right _ _
      _=2000*(B+1)^2 := by ring

structure WordPacketDistanceResult where
  scalar : WordIntegerScalar
  coordinates : List.Vector WordDistanceCoordinateResult 4
  sumRun : SignedFourSumResult
  denominatorProduct : NaturalWordMultiplicationResult
  denominatorSquare : NaturalWordMultiplicationResult

def wordPacketDistanceProgram (a b : WordIntegerPacket) : WordPacketDistanceResult :=
  let coordinates:=List.Vector.ofFn (wordDistanceCoordinateProgram a b)
  let sum:=signedFourSumProgram (coordinates.map WordDistanceCoordinateResult.word)
  let denominator:=naturalMultiplyProgram a.denominator b.denominator
  let square:=naturalMultiplyProgram denominator.bits denominator.bits
  ⟨⟨sum.word,square.bits,signedFourSumProgram_canonical _,naturalMultiplyProgram_canonical _ _,by
      rw [naturalMultiplyProgram_value,naturalMultiplyProgram_value]
      exact Nat.mul_pos (Nat.mul_pos a.denominator_pos b.denominator_pos)
        (Nat.mul_pos a.denominator_pos b.denominator_pos)⟩,coordinates,sum,denominator,square⟩

theorem wordPacketDistanceProgram_decode (a b : WordIntegerPacket) :
    (wordPacketDistanceProgram a b).scalar.decode=a.decode.distanceScalar b.decode := by
  apply integerScalar_eq_components
  · simp only [wordPacketDistanceProgram,WordIntegerScalar.decode,signedFourSumProgram_value,
      List.Vector.get_map,List.Vector.get_ofFn,wordDistanceCoordinateProgram_value,IntegerPacket.distanceScalar]
  · simp only [wordPacketDistanceProgram,WordIntegerScalar.decode,naturalMultiplyProgram_value,
      IntegerPacket.distanceScalar,WordIntegerPacket.decode,pow_two]

def WordPacketDistanceResult.actions (result : WordPacketDistanceResult) : ℕ :=
  (∑ i : Fin 4,(result.coordinates.get i).actions)+result.sumRun.actions+
    result.denominatorProduct.actions+result.denominatorSquare.actions+24

theorem wordPacketDistanceProgram_height_actions (a b : WordIntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a.decode B) (hb : IntegerPacketHeight b.decode B) :
    (wordPacketDistanceProgram a b).actions≤11000*(B+2)^2 := by
  have hwA:=a.height_width B ha
  have hwB:=b.height_width B hb
  have hcoords:=fun i => wordDistanceCoordinateProgram_width_actions a b i (B+1) hwA hwB
  have hcs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (hcoords i).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hcs
  have hsum:=signedFourSumProgram_uniform_actions
    ((List.Vector.ofFn (wordDistanceCoordinateProgram a b)).map WordDistanceCoordinateResult.word)
    (9*(B+1)+3) (by intro i;simpa only [List.Vector.get_map,List.Vector.get_ofFn] using (hcoords i).1)
  have hd:=naturalMultiplyProgram_uniform_actions a.denominator b.denominator (B+1) hwA.2 hwB.2
  have hdl:=naturalMultiplyProgram_length a.denominator b.denominator
  have hdenlen : (naturalMultiplyProgram a.denominator b.denominator).bits.length≤3*(B+1) := by omega
  have hsq:=naturalMultiplyProgram_uniform_actions (naturalMultiplyProgram a.denominator b.denominator).bits
    (naturalMultiplyProgram a.denominator b.denominator).bits (3*(B+1)) hdenlen hdenlen
  simp only [Nat.add_assoc] at hcs hd
  norm_num only at hcs hd
  simp only [wordPacketDistanceProgram,WordPacketDistanceResult.actions,List.Vector.get_ofFn]
  calc
    _≤4*(2000*(B+2)^2)+160*(9*(B+1)+3+4)+100*(B+2)^2+100*(3*(B+1)+1)^2+24 := by omega
    _≤(4*(2000*(B+2)^2)+160*(9*(B+1)+3+4)+100*(B+2)^2+100*(3*(B+1)+1)^2+24)+
        (2000*B^2+7760*B+7416) := Nat.le_add_right _ _
    _=11000*(B+2)^2 := by ring

end CircuitRecursion
