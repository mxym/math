import EffectiveEncoding.NativeBinaryRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure NativeTripleWords where
  first : UnaryWordEncodingResult
  second : UnaryWordEncodingResult
  third : UnaryWordEncodingResult

/-- Three real Boolean encoders, each executed once. No Nat.bits adapter. -/
def nativeTripleWordProgram (t : Triple) : NativeTripleWords :=
  ⟨unaryWordEncoding t.1,unaryWordEncoding t.2.1,unaryWordEncoding t.2.2⟩

/-- Semantic projection only; comparison programs read the stored Bool lists. -/
def NativeTripleWords.value (r : NativeTripleWords) : Triple :=
  (binaryWordValue r.first.bits,binaryWordValue r.second.bits,binaryWordValue r.third.bits)


theorem nativeTripleWordProgram_value (t : Triple) : (nativeTripleWordProgram t).value=t := by
  simp only [nativeTripleWordProgram,NativeTripleWords.value,unaryWordEncoding_value]


def NativeTripleWords.encodingActions (r : NativeTripleWords) : ℕ :=
  r.first.trace.incrementTrimActions+r.second.trace.incrementTrimActions+r.third.trace.incrementTrimActions


theorem nativeTripleWordProgram_encodingActions (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeTripleWordProgram t).encodingActions≤96*(k+1)^2 := by
  have h1:=unaryWordEncoding_incrementTrimActions t.1
  have h2:=unaryWordEncoding_incrementTrimActions t.2.1
  have h3:=unaryWordEncoding_incrementTrimActions t.2.2
  have ht1 : t.1≤k := by unfold total at h;omega
  have ht2 : t.2.1≤k := by unfold total at h;omega
  have ht3 : t.2.2≤k := by unfold total at h;omega
  have p1:=Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right ht1 1) 2)
  have p2:=Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right ht2 1) 2)
  have p3:=Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (Nat.add_le_add_right ht3 1) 2)
  change (unaryWordEncoding t.1).trace.incrementTrimActions+
    (unaryWordEncoding t.2.1).trace.incrementTrimActions+
      (unaryWordEncoding t.2.2).trace.incrementTrimActions≤_
  omega


def NativeTripleWords.Width (r : NativeTripleWords) (B : ℕ) : Prop :=
  r.first.bits.length≤B ∧ r.second.bits.length≤B ∧ r.third.bits.length≤B


theorem nativeTripleWordProgram_width (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeTripleWordProgram t).Width (k+1) := by
  have h1:=unaryWordEncoding_length t.1
  have h2:=unaryWordEncoding_length t.2.1
  have h3:=unaryWordEncoding_length t.2.2
  unfold total at h
  exact ⟨h1.trans (by omega),h2.trans (by omega),h3.trans (by omega)⟩


def nativeOrderIsEqual : Ordering → Bool
  | .eq => true
  | _ => false


theorem nativeOrderIsEqual_correct (as bs : List Bool) :
    nativeOrderIsEqual (binaryWordCompareProgram as bs).order=(binaryWordValue as==binaryWordValue bs) := by
  have hc:=binaryWordCompareProgram_correct as bs
  cases ho : (binaryWordCompareProgram as bs).order with
  | lt =>
    have hlt : binaryWordValue as<binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using hc
    simp only [nativeOrderIsEqual,beq_false_of_ne (Nat.ne_of_lt hlt)]
  | eq =>
    have heq : binaryWordValue as=binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using hc
    simp only [nativeOrderIsEqual,heq,beq_self_eq_true]
  | gt =>
    have hgt : binaryWordValue bs<binaryWordValue as := by simpa only [ho,binaryComparisonCorrect] using hc
    simp only [nativeOrderIsEqual,beq_false_of_ne (Nat.ne_of_gt hgt)]

structure NativeTripleComparison where
  equal : Bool
  first : BinaryWordComparisonResult
  second : BinaryWordComparisonResult
  third : BinaryWordComparisonResult

/-- Each concrete word comparison is executed once and retained. Nat equality
is absent from the value program; the three ordering-tag tests are finite. -/
def nativeTripleComparisonProgram (a b : NativeTripleWords) : NativeTripleComparison :=
  let x:=binaryWordCompareProgram a.first.bits b.first.bits
  let y:=binaryWordCompareProgram a.second.bits b.second.bits
  let z:=binaryWordCompareProgram a.third.bits b.third.bits
  ⟨nativeOrderIsEqual x.order&&(nativeOrderIsEqual y.order&&nativeOrderIsEqual z.order),x,y,z⟩


theorem nativeTripleComparisonProgram_equal (a b : NativeTripleWords) :
    (nativeTripleComparisonProgram a b).equal=(a.value==b.value) := by
  simp only [nativeTripleComparisonProgram,nativeOrderIsEqual_correct,NativeTripleWords.value]
  rfl

/-- Concrete comparison traces plus six local ordering/Boolean actions.
Loop/index/counter/record allocation costs outside these traces stay separate. -/
def NativeTripleComparison.actions (r : NativeTripleComparison) : ℕ :=
  r.first.trace.actions+r.second.trace.actions+r.third.trace.actions+6


theorem nativeTripleComparisonProgram_actions (a b : NativeTripleWords) (B : ℕ)
    (ha : a.Width B) (hb : b.Width B) :
    (nativeTripleComparisonProgram a b).actions≤48*(B+1)+6 := by
  have h1:=(binaryWordCompareProgram_actions a.first.bits b.first.bits).trans
    (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le ha.1 hb.1) 1))
  have h2:=(binaryWordCompareProgram_actions a.second.bits b.second.bits).trans
    (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le ha.2.1 hb.2.1) 1))
  have h3:=(binaryWordCompareProgram_actions a.third.bits b.third.bits).trans
    (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le ha.2.2 hb.2.2) 1))
  change (binaryWordCompareProgram a.first.bits b.first.bits).trace.actions+
    (binaryWordCompareProgram a.second.bits b.second.bits).trace.actions+
      (binaryWordCompareProgram a.third.bits b.third.bits).trace.actions+6≤_
  omega

end EffectiveEncoding
