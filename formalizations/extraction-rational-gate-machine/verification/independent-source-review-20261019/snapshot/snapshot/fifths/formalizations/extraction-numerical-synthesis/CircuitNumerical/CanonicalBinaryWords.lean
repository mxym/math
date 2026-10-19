import CircuitNumerical.TracedWordArithmetic

namespace CircuitRecursion

inductive BinaryWordCanonical : List Bool → Prop where
  | nil : BinaryWordCanonical []
  | one : BinaryWordCanonical [true]
  | prepend (b c : Bool) (cs : List Bool) :
      BinaryWordCanonical (c::cs) → BinaryWordCanonical (b::c::cs)

inductive BinaryWordTrimDecision where
  | dropZero | keepOne | keepTail

inductive BinaryWordTrimTrace where
  | terminal : BinaryWordTrimTrace
  | frame : Bool → BinaryWordTrimTrace → BinaryWordTrimDecision → BinaryWordTrimTrace

structure BinaryWordTrimResult where
  bits : List Bool
  trace : BinaryWordTrimTrace

/-- Remove high zero padding on an LSB-first list. The trimmed tail is stored
once. Only matching a list constructor and the current Boolean chooses a
branch; no value, length, or natural comparison is used by the program. -/
def binaryTrimProgram : List Bool → BinaryWordTrimResult
  | [] => ⟨[],.terminal⟩
  | b::bs =>
    let tail:=binaryTrimProgram bs
    match tail.bits with
    | [] =>
      if b then ⟨[true],.frame b tail.trace .keepOne⟩
      else ⟨[],.frame b tail.trace .dropZero⟩
    | c::cs => ⟨b::c::cs,.frame b tail.trace .keepTail⟩

theorem binaryTrimProgram_value (as : List Bool) :
    binaryWordValue (binaryTrimProgram as).bits=binaryWordValue as := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    cases ht : (binaryTrimProgram bs).bits with
    | nil =>
      rw [ht] at ih
      cases b <;> simp only [binaryTrimProgram,ht,Bool.false_eq_true,ite_false,ite_true,binaryWordValue,binaryBitValue] at ih ⊢ <;> omega
    | cons c cs =>
      rw [ht] at ih
      simp only [binaryTrimProgram,ht,binaryWordValue]
      rw [←ih]
      rfl

theorem binaryTrimProgram_canonical (as : List Bool) :
    BinaryWordCanonical (binaryTrimProgram as).bits := by
  induction as with
  | nil => exact .nil
  | cons b bs ih =>
    cases ht : (binaryTrimProgram bs).bits with
    | nil =>
      cases b
      · simpa only [binaryTrimProgram,ht,Bool.false_eq_true,ite_false] using BinaryWordCanonical.nil
      · simpa only [binaryTrimProgram,ht,ite_true] using BinaryWordCanonical.one
    | cons c cs =>
      rw [ht] at ih
      simpa only [binaryTrimProgram,ht] using BinaryWordCanonical.prepend b c cs ih

theorem binaryTrimProgram_length (as : List Bool) :
    (binaryTrimProgram as).bits.length≤as.length := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    cases ht : (binaryTrimProgram bs).bits with
    | nil => cases b <;> simp only [binaryTrimProgram,ht,Bool.false_eq_true,ite_false,ite_true,List.length_nil,List.length_cons] <;> omega
    | cons c cs =>
      rw [ht] at ih
      simp only [binaryTrimProgram,ht,List.length_cons] at ih ⊢
      omega

theorem binaryWordCanonical_lower (as : List Bool) (h : BinaryWordCanonical as) :
    as=[] ∨ 2^(as.length-1)≤binaryWordValue as := by
  induction h with
  | nil => exact Or.inl rfl
  | one => right;decide
  | prepend b c cs h ih =>
    right
    have hi : 2^((c::cs).length-1)≤binaryWordValue (c::cs) := by
      rcases ih with he|hi
      · cases he
      · exact hi
    have hp:=Nat.mul_le_mul_left 2 hi
    simpa only [List.length_cons,Nat.add_sub_cancel,pow_succ,binaryWordValue,Nat.mul_comm] using
      (show 2*2^cs.length≤binaryBitValue b+2*binaryWordValue (c::cs) from by
        simp only [List.length_cons,Nat.add_sub_cancel] at hp
        omega)

theorem binaryWordCanonical_zero_iff (as : List Bool) (h : BinaryWordCanonical as) :
    binaryWordValue as=0 ↔ as=[] := by
  constructor
  · intro hz
    rcases binaryWordCanonical_lower as h with he|hi
    · exact he
    · have hp : 0<2^(as.length-1) := by positivity
      omega
  · rintro rfl
    rfl

theorem binaryWordCanonical_width (as : List Bool) (h : BinaryWordCanonical as) (B : ℕ)
    (hv : binaryWordValue as≤2^B) : as.length≤B+1 := by
  rcases binaryWordCanonical_lower as h with he|hi
  · simp only [he,List.length_nil];omega
  · by_contra hn
    have he : B+1≤as.length-1 := by omega
    have hp : 2^(B+1)≤2^(as.length-1) := Nat.pow_le_pow_right (by decide) he
    have hpos : 0<2^B := by positivity
    rw [pow_succ] at hp
    omega

theorem binaryTrimProgram_width (as : List Bool) (B : ℕ)
    (hv : binaryWordValue as≤2^B) : (binaryTrimProgram as).bits.length≤B+1 := by
  apply binaryWordCanonical_width _ (binaryTrimProgram_canonical as) B
  simpa only [binaryTrimProgram_value] using hv

/-- Six Boolean/list/record actions per input digit and one terminal action. -/
def BinaryWordTrimTrace.actions : BinaryWordTrimTrace → ℕ
  | .terminal => 1
  | .frame _ tail _ => tail.actions+6

theorem binaryTrimProgram_actions (as : List Bool) :
    (binaryTrimProgram as).trace.actions≤6*(as.length+1) := by
  induction as with
  | nil => decide
  | cons b bs ih =>
    cases ht : (binaryTrimProgram bs).bits with
    | nil =>
      cases b <;> simp only [binaryTrimProgram,ht,Bool.false_eq_true,ite_false,ite_true,
        BinaryWordTrimTrace.actions,List.length_cons] <;> omega
    | cons c cs =>
      simp only [binaryTrimProgram,ht,BinaryWordTrimTrace.actions,List.length_cons]
      omega

end CircuitRecursion
