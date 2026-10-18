import EffectiveEncoding.PreparedNativeExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The actual addition/trim records are retained from each executed increment.
Nat recursion control, wrapper allocation and annotation evaluation are not
charged by this trace's increment/trim action projection. -/
inductive UnaryWordTrace where
  | zero : UnaryWordTrace
  | increment : UnaryWordTrace → BinaryWordAdditionTrace → BinaryWordTrimTrace → UnaryWordTrace

structure UnaryWordEncodingResult where
  bits : List Bool
  trace : UnaryWordTrace

/-- Convert the bounded native mass by actual Boolean ripple-carry increments.
No Nat.bits, binary quotient, Int/Rat conversion or semantic decoding is called. -/
def unaryWordEncoding : ℕ → UnaryWordEncodingResult
  | 0 => ⟨[],.zero⟩
  | n+1 =>
    let previous:=unaryWordEncoding n
    let increment:=binaryAddProgram previous.bits [true] false
    let trimmed:=binaryTrimProgram increment.bits
    ⟨trimmed.bits,.increment previous.trace increment.trace trimmed.trace⟩


theorem unaryWordEncoding_value (n : ℕ) : binaryWordValue (unaryWordEncoding n).bits=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unaryWordEncoding,binaryTrimProgram_value,binaryAddProgram_value,ih,binaryWordValue,binaryBitValue]


theorem unaryWordEncoding_canonical (n : ℕ) : BinaryWordCanonical (unaryWordEncoding n).bits := by
  cases n with
  | zero => exact .nil
  | succ n => exact binaryTrimProgram_canonical _


theorem unaryWordEncoding_length (n : ℕ) : (unaryWordEncoding n).bits.length≤n+1 := by
  induction n with
  | zero => simp [unaryWordEncoding]
  | succ n ih =>
    have hl:=binaryAddProgram_length (unaryWordEncoding n).bits [true] false
    have ht:=binaryTrimProgram_length (binaryAddProgram (unaryWordEncoding n).bits [true] false).bits
    simp only [List.length_cons,List.length_nil] at hl
    change (binaryTrimProgram (binaryAddProgram (unaryWordEncoding n).bits [true] false).bits).bits.length≤_
    omega


def UnaryWordTrace.incrementCount : UnaryWordTrace → ℕ
  | .zero => 0
  | .increment previous _ _ => previous.incrementCount+1


theorem unaryWordEncoding_incrementCount (n : ℕ) : (unaryWordEncoding n).trace.incrementCount=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [unaryWordEncoding,UnaryWordTrace.incrementCount,ih]

/-- Sum only the existing actual Boolean/list addition and trim trace models.
The projection does not charge its own Nat sum or the outer recursion control. -/
def UnaryWordTrace.incrementTrimActions : UnaryWordTrace → ℕ
  | .zero => 0
  | .increment previous addition trimming =>
    previous.incrementTrimActions+addition.actions+trimming.actions


theorem unaryWordEncoding_incrementTrimActions (n : ℕ) :
    (unaryWordEncoding n).trace.incrementTrimActions≤32*(n+1)^2 := by
  induction n with
  | zero => simp [unaryWordEncoding,UnaryWordTrace.incrementTrimActions]
  | succ n ih =>
    have hw:=unaryWordEncoding_length n
    have ha:=binaryAddProgram_actions (unaryWordEncoding n).bits [true] false
    have hl:=binaryAddProgram_length (unaryWordEncoding n).bits [true] false
    have ht:=binaryTrimProgram_actions (binaryAddProgram (unaryWordEncoding n).bits [true] false).bits
    simp only [List.length_cons,List.length_nil] at ha hl
    have ham : (binaryAddProgram (unaryWordEncoding n).bits [true] false).trace.actions≤12*(n+2) := by omega
    have htm : (binaryTrimProgram (binaryAddProgram (unaryWordEncoding n).bits [true] false).bits).trace.actions≤6*(n+3) := by omega
    change (unaryWordEncoding n).trace.incrementTrimActions+
      (binaryAddProgram (unaryWordEncoding n).bits [true] false).trace.actions+
      (binaryTrimProgram (binaryAddProgram (unaryWordEncoding n).bits [true] false).bits).trace.actions≤_
    nlinarith


theorem unaryWordEncoding_width (n : ℕ) :
    (unaryWordEncoding n).bits.length≤binaryWidth n+1 := by
  apply binaryWordCanonical_width _ (unaryWordEncoding_canonical n)
  rw [unaryWordEncoding_value]
  exact (Nat.le_succ n).trans (Nat.le_pow_clog (by decide : 1<2) (n+1))

end EffectiveEncoding
