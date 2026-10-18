import CircuitNumerical.BinaryWordSquareRoot

namespace CircuitRecursion

inductive BinaryWordAdditionTrace where
  | terminal : Bool → BinaryWordAdditionTrace
  | frame : Option Bool → Option Bool → Bool → Bool → Bool →
      BinaryWordAdditionTrace → BinaryWordAdditionTrace

structure BinaryWordAdditionResult where
  bits : List Bool
  trace : BinaryWordAdditionTrace

/-- Ripple carry with each digit and its actual recursive trace retained. -/
def binaryAddProgram : List Bool → List Bool → Bool → BinaryWordAdditionResult
  | [],[],carry => ⟨if carry then [true] else [],.terminal carry⟩
  | a::as,[],carry =>
    let digit:=binaryFullAdder a false carry
    let tail:=binaryAddProgram as [] digit.2
    ⟨digit.1::tail.bits,.frame (some a) none carry digit.1 digit.2 tail.trace⟩
  | [],b::bs,carry =>
    let digit:=binaryFullAdder false b carry
    let tail:=binaryAddProgram [] bs digit.2
    ⟨digit.1::tail.bits,.frame none (some b) carry digit.1 digit.2 tail.trace⟩
  | a::as,b::bs,carry =>
    let digit:=binaryFullAdder a b carry
    let tail:=binaryAddProgram as bs digit.2
    ⟨digit.1::tail.bits,.frame (some a) (some b) carry digit.1 digit.2 tail.trace⟩
termination_by as bs _ => as.length+bs.length

theorem binaryAddProgram_bits (as bs : List Bool) (carry : Bool) :
    (binaryAddProgram as bs carry).bits=binaryAddCarry as bs carry := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp only [binaryAddProgram,binaryAddCarry]
    | cons b bs ih => simp only [binaryAddProgram,binaryAddCarry,ih]
  | cons a as ih =>
    cases bs with
    | nil => simp only [binaryAddProgram,binaryAddCarry,ih]
    | cons b bs => simp only [binaryAddProgram,binaryAddCarry,ih]

theorem binaryAddProgram_value (as bs : List Bool) (carry : Bool) :
    binaryWordValue (binaryAddProgram as bs carry).bits=
      binaryWordValue as+binaryWordValue bs+binaryBitValue carry := by
  rw [binaryAddProgram_bits,binaryAddCarry_value]

theorem binaryAddProgram_length (as bs : List Bool) (carry : Bool) :
    (binaryAddProgram as bs carry).bits.length≤max as.length bs.length+1 := by
  rw [binaryAddProgram_bits]
  exact binaryAddCarry_length as bs carry

/-- The model charges one terminal action and twelve per executed digit. -/
def BinaryWordAdditionTrace.actions : BinaryWordAdditionTrace → ℕ
  | .terminal _ => 1
  | .frame _ _ _ _ _ tail => tail.actions+12

theorem binaryAddProgram_actions_eq (as bs : List Bool) (carry : Bool) :
    (binaryAddProgram as bs carry).trace.actions=binaryAddBitOperations as bs carry := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp only [binaryAddProgram,BinaryWordAdditionTrace.actions,binaryAddBitOperations]
    | cons b bs ih => simp only [binaryAddProgram,BinaryWordAdditionTrace.actions,binaryAddBitOperations,ih]
  | cons a as ih =>
    cases bs with
    | nil => simp only [binaryAddProgram,BinaryWordAdditionTrace.actions,binaryAddBitOperations,ih]
    | cons b bs => simp only [binaryAddProgram,BinaryWordAdditionTrace.actions,binaryAddBitOperations,ih]

theorem binaryAddProgram_actions (as bs : List Bool) (carry : Bool) :
    (binaryAddProgram as bs carry).trace.actions≤12*(max as.length bs.length+1) := by
  rw [binaryAddProgram_actions_eq]
  exact binaryAddBitOperations_bound as bs carry

inductive BinaryWordMultiplicationTrace where
  | terminal : BinaryWordMultiplicationTrace
  | shift : BinaryWordMultiplicationTrace → BinaryWordMultiplicationTrace
  | add : BinaryWordMultiplicationTrace → BinaryWordAdditionTrace → BinaryWordMultiplicationTrace

structure BinaryWordMultiplicationResult where
  bits : List Bool
  trace : BinaryWordMultiplicationTrace

/-- Schoolbook multiplication with the recursive product stored once and the
actual addition trace stored only in the branch that executes the adder. -/
def binaryMultiplyProgram (as : List Bool) : List Bool → BinaryWordMultiplicationResult
  | [] => ⟨[],.terminal⟩
  | false::bs =>
    let tail:=binaryMultiplyProgram as bs
    ⟨false::tail.bits,.shift tail.trace⟩
  | true::bs =>
    let tail:=binaryMultiplyProgram as bs
    let addition:=binaryAddProgram as (false::tail.bits) false
    ⟨addition.bits,.add tail.trace addition.trace⟩

theorem binaryMultiplyProgram_bits (as bs : List Bool) :
    (binaryMultiplyProgram as bs).bits=binaryMultiplyWord as bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [binaryMultiplyProgram,binaryMultiplyWord,binaryAddProgram_bits,ih]

theorem binaryMultiplyProgram_value (as bs : List Bool) :
    binaryWordValue (binaryMultiplyProgram as bs).bits=binaryWordValue as*binaryWordValue bs := by
  rw [binaryMultiplyProgram_bits,binaryMultiplyWord_value]

theorem binaryMultiplyProgram_length (as bs : List Bool) :
    (binaryMultiplyProgram as bs).bits.length≤as.length+2*bs.length := by
  rw [binaryMultiplyProgram_bits]
  exact binaryMultiplyWord_length as bs

def BinaryWordMultiplicationTrace.actions : BinaryWordMultiplicationTrace → ℕ
  | .terminal => 1
  | .shift tail => tail.actions+3
  | .add tail addition => tail.actions+addition.actions+3

theorem binaryMultiplyProgram_actions_eq (as bs : List Bool) :
    (binaryMultiplyProgram as bs).trace.actions=binaryMultiplyBitOperations as bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [binaryMultiplyProgram,BinaryWordMultiplicationTrace.actions,
      binaryAddProgram_actions_eq,binaryMultiplyProgram_bits,binaryMultiplyBitOperations,ih]

theorem binaryMultiplyProgram_actions (as bs : List Bool) :
    (binaryMultiplyProgram as bs).trace.actions≤24*(bs.length+1)*(as.length+2*bs.length+1) := by
  rw [binaryMultiplyProgram_actions_eq]
  exact binaryMultiplyBitOperations_bound as bs

theorem binaryMultiplyProgram_uniform_actions (as bs : List Bool) (B : ℕ)
    (ha : as.length≤B) (hb : bs.length≤B) :
    (binaryMultiplyProgram as bs).trace.actions≤72*(B+1)^2 := by
  rw [binaryMultiplyProgram_actions_eq]
  exact binaryMultiplyBitOperations_uniform as bs B ha hb

end CircuitRecursion
