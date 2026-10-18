import CircuitNumerical.BinaryWordSubtraction

namespace CircuitRecursion

inductive BinaryWordDivisionTrace where
  | terminal : BinaryWordDivisionTrace
  | frame : Bool → BinaryWordDivisionTrace → BinaryWordComparisonTrace →
      Option BinaryWordSubtractionTrace → BinaryWordDivisionTrace

structure BinaryWordDivisionResult where
  quotient : List Bool
  remainder : List Bool
  trace : BinaryWordDivisionTrace

/-- Base-two long division on LSB-first input words. The recursive call reads
the higher input digits first. Each frame runs its comparison once and runs
the ripple-borrow subtractor exactly when the comparison permits subtraction.
No natural-number division, subtraction or comparison computes these words. -/
def binaryWordDivisionProgram : List Bool → List Bool → BinaryWordDivisionResult
  | [],_ => ⟨[],[],.terminal⟩
  | a::as,bs =>
    let tail:=binaryWordDivisionProgram as bs
    let candidate:=a::tail.remainder
    let comparison:=binaryWordCompareProgram bs candidate
    match comparison.order with
    | .gt => ⟨false::tail.quotient,candidate,.frame false tail.trace comparison.trace none⟩
    | _ =>
      let subtraction:=binarySubtractProgram candidate bs false
      ⟨true::tail.quotient,subtraction.bits,.frame true tail.trace comparison.trace (some subtraction.trace)⟩

theorem binaryWordDivisionProgram_correct (as bs : List Bool)
    (hb : 0<binaryWordValue bs) :
    binaryWordValue as=binaryWordValue bs*binaryWordValue (binaryWordDivisionProgram as bs).quotient+
      binaryWordValue (binaryWordDivisionProgram as bs).remainder ∧
      binaryWordValue (binaryWordDivisionProgram as bs).remainder<binaryWordValue bs := by
  induction as with
  | nil => simpa [binaryWordDivisionProgram,binaryWordValue] using hb
  | cons a as ih =>
    let tail:=binaryWordDivisionProgram as bs
    let candidate:=a::tail.remainder
    have hi : binaryWordValue as=binaryWordValue bs*binaryWordValue tail.quotient+
        binaryWordValue tail.remainder ∧ binaryWordValue tail.remainder<binaryWordValue bs := ih
    have hbit : binaryBitValue a≤1 := by cases a <;> decide
    have hc : binaryWordValue candidate<2*binaryWordValue bs := by
      simp only [candidate,binaryWordValue]
      omega
    have hcomp:=binaryWordCompareProgram_correct bs candidate
    cases he : (binaryWordCompareProgram bs candidate).order with
    | lt =>
      rw [he] at hcomp
      simp only [candidate,tail] at he
      have hle : binaryWordValue bs≤binaryWordValue candidate := by
        change binaryWordValue bs<binaryWordValue candidate at hcomp
        omega
      have hs:=binarySubtractProgram_nonnegative_value candidate bs false (by simpa [binaryBitValue] using hle)
      simp only [binaryBitValue,Nat.sub_zero] at hs
      simp only [binaryWordDivisionProgram,he,binaryWordValue]
      change binaryBitValue a+2*binaryWordValue as=
        binaryWordValue bs*(1+2*binaryWordValue tail.quotient)+
          binaryWordValue (binarySubtractProgram candidate bs false).bits ∧
          binaryWordValue (binarySubtractProgram candidate bs false).bits<binaryWordValue bs
      have hv : binaryWordValue candidate=binaryBitValue a+2*binaryWordValue tail.remainder := rfl
      constructor <;> nlinarith [Nat.sub_add_cancel hle]
    | eq =>
      rw [he] at hcomp
      simp only [candidate,tail] at he
      have hle : binaryWordValue bs≤binaryWordValue candidate := by
        change binaryWordValue bs=binaryWordValue candidate at hcomp
        omega
      have hs:=binarySubtractProgram_nonnegative_value candidate bs false (by simpa [binaryBitValue] using hle)
      simp only [binaryBitValue,Nat.sub_zero] at hs
      simp only [binaryWordDivisionProgram,he,binaryWordValue]
      change binaryBitValue a+2*binaryWordValue as=
        binaryWordValue bs*(1+2*binaryWordValue tail.quotient)+
          binaryWordValue (binarySubtractProgram candidate bs false).bits ∧
          binaryWordValue (binarySubtractProgram candidate bs false).bits<binaryWordValue bs
      have hv : binaryWordValue candidate=binaryBitValue a+2*binaryWordValue tail.remainder := rfl
      constructor <;> nlinarith [Nat.sub_add_cancel hle]
    | gt =>
      rw [he] at hcomp
      simp only [candidate,tail] at he
      change binaryWordValue candidate<binaryWordValue bs at hcomp
      simp only [binaryWordDivisionProgram,he,binaryWordValue]
      change binaryBitValue a+2*binaryWordValue as=
        binaryWordValue bs*(0+2*binaryWordValue tail.quotient)+
          (binaryBitValue a+2*binaryWordValue tail.remainder) ∧
          (binaryBitValue a+2*binaryWordValue tail.remainder)<binaryWordValue bs
      constructor
      · nlinarith [hi.1]
      · exact hcomp

theorem binaryWordDivisionProgram_div_mod (as bs : List Bool)
    (hb : 0<binaryWordValue bs) :
    binaryWordValue (binaryWordDivisionProgram as bs).quotient=binaryWordValue as/binaryWordValue bs ∧
    binaryWordValue (binaryWordDivisionProgram as bs).remainder=binaryWordValue as%binaryWordValue bs := by
  have hi:=binaryWordDivisionProgram_correct as bs hb
  have hu:= (Nat.div_mod_unique hb).mpr (show
      binaryWordValue (binaryWordDivisionProgram as bs).remainder+
        binaryWordValue bs*binaryWordValue (binaryWordDivisionProgram as bs).quotient=binaryWordValue as ∧
      binaryWordValue (binaryWordDivisionProgram as bs).remainder<binaryWordValue bs from ⟨by omega,hi.2⟩)
  exact ⟨hu.1.symm,hu.2.symm⟩

theorem binaryWordDivisionProgram_quotient_length (as bs : List Bool) :
    (binaryWordDivisionProgram as bs).quotient.length=as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases he : (binaryWordCompareProgram bs (a::(binaryWordDivisionProgram as bs).remainder)).order <;>
      simp only [binaryWordDivisionProgram,he,List.length_cons,ih]

theorem binaryWordDivisionProgram_remainder_length (as bs : List Bool) :
    (binaryWordDivisionProgram as bs).remainder.length≤as.length+bs.length := by
  induction as with
  | nil => simp [binaryWordDivisionProgram]
  | cons a as ih =>
    cases he : (binaryWordCompareProgram bs (a::(binaryWordDivisionProgram as bs).remainder)).order <;>
      simp only [binaryWordDivisionProgram,he,binarySubtractProgram_length,List.length_cons] <;> omega

/-- An explicit model over the returned execution tree: six terminal actions,
twelve frame actions, and the actual comparison/subtraction trace charges.
It does not include the cost of computing this annotation. -/
def BinaryWordDivisionTrace.actions : BinaryWordDivisionTrace → ℕ
  | .terminal => 6
  | .frame _ tail comparison subtraction =>
    tail.actions+comparison.actions+(subtraction.map BinaryWordSubtractionTrace.actions).getD 0+12

theorem binaryWordDivisionProgram_actions (as bs : List Bool) :
    (binaryWordDivisionProgram as bs).trace.actions≤48*(as.length+1)*(as.length+bs.length+1) := by
  induction as with
  | nil => simp [binaryWordDivisionProgram,BinaryWordDivisionTrace.actions];omega
  | cons a as ih =>
    have hr:=binaryWordDivisionProgram_remainder_length as bs
    have hc:=binaryWordCompareProgram_actions bs (a::(binaryWordDivisionProgram as bs).remainder)
    have hs:=binarySubtractProgram_actions (a::(binaryWordDivisionProgram as bs).remainder) bs false
    cases he : (binaryWordCompareProgram bs (a::(binaryWordDivisionProgram as bs).remainder)).order
    all_goals
      simp only [binaryWordDivisionProgram,he,BinaryWordDivisionTrace.actions,Option.map_some,Option.getD_some,
        Option.map_none,Option.getD_none,List.length_cons]
      simp only [List.length_cons] at hc hs
      have hm : max bs.length ((binaryWordDivisionProgram as bs).remainder.length+1)≤as.length+bs.length+1 := by omega
      have hn : max ((binaryWordDivisionProgram as bs).remainder.length+1) bs.length≤as.length+bs.length+1 := by omega
      nlinarith

theorem binaryWordDivisionProgram_uniform_actions (as bs : List Bool) (B : ℕ)
    (ha : as.length≤B) (hb : bs.length≤B) :
    (binaryWordDivisionProgram as bs).trace.actions≤96*(B+1)^2 := by
  have h:=binaryWordDivisionProgram_actions as bs
  have h₁ : (as.length+1)*(as.length+bs.length+1)≤(B+1)*(2*B+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

end CircuitRecursion
