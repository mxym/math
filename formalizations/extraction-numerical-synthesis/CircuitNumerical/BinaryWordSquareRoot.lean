import CircuitNumerical.BinaryWordDivision

namespace CircuitRecursion

inductive BinaryWordSqrtTrace where
  | terminal : BinaryWordSqrtTrace
  | frame : Bool → Bool → Bool → BinaryWordSqrtTrace → BinaryWordComparisonTrace →
      Option BinaryWordSubtractionTrace → BinaryWordSqrtTrace

structure BinaryWordSqrtResult where
  root : List Bool
  remainder : List Bool
  trace : BinaryWordSqrtTrace

def binaryWordSqrtZero : BinaryWordSqrtResult := ⟨[],[],.terminal⟩

/-- One restoring-square-root digit. The candidate remainder is 4r+d and
the test value is 4q+1. These shifts and constants are literal list conses. -/
def binaryWordSqrtStep (a b : Bool) (previous : BinaryWordSqrtResult) : BinaryWordSqrtResult :=
  let candidate:=a::b::previous.remainder
  let threshold:=true::false::previous.root
  let comparison:=binaryWordCompareProgram threshold candidate
  match comparison.order with
  | .gt => ⟨false::previous.root,candidate,.frame a b false previous.trace comparison.trace none⟩
  | _ =>
    let subtraction:=binarySubtractProgram candidate threshold false
    ⟨true::previous.root,subtraction.bits,.frame a b true previous.trace comparison.trace (some subtraction.trace)⟩

/-- Concrete restoring square root on LSB-first words. It processes two input
bits per frame and executes only Boolean comparison and subtraction. -/
def binaryWordSqrtProgram : List Bool → BinaryWordSqrtResult
  | [] => binaryWordSqrtZero
  | [a] => binaryWordSqrtStep a false binaryWordSqrtZero
  | a::b::as => binaryWordSqrtStep a b (binaryWordSqrtProgram as)

theorem binaryWordSqrtStep_correct (a b : Bool) (previous : BinaryWordSqrtResult)
    (hr : binaryWordValue previous.remainder<2*binaryWordValue previous.root+1) :
    4*(binaryWordValue previous.root^2+binaryWordValue previous.remainder)+binaryBitValue a+2*binaryBitValue b=
      binaryWordValue (binaryWordSqrtStep a b previous).root^2+
        binaryWordValue (binaryWordSqrtStep a b previous).remainder ∧
    binaryWordValue (binaryWordSqrtStep a b previous).remainder<
      2*binaryWordValue (binaryWordSqrtStep a b previous).root+1 := by
  let candidate:=a::b::previous.remainder
  let threshold:=true::false::previous.root
  have ha : binaryBitValue a≤1 := by cases a <;> decide
  have hb : binaryBitValue b≤1 := by cases b <;> decide
  have hc : binaryWordValue candidate=binaryBitValue a+2*binaryBitValue b+4*binaryWordValue previous.remainder := by
    simp only [candidate,binaryWordValue];ring
  have ht : binaryWordValue threshold=4*binaryWordValue previous.root+1 := by
    simp only [threshold,binaryWordValue,binaryBitValue];ring
  have hcomp:=binaryWordCompareProgram_correct threshold candidate
  cases he : (binaryWordCompareProgram threshold candidate).order with
  | lt =>
    rw [he] at hcomp
    change binaryWordValue threshold<binaryWordValue candidate at hcomp
    have hle : binaryWordValue threshold≤binaryWordValue candidate := by omega
    have hs:=binarySubtractProgram_nonnegative_value candidate threshold false (by simpa [binaryBitValue] using hle)
    simp only [binaryBitValue,Nat.sub_zero] at hs
    simp only [candidate,threshold] at he
    simp only [binaryWordSqrtStep,he,binaryWordValue]
    change _=(1+2*binaryWordValue previous.root)^2+binaryWordValue (binarySubtractProgram candidate threshold false).bits ∧
      binaryWordValue (binarySubtractProgram candidate threshold false).bits<2*(1+2*binaryWordValue previous.root)+1
    constructor <;> nlinarith [Nat.sub_add_cancel hle]
  | eq =>
    rw [he] at hcomp
    change binaryWordValue threshold=binaryWordValue candidate at hcomp
    have hle : binaryWordValue threshold≤binaryWordValue candidate := by omega
    have hs:=binarySubtractProgram_nonnegative_value candidate threshold false (by simpa [binaryBitValue] using hle)
    simp only [binaryBitValue,Nat.sub_zero] at hs
    simp only [candidate,threshold] at he
    simp only [binaryWordSqrtStep,he,binaryWordValue]
    change _=(1+2*binaryWordValue previous.root)^2+binaryWordValue (binarySubtractProgram candidate threshold false).bits ∧
      binaryWordValue (binarySubtractProgram candidate threshold false).bits<2*(1+2*binaryWordValue previous.root)+1
    constructor <;> nlinarith [Nat.sub_add_cancel hle]
  | gt =>
    rw [he] at hcomp
    change binaryWordValue candidate<binaryWordValue threshold at hcomp
    simp only [candidate,threshold] at he
    simp only [binaryWordSqrtStep,he,binaryWordValue]
    change _=(0+2*binaryWordValue previous.root)^2+binaryWordValue candidate ∧
      binaryWordValue candidate<2*(0+2*binaryWordValue previous.root)+1
    constructor <;> nlinarith

theorem binaryWordSqrtProgram_correct (as : List Bool) :
    binaryWordValue as=binaryWordValue (binaryWordSqrtProgram as).root^2+
      binaryWordValue (binaryWordSqrtProgram as).remainder ∧
    binaryWordValue (binaryWordSqrtProgram as).remainder<
      2*binaryWordValue (binaryWordSqrtProgram as).root+1 := by
  induction as using binaryWordSqrtProgram.induct with
  | case1 => decide
  | case2 a =>
    have h:=binaryWordSqrtStep_correct a false binaryWordSqrtZero (by decide)
    simpa [binaryWordSqrtProgram,binaryWordSqrtZero,binaryWordValue,binaryBitValue] using h
  | case3 a b as ih =>
    have h:=binaryWordSqrtStep_correct a b (binaryWordSqrtProgram as) ih.2
    simp only [binaryWordSqrtProgram,binaryWordValue]
    constructor
    · nlinarith [h.1,ih.1]
    · exact h.2

theorem binaryWordSqrtProgram_sqrt (as : List Bool) :
    binaryWordValue (binaryWordSqrtProgram as).root=Nat.sqrt (binaryWordValue as) := by
  have h:=binaryWordSqrtProgram_correct as
  apply Nat.eq_sqrt.mpr
  constructor <;> nlinarith [h.1,h.2]

theorem binaryWordSqrtStep_lengths (a b : Bool) (previous : BinaryWordSqrtResult) :
    (binaryWordSqrtStep a b previous).root.length=previous.root.length+1 ∧
    (binaryWordSqrtStep a b previous).remainder.length≤max previous.root.length previous.remainder.length+2 := by
  cases he : (binaryWordCompareProgram (true::false::previous.root) (a::b::previous.remainder)).order <;>
    simp only [binaryWordSqrtStep,he,List.length_cons,binarySubtractProgram_length]
  all_goals
    constructor
    · trivial
    · omega

theorem binaryWordSqrtProgram_lengths (as : List Bool) :
    (binaryWordSqrtProgram as).root.length≤as.length ∧
    (binaryWordSqrtProgram as).remainder.length≤as.length+1 := by
  induction as using binaryWordSqrtProgram.induct with
  | case1 => decide
  | case2 a =>
    have h:=binaryWordSqrtStep_lengths a false binaryWordSqrtZero
    simp only [binaryWordSqrtProgram,binaryWordSqrtZero,List.length_nil,List.length_cons] at h ⊢
    omega
  | case3 a b as ih =>
    have h:=binaryWordSqrtStep_lengths a b (binaryWordSqrtProgram as)
    simp only [binaryWordSqrtProgram,List.length_cons]
    omega

theorem binaryWordSqrtProgram_root_width (as : List Bool) :
    2*(binaryWordSqrtProgram as).root.length≤as.length+1 ∧
    as.length≤2*(binaryWordSqrtProgram as).root.length := by
  induction as using binaryWordSqrtProgram.induct with
  | case1 => decide
  | case2 a =>
    have h:=(binaryWordSqrtStep_lengths a false binaryWordSqrtZero).1
    simp only [binaryWordSqrtProgram,binaryWordSqrtZero,List.length_nil,List.length_cons] at h ⊢
    omega
  | case3 a b as ih =>
    have h:=(binaryWordSqrtStep_lengths a b (binaryWordSqrtProgram as)).1
    simp only [binaryWordSqrtProgram,List.length_cons]
    omega

theorem binaryWordSqrtProgram_root_length (as : List Bool) :
    (binaryWordSqrtProgram as).root.length=(as.length+1)/2 := by
  have h:=binaryWordSqrtProgram_root_width as
  omega

/-- Explicit Boolean/list/record action model over the actual returned tree.
The cost of evaluating the annotation is not included. -/
def BinaryWordSqrtTrace.actions : BinaryWordSqrtTrace → ℕ
  | .terminal => 6
  | .frame _ _ _ tail comparison subtraction =>
    tail.actions+comparison.actions+(subtraction.map BinaryWordSubtractionTrace.actions).getD 0+20

theorem binaryWordSqrtStep_actions (a b : Bool) (previous : BinaryWordSqrtResult) :
    (binaryWordSqrtStep a b previous).trace.actions≤previous.trace.actions+
      36*(max previous.root.length previous.remainder.length+3)+20 := by
  have hc:=binaryWordCompareProgram_actions (true::false::previous.root) (a::b::previous.remainder)
  have hs:=binarySubtractProgram_actions (a::b::previous.remainder) (true::false::previous.root) false
  cases he : (binaryWordCompareProgram (true::false::previous.root) (a::b::previous.remainder)).order
  all_goals
    simp only [binaryWordSqrtStep,he,BinaryWordSqrtTrace.actions,Option.map_some,Option.getD_some,
      Option.map_none,Option.getD_none]
    simp only [List.length_cons] at hc hs
    have hm : max (previous.root.length+1+1) (previous.remainder.length+1+1)=
        max previous.root.length previous.remainder.length+2 := by omega
    have hn : max (previous.remainder.length+1+1) (previous.root.length+1+1)=
        max previous.root.length previous.remainder.length+2 := by omega
    nlinarith

theorem binaryWordSqrtProgram_actions (as : List Bool) :
    (binaryWordSqrtProgram as).trace.actions≤64*(as.length+1)^2 := by
  induction as using binaryWordSqrtProgram.induct with
  | case1 => decide
  | case2 a =>
    have h:=binaryWordSqrtStep_actions a false binaryWordSqrtZero
    simp only [binaryWordSqrtProgram,binaryWordSqrtZero,List.length_nil,List.length_cons,
      Nat.max_self,BinaryWordSqrtTrace.actions] at h ⊢
    omega
  | case3 a b as ih =>
    have h:=binaryWordSqrtStep_actions a b (binaryWordSqrtProgram as)
    have hl:=binaryWordSqrtProgram_lengths as
    have hm : max (binaryWordSqrtProgram as).root.length (binaryWordSqrtProgram as).remainder.length≤as.length+1 := by omega
    simp only [binaryWordSqrtProgram,List.length_cons]
    nlinarith

end CircuitRecursion
