import CircuitNumerical.BinaryWordMultiplication

namespace CircuitRecursion

def binaryComparisonCorrect (order : Ordering) (a b : ℕ) : Prop := match order with
  | .lt => a<b
  | .eq => a=b
  | .gt => b<a

inductive BinaryComparisonDecision where
  | keepHigher : Ordering → BinaryComparisonDecision
  | compareLow : Bool → Bool → BinaryComparisonDecision

structure BinaryComparisonChoice where
  order : Ordering
  decision : BinaryComparisonDecision

def binaryLowBitOrder : Bool → Bool → Ordering
  | false,false => .eq
  | false,true => .lt
  | true,false => .gt
  | true,true => .eq

def binaryComparisonChoice (higher : Ordering) (a b : Bool) : BinaryComparisonChoice := match higher with
  | .lt => ⟨.lt,.keepHigher .lt⟩
  | .gt => ⟨.gt,.keepHigher .gt⟩
  | .eq => ⟨binaryLowBitOrder a b,.compareLow a b⟩

theorem binaryComparisonChoice_correct (higher : Ordering) (a b : Bool) (x y : ℕ)
    (h : binaryComparisonCorrect higher x y) :
    binaryComparisonCorrect (binaryComparisonChoice higher a b).order
      (binaryBitValue a+2*x) (binaryBitValue b+2*y) := by
  have ha:=binaryBitValue_le_one a
  have hb:=binaryBitValue_le_one b
  cases higher with
  | lt => change x<y at h;change binaryBitValue a+2*x<binaryBitValue b+2*y;omega
  | gt => change y<x at h;change binaryBitValue b+2*y<binaryBitValue a+2*x;omega
  | eq =>
    change x=y at h
    cases a <;> cases b <;> simp only [binaryComparisonChoice,binaryLowBitOrder,binaryComparisonCorrect,binaryBitValue] <;> omega

/- The returned trace records which concrete list/ordering/bit branch was
taken. It stores the recursive trace directly and needs no list append. -/
inductive BinaryWordComparisonTrace where
  | terminal
  | frame : Option Bool → Option Bool → BinaryWordComparisonTrace → BinaryComparisonDecision → BinaryWordComparisonTrace

structure BinaryWordComparisonResult where
  order : Ordering
  trace : BinaryWordComparisonTrace

def binaryWordCompareProgram : List Bool → List Bool → BinaryWordComparisonResult
  | [],[] => ⟨.eq,.terminal⟩
  | a::as,[] =>
    let higher:=binaryWordCompareProgram as []
    let chosen:=binaryComparisonChoice higher.order a false
    ⟨chosen.order,.frame (some a) none higher.trace chosen.decision⟩
  | [],b::bs =>
    let higher:=binaryWordCompareProgram [] bs
    let chosen:=binaryComparisonChoice higher.order false b
    ⟨chosen.order,.frame none (some b) higher.trace chosen.decision⟩
  | a::as,b::bs =>
    let higher:=binaryWordCompareProgram as bs
    let chosen:=binaryComparisonChoice higher.order a b
    ⟨chosen.order,.frame (some a) (some b) higher.trace chosen.decision⟩
termination_by as bs => as.length+bs.length

theorem binaryWordCompareProgram_correct (as bs : List Bool) :
    binaryComparisonCorrect (binaryWordCompareProgram as bs).order (binaryWordValue as) (binaryWordValue bs) := by
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => simp only [binaryWordCompareProgram,binaryWordValue,binaryComparisonCorrect]
    | cons b bs ih =>
      have h:=binaryComparisonChoice_correct (binaryWordCompareProgram [] bs).order false b 0 (binaryWordValue bs) ih
      simpa only [binaryWordCompareProgram,binaryWordValue,binaryBitValue,zero_mul,zero_add] using h
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=binaryComparisonChoice_correct (binaryWordCompareProgram as []).order a false (binaryWordValue as) 0 (ih [])
      simpa only [binaryWordCompareProgram,binaryWordValue,binaryBitValue,zero_mul,zero_add] using h
    | cons b bs =>
      simpa only [binaryWordCompareProgram,binaryWordValue] using
        binaryComparisonChoice_correct (binaryWordCompareProgram as bs).order a b _ _ (ih bs)

def BinaryWordComparisonTrace.depth : BinaryWordComparisonTrace → ℕ
  | .terminal => 1
  | .frame _ _ higher _ => higher.depth+1

/-- Explicit finite Boolean/list/record action model. A low-bit choice uses
at most four local bit/return actions. The twelve actions per frame include
list inspection, saved-record reads, the ordering test and trace/result
construction. The terminal frame uses four actions. -/
def BinaryComparisonDecision.actions : BinaryComparisonDecision → ℕ
  | .keepHigher _ => 2
  | .compareLow _ _ => 4

def BinaryWordComparisonTrace.actions : BinaryWordComparisonTrace → ℕ
  | .terminal => 4
  | .frame _ _ higher decision => higher.actions+12+decision.actions

theorem binaryComparisonChoice_actions (higher : Ordering) (a b : Bool) :
    (binaryComparisonChoice higher a b).decision.actions≤4 := by
  cases higher <;> simp [binaryComparisonChoice,BinaryComparisonDecision.actions]

theorem binaryWordCompareProgram_depth (as bs : List Bool) :
    (binaryWordCompareProgram as bs).trace.depth≤max as.length bs.length+1 := by
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => simp [binaryWordCompareProgram,BinaryWordComparisonTrace.depth]
    | cons b bs ih =>
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.depth,List.length_nil,List.length_cons] at ih ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=ih []
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.depth,List.length_nil,List.length_cons] at h ⊢
      omega
    | cons b bs =>
      have h:=ih bs
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.depth,List.length_cons] at h ⊢
      omega

theorem binaryWordCompareProgram_actions (as bs : List Bool) :
    (binaryWordCompareProgram as bs).trace.actions≤16*(max as.length bs.length+1) := by
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.actions,List.length_nil,Nat.max_self];decide
    | cons b bs ih =>
      have hc:=binaryComparisonChoice_actions (binaryWordCompareProgram [] bs).order false b
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.actions,List.length_nil,List.length_cons,Nat.zero_max] at ih ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=ih []
      have hc:=binaryComparisonChoice_actions (binaryWordCompareProgram as []).order a false
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.actions,List.length_nil,List.length_cons,Nat.max_zero] at h ⊢
      omega
    | cons b bs =>
      have h:=ih bs
      have hc:=binaryComparisonChoice_actions (binaryWordCompareProgram as bs).order a b
      simp only [binaryWordCompareProgram,BinaryWordComparisonTrace.actions,List.length_cons] at h ⊢
      omega

def binaryWordLEProgram (as bs : List Bool) : Bool := match (binaryWordCompareProgram as bs).order with
  | .gt => false
  | _ => true

theorem binaryWordLEProgram_correct (as bs : List Bool) :
    binaryWordLEProgram as bs=true ↔ binaryWordValue as≤binaryWordValue bs := by
  have h:=binaryWordCompareProgram_correct as bs
  cases ho : (binaryWordCompareProgram as bs).order with
  | lt =>
    have ht : binaryWordValue as<binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using h
    constructor
    · intro _;exact ht.le
    · intro _;simp only [binaryWordLEProgram,ho]
  | eq =>
    have he : binaryWordValue as=binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using h
    constructor
    · intro _;exact he.le
    · intro _;simp only [binaryWordLEProgram,ho]
  | gt =>
    have ht : binaryWordValue bs<binaryWordValue as := by simpa only [ho,binaryComparisonCorrect] using h
    constructor
    · intro hf
      simp only [binaryWordLEProgram,ho,Bool.false_eq_true] at hf
    · intro hn
      omega

end CircuitRecursion
