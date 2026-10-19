import CircuitNumerical.BinaryWordComparison

namespace CircuitRecursion

def binaryFullSubtractor (a b borrow : Bool) : Bool×Bool :=
  (Bool.xor (Bool.xor a b) borrow,((!a)&&b)||((!a)&&borrow)||(b&&borrow))

theorem binaryFullSubtractor_value (a b borrow : Bool) :
    binaryBitValue a+2*binaryBitValue (binaryFullSubtractor a b borrow).2=
      binaryBitValue b+binaryBitValue borrow+binaryBitValue (binaryFullSubtractor a b borrow).1 := by
  cases a <;> cases b <;> cases borrow <;> decide

inductive BinaryWordSubtractionTrace where
  | terminal : Bool → BinaryWordSubtractionTrace
  | frame : Option Bool → Option Bool → Bool → Bool → Bool →
      BinaryWordSubtractionTrace → BinaryWordSubtractionTrace

structure BinaryWordSubtractionResult where
  bits : List Bool
  borrow : Bool
  trace : BinaryWordSubtractionTrace

/-- Concrete ripple-borrow subtraction. The result retains the final borrow
and exactly the maximum input width; the program uses no natural subtraction. -/
def binarySubtractProgram : List Bool → List Bool → Bool → BinaryWordSubtractionResult
  | [],[],borrow => ⟨[],borrow,.terminal borrow⟩
  | a::as,[],borrow =>
    let digit:=binaryFullSubtractor a false borrow
    let tail:=binarySubtractProgram as [] digit.2
    ⟨digit.1::tail.bits,tail.borrow,.frame (some a) none borrow digit.1 digit.2 tail.trace⟩
  | [],b::bs,borrow =>
    let digit:=binaryFullSubtractor false b borrow
    let tail:=binarySubtractProgram [] bs digit.2
    ⟨digit.1::tail.bits,tail.borrow,.frame none (some b) borrow digit.1 digit.2 tail.trace⟩
  | a::as,b::bs,borrow =>
    let digit:=binaryFullSubtractor a b borrow
    let tail:=binarySubtractProgram as bs digit.2
    ⟨digit.1::tail.bits,tail.borrow,.frame (some a) (some b) borrow digit.1 digit.2 tail.trace⟩
termination_by as bs _ => as.length+bs.length

theorem binarySubtractProgram_value (as bs : List Bool) (borrow : Bool) :
    binaryWordValue as+2^(max as.length bs.length)*binaryBitValue (binarySubtractProgram as bs borrow).borrow=
      binaryWordValue bs+binaryBitValue borrow+binaryWordValue (binarySubtractProgram as bs borrow).bits := by
  induction as generalizing bs borrow with
  | nil =>
    induction bs generalizing borrow with
    | nil => simp [binarySubtractProgram,binaryWordValue]
    | cons b bs ih =>
      have hs:=binaryFullSubtractor_value false b borrow
      have ht:=ih (binaryFullSubtractor false b borrow).2
      simp only [binaryWordValue,List.length_nil,Nat.zero_max] at ht
      simp only [binarySubtractProgram,binaryWordValue,List.length_nil,List.length_cons,Nat.zero_max,pow_succ]
      change 0+2*binaryBitValue (binaryFullSubtractor false b borrow).2=
        binaryBitValue b+binaryBitValue borrow+binaryBitValue (binaryFullSubtractor false b borrow).1 at hs
      nlinarith
  | cons a as ih =>
    cases bs with
    | nil =>
      have hs:=binaryFullSubtractor_value a false borrow
      have ht:=ih [] (binaryFullSubtractor a false borrow).2
      simp only [binaryWordValue,List.length_nil,Nat.max_zero] at ht
      simp only [binarySubtractProgram,binaryWordValue,List.length_nil,List.length_cons,Nat.max_zero,pow_succ]
      change binaryBitValue a+2*binaryBitValue (binaryFullSubtractor a false borrow).2=
        0+binaryBitValue borrow+binaryBitValue (binaryFullSubtractor a false borrow).1 at hs
      nlinarith
    | cons b bs =>
      have hs:=binaryFullSubtractor_value a b borrow
      have ht:=ih bs (binaryFullSubtractor a b borrow).2
      have hm : max (as.length+1) (bs.length+1)=max as.length bs.length+1 := by omega
      simp only [binarySubtractProgram,binaryWordValue,List.length_cons,hm,pow_succ]
      nlinarith

theorem binarySubtractProgram_length (as bs : List Bool) (borrow : Bool) :
    (binarySubtractProgram as bs borrow).bits.length=max as.length bs.length := by
  induction as generalizing bs borrow with
  | nil =>
    induction bs generalizing borrow with
    | nil => simp [binarySubtractProgram]
    | cons b bs ih =>
      simp only [binarySubtractProgram,List.length_cons,List.length_nil,Nat.zero_max]
      exact congrArg Nat.succ (by simpa only [List.length_nil,Nat.zero_max] using ih (binaryFullSubtractor false b borrow).2)
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [binarySubtractProgram,List.length_cons,List.length_nil,Nat.max_zero]
      exact congrArg Nat.succ (by simpa only [List.length_nil,Nat.max_zero] using ih [] (binaryFullSubtractor a false borrow).2)
    | cons b bs =>
      have h:=ih bs (binaryFullSubtractor a b borrow).2
      simp only [binarySubtractProgram,List.length_cons]
      omega

theorem binarySubtractProgram_borrow (as bs : List Bool) (borrow : Bool) :
    (binarySubtractProgram as bs borrow).borrow=true ↔
      binaryWordValue as<binaryWordValue bs+binaryBitValue borrow := by
  have hv:=binarySubtractProgram_value as bs borrow
  have ho:=binaryWordValue_lt_power_length (binarySubtractProgram as bs borrow).bits
  rw [binarySubtractProgram_length] at ho
  cases hb : (binarySubtractProgram as bs borrow).borrow <;>
    simp only [hb,binaryBitValue,mul_zero,mul_one,add_zero,Bool.false_eq_true,true_iff,false_iff] at hv ⊢ <;> omega

theorem binarySubtractProgram_nonnegative_value (as bs : List Bool) (borrow : Bool)
    (h : binaryWordValue bs+binaryBitValue borrow≤binaryWordValue as) :
    binaryWordValue (binarySubtractProgram as bs borrow).bits=
      binaryWordValue as-binaryWordValue bs-binaryBitValue borrow := by
  have hv:=binarySubtractProgram_value as bs borrow
  have hb : (binarySubtractProgram as bs borrow).borrow=false := by
    cases he : (binarySubtractProgram as bs borrow).borrow with
    | false => rfl
    | true => have hn:=(binarySubtractProgram_borrow as bs borrow).mp he;omega
  simp only [hb,show binaryBitValue false=0 from rfl,mul_zero,add_zero] at hv
  omega

/-- The returned trace records each actual ripple digit and borrow. In the
explicit Boolean/list/record action model, the terminal costs 4 and each
digit costs 20, including the fixed full-subtractor Boolean circuit. -/
def BinaryWordSubtractionTrace.actions : BinaryWordSubtractionTrace → ℕ
  | .terminal _ => 4
  | .frame _ _ _ _ _ tail => tail.actions+20

theorem binarySubtractProgram_actions (as bs : List Bool) (borrow : Bool) :
    (binarySubtractProgram as bs borrow).trace.actions≤20*(max as.length bs.length+1) := by
  induction as generalizing bs borrow with
  | nil =>
    induction bs generalizing borrow with
    | nil => simp [binarySubtractProgram,BinaryWordSubtractionTrace.actions]
    | cons b bs ih =>
      have h:=ih (binaryFullSubtractor false b borrow).2
      simp only [binarySubtractProgram,BinaryWordSubtractionTrace.actions,List.length_nil,List.length_cons,Nat.zero_max] at h ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=ih [] (binaryFullSubtractor a false borrow).2
      simp only [binarySubtractProgram,BinaryWordSubtractionTrace.actions,List.length_nil,List.length_cons,Nat.max_zero] at h ⊢
      omega
    | cons b bs =>
      have h:=ih bs (binaryFullSubtractor a b borrow).2
      simp only [binarySubtractProgram,BinaryWordSubtractionTrace.actions,List.length_cons] at h ⊢
      omega

end CircuitRecursion
