import CircuitNumerical.IntegerNumericalProgram

namespace CircuitRecursion

def binaryBitValue : Bool → ℕ
  | false => 0
  | true => 1

def binaryWordValue : List Bool → ℕ
  | [] => 0
  | b::bs => binaryBitValue b+2*binaryWordValue bs

def binaryFullAdder (a b c : Bool) : Bool×Bool :=
  (Bool.xor (Bool.xor a b) c,(a&&b)||(a&&c)||(b&&c))

theorem binaryBitValue_le_one (b : Bool) : binaryBitValue b≤1 := by cases b <;> decide

theorem binaryFullAdder_value (a b c : Bool) :
    binaryBitValue (binaryFullAdder a b c).1+2*binaryBitValue (binaryFullAdder a b c).2=
      binaryBitValue a+binaryBitValue b+binaryBitValue c := by
  cases a <;> cases b <;> cases c <;> decide

def binaryAddCarry : List Bool → List Bool → Bool → List Bool
  | [],[],carry => if carry then [true] else []
  | a::as,[],carry =>
    let digit:=binaryFullAdder a false carry
    digit.1::binaryAddCarry as [] digit.2
  | [],b::bs,carry =>
    let digit:=binaryFullAdder false b carry
    digit.1::binaryAddCarry [] bs digit.2
  | a::as,b::bs,carry =>
    let digit:=binaryFullAdder a b carry
    digit.1::binaryAddCarry as bs digit.2
termination_by as bs _ => as.length+bs.length

theorem binaryAddCarry_value (as bs : List Bool) (carry : Bool) :
    binaryWordValue (binaryAddCarry as bs carry)=
      binaryWordValue as+binaryWordValue bs+binaryBitValue carry := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [binaryAddCarry,binaryWordValue,binaryBitValue]
    | cons b bs ih =>
      have hs:=binaryFullAdder_value false b carry
      have ht:=ih (binaryFullAdder false b carry).2
      simp only [binaryWordValue] at ht
      rw [binaryAddCarry]
      change binaryBitValue (binaryFullAdder false b carry).1+
        2*binaryWordValue (binaryAddCarry [] bs (binaryFullAdder false b carry).2)=
          0+(binaryBitValue b+2*binaryWordValue bs)+binaryBitValue carry
      change binaryBitValue (binaryFullAdder false b carry).1+
        2*binaryBitValue (binaryFullAdder false b carry).2=0+binaryBitValue b+binaryBitValue carry at hs
      nlinarith
  | cons a as ih =>
    cases bs with
    | nil =>
      have hs:=binaryFullAdder_value a false carry
      have ht:=ih [] (binaryFullAdder a false carry).2
      simp only [binaryWordValue] at ht
      rw [binaryAddCarry]
      change binaryBitValue (binaryFullAdder a false carry).1+
        2*binaryWordValue (binaryAddCarry as [] (binaryFullAdder a false carry).2)=
          (binaryBitValue a+2*binaryWordValue as)+0+binaryBitValue carry
      change binaryBitValue (binaryFullAdder a false carry).1+
        2*binaryBitValue (binaryFullAdder a false carry).2=binaryBitValue a+0+binaryBitValue carry at hs
      nlinarith
    | cons b bs =>
      have hs:=binaryFullAdder_value a b carry
      have ht:=ih bs (binaryFullAdder a b carry).2
      rw [binaryAddCarry]
      change binaryBitValue (binaryFullAdder a b carry).1+
        2*binaryWordValue (binaryAddCarry as bs (binaryFullAdder a b carry).2)=
          (binaryBitValue a+2*binaryWordValue as)+(binaryBitValue b+2*binaryWordValue bs)+binaryBitValue carry
      nlinarith

theorem binaryAddCarry_length (as bs : List Bool) (carry : Bool) :
    (binaryAddCarry as bs carry).length≤max as.length bs.length+1 := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [binaryAddCarry]
    | cons b bs ih =>
      have h:=ih (binaryFullAdder false b carry).2
      simp only [binaryAddCarry,List.length_cons,List.length_nil] at h ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=ih [] (binaryFullAdder a false carry).2
      simp only [binaryAddCarry,List.length_cons,List.length_nil] at h ⊢
      omega
    | cons b bs =>
      have h:=ih bs (binaryFullAdder a b carry).2
      simp only [binaryAddCarry,List.length_cons] at h ⊢
      omega

/-- Boolean/list cost model: at most twelve local Boolean and list actions
per full-adder digit, and one terminal action. This is an explicit finite
bit-word cost semantics, separate from a machine implementation theorem. -/
def binaryAddBitOperations : List Bool → List Bool → Bool → ℕ
  | [],[],_ => 1
  | a::as,[],carry => binaryAddBitOperations as [] (binaryFullAdder a false carry).2+12
  | [],b::bs,carry => binaryAddBitOperations [] bs (binaryFullAdder false b carry).2+12
  | a::as,b::bs,carry => binaryAddBitOperations as bs (binaryFullAdder a b carry).2+12
termination_by as bs _ => as.length+bs.length

theorem binaryAddBitOperations_bound (as bs : List Bool) (carry : Bool) :
    binaryAddBitOperations as bs carry≤12*(max as.length bs.length+1) := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => simp [binaryAddBitOperations]
    | cons b bs ih =>
      have h:=ih (binaryFullAdder false b carry).2
      simp only [binaryAddBitOperations,List.length_nil,List.length_cons,Nat.zero_max] at h ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      have h:=ih [] (binaryFullAdder a false carry).2
      simp only [binaryAddBitOperations,List.length_nil,List.length_cons,Nat.max_zero] at h ⊢
      omega
    | cons b bs =>
      have h:=ih bs (binaryFullAdder a b carry).2
      simp only [binaryAddBitOperations,List.length_cons] at h ⊢
      omega

theorem binaryWordValue_lt_power_length (bs : List Bool) : binaryWordValue bs<2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have hb:=binaryBitValue_le_one b
    simp only [binaryWordValue,List.length_cons,pow_succ]
    omega

end CircuitRecursion
