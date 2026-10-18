import CircuitNumerical.RootProgramCosts
import CircuitNumerical.BinaryProgramTrace

namespace CircuitRecursion

/-- Exact comparison of raw scalar fractions by signed integer products.
The program does not normalize or construct rational values to compare. -/
def IntegerScalar.crossLE (a b : IntegerScalar) : Prop :=
  a.numerator*(b.denominator:ℤ)≤b.numerator*(a.denominator:ℤ)

instance (a b : IntegerScalar) : Decidable (a.crossLE b) := inferInstanceAs
  (Decidable (a.numerator*(b.denominator:ℤ)≤b.numerator*(a.denominator:ℤ)))

theorem IntegerScalar.crossLE_value (a b : IntegerScalar) : a.crossLE b ↔ a.value≤b.value := by
  have ha : (0:ℚ)<a.denominator := by exact_mod_cast a.denominator_pos
  have hb : (0:ℚ)<b.denominator := by exact_mod_cast b.denominator_pos
  change a.numerator*(b.denominator:ℤ)≤b.numerator*(a.denominator:ℤ) ↔
    (a.numerator:ℚ)/(a.denominator:ℚ)≤(b.numerator:ℚ)/(b.denominator:ℚ)
  rw [div_le_div_iff₀ ha hb]
  constructor <;> intro h <;> exact_mod_cast h

def integerMinIndex : (n : ℕ) → (Fin (n+1) → IntegerScalar) → Fin (n+1)
  | 0,_ => 0
  | n+1,score =>
    let j:=integerMinIndex n (fun i => score i.succ)
    if (score 0).crossLE (score j.succ) then 0 else j.succ

theorem integerMinIndex_eq (n : ℕ) (score : Fin (n+1) → IntegerScalar) :
    integerMinIndex n score=rationalMinIndex n (fun i => (score i).value) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [integerMinIndex,rationalMinIndex,ih,IntegerScalar.crossLE_value]

def integerMaxIndex (n : ℕ) (score : Fin (n+1) → IntegerScalar) : Fin (n+1) :=
  integerMinIndex n (fun i => (score i).neg)

theorem integerMaxIndex_eq (n : ℕ) (score : Fin (n+1) → IntegerScalar) :
    integerMaxIndex n score=rationalMaxIndex n (fun i => (score i).value) := by
  simp only [integerMaxIndex,integerMinIndex_eq,rationalMaxIndex,IntegerScalar.neg_value]

theorem IntegerScalar.crossLE_operands_height (a b : IntegerScalar) (A B : ℕ)
    (ha : IntegerScalarHeight a A) (hb : IntegerScalarHeight b B) :
    (a.numerator*(b.denominator:ℤ)).natAbs≤2^(A+B) ∧
      (b.numerator*(a.denominator:ℤ)).natAbs≤2^(A+B) := by
  constructor
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast,pow_add] using Nat.mul_le_mul ha.2 hb.1
  · have h:=Nat.mul_le_mul hb.2 ha.1
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,pow_add,Nat.mul_comm] using h

end CircuitRecursion
