import CircuitNumerical.BinaryWordAddition

namespace CircuitRecursion

/-- Schoolbook multiplication on least-significant-bit-first words. Only
Boolean branching, a leading zero bit and the proved full-adder are used. -/
def binaryMultiplyWord (as : List Bool) : List Bool → List Bool
  | [] => []
  | false::bs => false::binaryMultiplyWord as bs
  | true::bs => binaryAddCarry as (false::binaryMultiplyWord as bs) false

theorem binaryMultiplyWord_value (as bs : List Bool) :
    binaryWordValue (binaryMultiplyWord as bs)=binaryWordValue as*binaryWordValue bs := by
  induction bs with
  | nil => simp only [binaryMultiplyWord,binaryWordValue,mul_zero]
  | cons b bs ih =>
    cases b
    · simp only [binaryMultiplyWord,binaryWordValue,binaryBitValue,zero_add,ih]
      ring
    · simp only [binaryMultiplyWord,binaryAddCarry_value,binaryWordValue,binaryBitValue,zero_add,add_zero,ih]
      ring

theorem binaryMultiplyWord_length (as bs : List Bool) :
    (binaryMultiplyWord as bs).length≤as.length+2*bs.length := by
  induction bs with
  | nil => exact Nat.zero_le _
  | cons b bs ih =>
    cases b
    · simp only [binaryMultiplyWord,List.length_cons]
      omega
    · have ha:=binaryAddCarry_length as (false::binaryMultiplyWord as bs) false
      simp only [List.length_cons] at ha
      change (binaryAddCarry as (false::binaryMultiplyWord as bs) false).length≤as.length+2*(bs.length+1)
      omega

def binaryMultiplyBitOperations (as : List Bool) : List Bool → ℕ
  | [] => 1
  | false::bs => binaryMultiplyBitOperations as bs+3
  | true::bs => binaryMultiplyBitOperations as bs+
      binaryAddBitOperations as (false::binaryMultiplyWord as bs) false+3

theorem binaryMultiplyBitOperations_bound (as bs : List Bool) :
    binaryMultiplyBitOperations as bs≤24*(bs.length+1)*(as.length+2*bs.length+1) := by
  induction bs with
  | nil =>
    simp only [binaryMultiplyBitOperations,List.length_nil]
    omega
  | cons b bs ih =>
    cases b
    · simp only [binaryMultiplyBitOperations,List.length_cons]
      nlinarith
    · have hlen:=binaryMultiplyWord_length as bs
      have hadd:=binaryAddBitOperations_bound as (false::binaryMultiplyWord as bs) false
      have hadd' : binaryAddBitOperations as (false::binaryMultiplyWord as bs) false≤
          12*(as.length+2*bs.length+2) := by
        apply hadd.trans
        apply Nat.mul_le_mul_left 12
        simp only [List.length_cons]
        omega
      simp only [binaryMultiplyBitOperations,List.length_cons]
      nlinarith

theorem binaryMultiplyBitOperations_uniform (as bs : List Bool) (B : ℕ)
    (ha : as.length≤B) (hb : bs.length≤B) :
    binaryMultiplyBitOperations as bs≤72*(B+1)^2 := by
  have h:=binaryMultiplyBitOperations_bound as bs
  have hp : as.length+2*bs.length+1≤3*(B+1) := by omega
  have hprod:=Nat.mul_le_mul (by omega : bs.length+1≤B+1) hp
  have hm:=Nat.mul_le_mul_left 24 hprod
  exact h.trans (by nlinarith)

end CircuitRecursion
