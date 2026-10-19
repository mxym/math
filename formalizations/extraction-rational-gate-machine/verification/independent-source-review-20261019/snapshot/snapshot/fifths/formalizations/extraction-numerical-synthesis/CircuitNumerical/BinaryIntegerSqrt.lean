import CircuitNumerical.RootTraceBudgets

namespace CircuitRecursion

/-- A digit-by-digit base-four square-root program. The recursive call
processes `n/4`; each step chooses between the two possible next binary root
digits by an exact integer square comparison. -/
def binarySqrtDigits : ℕ → ℕ → ℕ
  | 0,_ => 0
  | fuel+1,n =>
    let s:=binarySqrtDigits fuel (n/4)
    let candidate:=2*s+1
    if candidate*candidate≤n then candidate else 2*s

theorem binarySqrtDigits_correct (fuel n : ℕ) (hn : n<4^fuel) :
    binarySqrtDigits fuel n=Nat.sqrt n := by
  induction fuel generalizing n with
  | zero =>
    have hz : n=0 := by simpa only [pow_zero] using Nat.eq_zero_of_le_zero (by omega : n≤0)
    subst n
    simp only [binarySqrtDigits,Nat.sqrt_zero]
  | succ fuel ih =>
    have hmod:=Nat.mod_lt n (by decide : 0<4)
    have hdecomp:=Nat.mod_add_div n 4
    have hq : n/4<4^fuel := by rw [pow_succ] at hn;omega
    let s:=binarySqrtDigits fuel (n/4)
    have hs : s=Nat.sqrt (n/4) := ih _ hq
    have hlo : s*s≤n/4 := by rw [hs];exact Nat.sqrt_le _
    have hhi : n/4<(s+1)*(s+1) := by rw [hs];exact Nat.lt_succ_sqrt _
    change (if (2*s+1)*(2*s+1)≤n then 2*s+1 else 2*s)=Nat.sqrt n
    split_ifs with hc
    · apply Nat.eq_sqrt.mpr
      constructor
      · exact hc
      · nlinarith
    · apply Nat.eq_sqrt.mpr
      constructor
      · calc
          (2*s)*(2*s)=4*(s*s) := by ring
          _≤4*(n/4) := Nat.mul_le_mul_left 4 hlo
          _≤n := by omega
      · omega

theorem binarySqrtDigits_le_input (fuel n : ℕ) : binarySqrtDigits fuel n≤n := by
  induction fuel generalizing n with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    have hs:=ih (n/4)
    have hq:=Nat.div_mul_le_self n 4
    dsimp only [binarySqrtDigits]
    split_ifs with hc
    · exact (Nat.le_mul_self _).trans hc
    · omega

def binaryIntegerSqrtFuel (n : ℕ) : ℕ := Nat.clog 2 (n+1)+1

def binaryIntegerSqrt (n : ℕ) : ℕ := binarySqrtDigits (binaryIntegerSqrtFuel n) n

theorem binaryIntegerSqrt_eq (n : ℕ) : binaryIntegerSqrt n=Nat.sqrt n := by
  apply binarySqrtDigits_correct
  have hn : n<2^Nat.clog 2 (n+1) := (Nat.lt_succ_self n).trans_le (Nat.le_pow_clog (by decide) (n+1))
  have hp : 2^Nat.clog 2 (n+1)≤4^Nat.clog 2 (n+1) := Nat.pow_le_pow_left (by decide) _
  exact (hn.trans_le hp).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [binaryIntegerSqrtFuel];omega))

theorem binaryIntegerSqrtFuel_bound (n B : ℕ) (hn : n≤2^B) : binaryIntegerSqrtFuel n≤B+2 :=
  commonDenominator_binary_bound n B hn

/-- Six bounded-integer primitives per digit: shift the input by two bits,
shift the partial root, add one, square, compare, and choose the next digit.
This counter is separate from a bit-cost implementation of those primitives. -/
def binarySqrtDigitOperations : ℕ → ℕ
  | 0 => 0
  | fuel+1 => binarySqrtDigitOperations fuel+6

theorem binarySqrtDigitOperations_eq (fuel : ℕ) : binarySqrtDigitOperations fuel=6*fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [binarySqrtDigitOperations,ih];omega

theorem binaryIntegerSqrt_operations (n B : ℕ) (hn : n≤2^B) :
    binarySqrtDigitOperations (binaryIntegerSqrtFuel n)≤6*(B+2) := by
  rw [binarySqrtDigitOperations_eq]
  exact Nat.mul_le_mul_left 6 (binaryIntegerSqrtFuel_bound n B hn)

/-- All input and temporary magnitudes of the digit program, including the
candidate square which can exceed the input. -/
def binarySqrtOperandTrace : ℕ → ℕ → List ℕ
  | 0,n => [n]
  | fuel+1,n =>
    let s:=binarySqrtDigits fuel (n/4)
    [n,n/4,s,2*s,2*s+1,(2*s+1)*(2*s+1)]++binarySqrtOperandTrace fuel (n/4)

theorem binarySqrtOperandTrace_height (fuel n B : ℕ) (hn : n≤2^B)
    (x : ℕ) (hx : x∈binarySqrtOperandTrace fuel n) : x≤2^(2*B+2) := by
  induction fuel generalizing n x with
  | zero =>
    have he : x=n := by simpa only [binarySqrtOperandTrace,List.mem_singleton] using hx
    subst x
    exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))
  | succ fuel ih =>
    let s:=binarySqrtDigits fuel (n/4)
    have hs : s≤n/4 := binarySqrtDigits_le_input fuel (n/4)
    have hq : n/4≤n := Nat.div_le_self n 4
    have hmul:=Nat.div_mul_le_self n 4
    have htwice : 2*s≤n := by omega
    have hc : 2*s+1≤2^(B+1) := by
      rw [pow_succ]
      have hp : 1≤2^B := Nat.one_le_pow _ _ (by decide)
      omega
    have hc2 : (2*s+1)*(2*s+1)≤2^(2*B+2) := by
      have h:=Nat.mul_le_mul hc hc
      rw [← pow_add] at h
      convert h using 1 <;> congr 1 <;> omega
    have hp : 2^B≤2^(2*B+2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp1 : 2^(B+1)≤2^(2*B+2) := Nat.pow_le_pow_right (by decide) (by omega)
    change x∈[n,n/4,s,2*s,2*s+1,(2*s+1)*(2*s+1)]++binarySqrtOperandTrace fuel (n/4) at hx
    rcases List.mem_append.mp hx with hhere|hbelow
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hhere
      rcases hhere with rfl|rfl|rfl|rfl|rfl|rfl
      · exact hn.trans hp
      · exact (hq.trans hn).trans hp
      · exact ((hs.trans hq).trans hn).trans hp
      · exact (htwice.trans hn).trans hp
      · exact hc.trans hp1
      · exact hc2
    · exact ih (n/4) (hq.trans hn) x hbelow

theorem binaryIntegerSqrt_operandTrace_height (n B : ℕ) (hn : n≤2^B)
    (x : ℕ) (hx : x∈binarySqrtOperandTrace (binaryIntegerSqrtFuel n) n) : x≤2^(2*B+2) :=
  binarySqrtOperandTrace_height _ n B hn x hx

end CircuitRecursion
