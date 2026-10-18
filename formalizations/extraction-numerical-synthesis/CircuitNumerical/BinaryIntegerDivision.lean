import CircuitNumerical.BinaryIntegerSqrt

namespace CircuitRecursion

/-- Binary long division. One recursion processes the leading digits `a/2`;
the last bit updates the remainder and chooses the next quotient bit. -/
def binaryDivDigits (b : ℕ) : ℕ → ℕ → ℕ×ℕ
  | 0,_ => (0,0)
  | fuel+1,a =>
    let previous:=binaryDivDigits b fuel (a/2)
    let remainder:=2*previous.2+a%2
    if b≤remainder then (2*previous.1+1,remainder-b) else (2*previous.1,remainder)

theorem binaryDivDigits_invariant (b fuel a : ℕ) (hb : 0<b) (ha : a<2^fuel) :
    (binaryDivDigits b fuel a).2+b*(binaryDivDigits b fuel a).1=a ∧
      (binaryDivDigits b fuel a).2<b := by
  induction fuel generalizing a with
  | zero =>
    have hz : a=0 := by
      simp only [pow_zero] at ha
      omega
    subst a
    simp only [binaryDivDigits,zero_mul,add_zero]
    exact ⟨rfl,hb⟩
  | succ fuel ih =>
    have hmod:=Nat.mod_lt a (by decide : 0<2)
    have hdecomp:=Nat.mod_add_div a 2
    have hhalf : a/2<2^fuel := by rw [pow_succ] at ha;omega
    let previous:=binaryDivDigits b fuel (a/2)
    have hi : previous.2+b*previous.1=a/2 ∧ previous.2<b := ih _ hhalf
    have hstep : 2*previous.2+a%2+b*(2*previous.1)=a := by nlinarith [hi.1]
    have hrange : 2*previous.2+a%2<2*b := by omega
    change (if b≤2*previous.2+a%2 then (2*previous.1+1,2*previous.2+a%2-b)
      else (2*previous.1,2*previous.2+a%2)).2+
      b*(if b≤2*previous.2+a%2 then (2*previous.1+1,2*previous.2+a%2-b)
        else (2*previous.1,2*previous.2+a%2)).1=a ∧
      (if b≤2*previous.2+a%2 then (2*previous.1+1,2*previous.2+a%2-b)
        else (2*previous.1,2*previous.2+a%2)).2<b
    split_ifs with hc
    · simp only [Prod.fst,Prod.snd]
      have hsub:=Nat.sub_add_cancel hc
      constructor
      · nlinarith
      · omega
    · simp only [Prod.fst,Prod.snd]
      exact ⟨hstep,by omega⟩

theorem binaryDivDigits_correct (b fuel a : ℕ) (hb : 0<b) (ha : a<2^fuel) :
    binaryDivDigits b fuel a=(a/b,a%b) := by
  have h: a/b=(binaryDivDigits b fuel a).1 ∧ a%b=(binaryDivDigits b fuel a).2 :=
    (Nat.div_mod_unique hb).mpr (binaryDivDigits_invariant b fuel a hb ha)
  exact Prod.ext h.1.symm h.2.symm

def binaryIntegerDivMod (a b : ℕ) : ℕ×ℕ :=
  if b=0 then (0,a) else binaryDivDigits b (binaryIntegerSqrtFuel a) a

theorem binaryIntegerDiv_input_fuel (a : ℕ) : a<2^binaryIntegerSqrtFuel a := by
  have ha : a<2^Nat.clog 2 (a+1) := (Nat.lt_succ_self a).trans_le (Nat.le_pow_clog (by decide) (a+1))
  exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [binaryIntegerSqrtFuel];omega))

theorem binaryIntegerDivMod_eq (a b : ℕ) : binaryIntegerDivMod a b=(a/b,a%b) := by
  by_cases hb : b=0
  · subst b
    simp [binaryIntegerDivMod]
  · rw [binaryIntegerDivMod,ite_eq_right hb]
    apply binaryDivDigits_correct b _ a (Nat.pos_of_ne_zero hb)
    exact binaryIntegerDiv_input_fuel a

def binaryIntegerDiv (a b : ℕ) : ℕ := (binaryIntegerDivMod a b).1
def binaryIntegerMod (a b : ℕ) : ℕ := (binaryIntegerDivMod a b).2

theorem binaryIntegerDiv_eq (a b : ℕ) : binaryIntegerDiv a b=a/b := by
  simp only [binaryIntegerDiv,binaryIntegerDivMod_eq]
theorem binaryIntegerMod_eq (a b : ℕ) : binaryIntegerMod a b=a%b := by
  simp only [binaryIntegerMod,binaryIntegerDivMod_eq]

/-- A conservative count for shifts, last-bit extraction, additions,
comparison, and subtraction per digit. It does not charge general division
or square root as constant-time primitives. -/
def binaryDivDigitOperations (fuel : ℕ) : ℕ := 10*fuel

theorem binaryIntegerDiv_operations (a B : ℕ) (ha : a≤2^B) :
    binaryDivDigitOperations (binaryIntegerSqrtFuel a)+1≤10*(B+2)+1 := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 (binaryIntegerSqrtFuel_bound a B ha)) 1

def binaryDivOperandTrace (b : ℕ) : ℕ → ℕ → List ℕ
  | 0,a => [a,b]
  | fuel+1,a =>
    let previous:=binaryDivDigits b fuel (a/2)
    let remainder:=2*previous.2+a%2
    [a,b,a/2,a%2,previous.1,previous.2,2*previous.1,2*previous.1+1,
      2*previous.2,remainder,remainder-b]++binaryDivOperandTrace b fuel (a/2)

theorem binaryDivOperandTrace_height (b fuel a B : ℕ) (hb : 0<b)
    (ha : a<2^fuel) (haB : a≤2^B) (hbB : b≤2^B)
    (x : ℕ) (hx : x∈binaryDivOperandTrace b fuel a) : x≤2^(B+2) := by
  induction fuel generalizing a x with
  | zero =>
    simp only [binaryDivOperandTrace,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact haB.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact hbB.trans (Nat.pow_le_pow_right (by decide) (by omega))
  | succ fuel ih =>
    have hmod:=Nat.mod_lt a (by decide : 0<2)
    have hdecomp:=Nat.mod_add_div a 2
    have hhalf : a/2<2^fuel := by rw [pow_succ] at ha;omega
    have hhalfB : a/2≤2^B := (Nat.div_le_self a 2).trans haB
    let previous:=binaryDivDigits b fuel (a/2)
    have hi : previous.2+b*previous.1=a/2 ∧ previous.2<b :=
      binaryDivDigits_invariant b fuel (a/2) hb hhalf
    have hqp : previous.1≤b*previous.1 := by
      simpa using Nat.mul_le_mul_right previous.1 hb
    have hq : previous.1≤a/2 := by omega
    have htwoq : 2*previous.1≤a := by omega
    have hrem : 2*previous.2+a%2<2*b := by omega
    have hp : 2^(B+2)=4*2^B := by rw [pow_add];ring
    have hpowpos : 1≤2^B := Nat.one_le_pow _ _ (by decide)
    have ha2 : a≤2^(B+2) := by rw [hp];omega
    have hb2 : b≤2^(B+2) := by rw [hp];omega
    have hrem2 : 2*previous.2+a%2≤2^(B+2) := by rw [hp];omega
    change x∈[a,b,a/2,a%2,previous.1,previous.2,2*previous.1,2*previous.1+1,
      2*previous.2,2*previous.2+a%2,2*previous.2+a%2-b]++binaryDivOperandTrace b fuel (a/2) at hx
    rcases List.mem_append.mp hx with hhere|hbelow
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hhere
      rcases hhere with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ha2
      · exact hb2
      · exact (Nat.div_le_self _ _).trans ha2
      · rw [hp];omega
      · exact (hq.trans (Nat.div_le_self _ _)).trans ha2
      · omega
      · exact htwoq.trans ha2
      · rw [hp];omega
      · omega
      · exact hrem2
      · exact (Nat.sub_le _ _).trans hrem2
    · exact ih (a/2) hhalf hhalfB x hbelow

end CircuitRecursion
