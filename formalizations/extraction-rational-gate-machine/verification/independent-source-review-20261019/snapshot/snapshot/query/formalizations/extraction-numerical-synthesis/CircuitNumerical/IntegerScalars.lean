import CircuitNumerical.IntegerPackets
import Mathlib.Algebra.Order.Floor.Semifield

namespace CircuitRecursion

structure IntegerScalar where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0<denominator

def IntegerScalar.value (a : IntegerScalar) : ℚ := (a.numerator:ℚ)/(a.denominator:ℚ)
def IntegerScalar.ofInt (n : ℤ) : IntegerScalar := ⟨n,1,by decide⟩
def IntegerScalar.add (a b : IntegerScalar) : IntegerScalar :=
  ⟨a.numerator*b.denominator+b.numerator*a.denominator,a.denominator*b.denominator,
    Nat.mul_pos a.denominator_pos b.denominator_pos⟩
def IntegerScalar.neg (a : IntegerScalar) : IntegerScalar :=
  ⟨-a.numerator,a.denominator,a.denominator_pos⟩
def IntegerScalar.mul (a b : IntegerScalar) : IntegerScalar :=
  ⟨a.numerator*b.numerator,a.denominator*b.denominator,
    Nat.mul_pos a.denominator_pos b.denominator_pos⟩
def IntegerScalar.inv (a : IntegerScalar) : IntegerScalar :=
  if h : a.numerator=0 then ofInt 0 else
    ⟨a.numerator.sign*a.denominator,a.numerator.natAbs,Int.natAbs_pos.mpr h⟩

theorem IntegerScalar.add_value (a b : IntegerScalar) : (a.add b).value=a.value+b.value := by
  have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
  have hb : (b.denominator:ℚ)≠0 := by exact_mod_cast b.denominator_pos.ne'
  simp only [add,value,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp

theorem IntegerScalar.neg_value (a : IntegerScalar) : a.neg.value= -a.value := by
  simp only [neg,value,Int.cast_neg]
  ring

theorem IntegerScalar.mul_value (a b : IntegerScalar) : (a.mul b).value=a.value*b.value := by
  simp only [mul,value,Int.cast_mul,Nat.cast_mul]
  ring

theorem IntegerScalar.inv_value (a : IntegerScalar) : a.inv.value=a.value⁻¹ := by
  by_cases h : a.numerator=0
  · simp [inv,h,ofInt,value]
  · have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
    have hn : (a.numerator:ℚ)≠0 := by exact_mod_cast h
    have habs : (a.numerator.natAbs:ℚ)≠0 := by exact_mod_cast (Int.natAbs_pos.mpr h).ne'
    have hs : (a.numerator.sign:ℚ)*(a.numerator:ℚ)=(a.numerator.natAbs:ℚ) := by
      have h := congrArg (fun x : ℤ => (x:ℚ)) (Int.sign_mul_self a.numerator)
      simpa only [Int.cast_mul,Int.cast_natCast] using h
    simp only [inv,dif_neg h,value,Int.cast_mul,Int.cast_natCast]
    field_simp
    nlinarith [congrArg (fun x : ℚ => x*a.denominator) hs]

def IntegerScalarHeight (a : IntegerScalar) (B : ℕ) : Prop :=
  a.denominator≤2^B ∧ a.numerator.natAbs≤2^B

theorem IntegerScalar.add_height (a b : IntegerScalar) (A B : ℕ)
    (ha : IntegerScalarHeight a A) (hb : IntegerScalarHeight b B) :
    IntegerScalarHeight (a.add b) (A+B+1) := by
  have he : 2^A*2^B+2^A*2^B=2^(A+B+1) := by rw [pow_succ,pow_add];ring
  have hd := Nat.mul_le_mul ha.1 hb.1
  have hn1 := Nat.mul_le_mul ha.2 hb.1
  have hn2 := Nat.mul_le_mul hb.2 ha.1
  constructor
  · change a.denominator*b.denominator≤_
    nlinarith
  · change (a.numerator*(b.denominator:ℤ)+b.numerator*a.denominator).natAbs≤_
    have h := Int.natAbs_add_le (a.numerator*(b.denominator:ℤ)) (b.numerator*(a.denominator:ℤ))
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at h
    nlinarith

theorem IntegerScalar.neg_height (a : IntegerScalar) (A : ℕ) (ha : IntegerScalarHeight a A) :
    IntegerScalarHeight a.neg A := by
  simpa only [IntegerScalarHeight,neg,Int.natAbs_neg] using ha

theorem IntegerScalar.mul_height (a b : IntegerScalar) (A B : ℕ)
    (ha : IntegerScalarHeight a A) (hb : IntegerScalarHeight b B) :
    IntegerScalarHeight (a.mul b) (A+B) := by
  constructor
  · simpa only [mul,pow_add] using Nat.mul_le_mul ha.1 hb.1
  · simpa only [mul,Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha.2 hb.2

theorem IntegerScalar.inv_height (a : IntegerScalar) (A : ℕ) (ha : IntegerScalarHeight a A) :
    IntegerScalarHeight a.inv A := by
  unfold inv
  split_ifs with h
  · constructor
    · exact Nat.one_le_pow _ _ (by decide)
    · exact Nat.zero_le _
  · constructor
    · exact ha.2
    · change (a.numerator.sign*(a.denominator:ℤ)).natAbs≤_
      simpa only [Int.natAbs_mul,Int.natAbs_sign_of_ne_zero h,Int.natAbs_natCast,one_mul] using ha.1

/-- Integer division and integer square root, with shifts providing the
dyadic scaling. No real or rational square root is evaluated. -/
def IntegerScalar.root (a : IntegerScalar) (p : ℕ) : IntegerScalar :=
  ⟨(Nat.sqrt ((a.numerator.toNat <<< (2*p))/a.denominator):ℤ),expressionPowerTwo p,
    by rw [expressionPowerTwo_eq];positivity⟩

theorem IntegerScalar.max_value (a : IntegerScalar) :
    max 0 a.value=(a.numerator.toNat:ℚ)/(a.denominator:ℚ) := by
  have hd : (0:ℚ)<a.denominator := by exact_mod_cast a.denominator_pos
  by_cases h : 0≤a.numerator
  · have hv : 0≤a.value := div_nonneg (by exact_mod_cast h) hd.le
    rw [max_eq_right hv]
    have he := congrArg (fun x : ℤ => (x:ℚ)) (Int.toNat_of_nonneg h)
    simp only [Int.cast_natCast] at he
    exact congrArg (fun x : ℚ => x/(a.denominator:ℚ)) he.symm
  · have hn : a.numerator≤0 := le_of_lt (lt_of_not_ge h)
    have hv : a.value≤0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn) hd.le
    rw [max_eq_left hv,Int.toNat_eq_zero.mpr hn]
    simp

theorem IntegerScalar.root_value (a : IntegerScalar) (p : ℕ) :
    (a.root p).value=rationalSqrtApprox a.value p := by
  have he : max 0 a.value*((2:ℚ)^p)^2=
      ((a.numerator.toNat*2^(2*p):ℕ):ℚ)/(a.denominator:ℚ) := by
    rw [max_value]
    push_cast
    have hp : (2:ℚ)^(2*p)=((2:ℚ)^p)^2 := by rw [← pow_mul,Nat.mul_comm 2 p]
    rw [hp]
    ring
  have hf : ⌊max 0 a.value*((2:ℚ)^p)^2⌋₊=
      (a.numerator.toNat*2^(2*p))/a.denominator := by
    rw [he,Nat.floor_div_natCast,Nat.floor_natCast]
  change (((Nat.sqrt ((a.numerator.toNat <<< (2*p))/a.denominator):ℤ):ℚ)/
    (expressionPowerTwo p:ℚ))=rationalSqrtApprox a.value p
  rw [rationalSqrtApprox,hf,expressionPowerTwo_eq]
  simp only [Nat.shiftLeft_eq,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat]

theorem IntegerScalar.root_height (a : IntegerScalar) (A p : ℕ) (ha : IntegerScalarHeight a A) :
    IntegerScalarHeight (a.root p) (A+2*p) := by
  have hnat : a.numerator.toNat≤a.numerator.natAbs := by
    cases a.numerator <;> simp
  have hnum := Nat.mul_le_mul_right (2^(2*p)) (hnat.trans ha.2)
  rw [← pow_add] at hnum
  constructor
  · change expressionPowerTwo p≤_
    rw [expressionPowerTwo_eq]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · change (Nat.sqrt ((a.numerator.toNat <<< (2*p))/a.denominator))≤_
    rw [Nat.shiftLeft_eq]
    exact (Nat.sqrt_le_self _).trans ((Nat.div_le_self _ _).trans hnum)

end CircuitRecursion
