import CircuitNumerical.RationalCacheBudgets

namespace CircuitRecursion

/-- The integer values used by the existing root implementation: the raw
input, clipping, shift counts, shifted numerator, quotient, root, and output
denominator. The shift and division expressions are the actual ones in
`IntegerScalar.root`. -/
def IntegerScalar.rootOperandTrace (a : IntegerScalar) (p : ℕ) : List ℕ :=
  [a.numerator.natAbs,a.denominator,a.numerator.toNat,p,2*p,
    expressionPowerTwo p,a.numerator.toNat <<< (2*p),
    (a.numerator.toNat <<< (2*p))/a.denominator,
    Nat.sqrt ((a.numerator.toNat <<< (2*p))/a.denominator)]

def integerStoppingThresholdOperandTrace (t : ℕ) : List ℕ :=
  [2,2*t,expressionPowerTwo (2*t)]

theorem natural_le_power_two (n : ℕ) : n≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    have hp : 1≤2^n := Nat.one_le_pow _ _ (by decide)
    omega

theorem IntegerScalar.rootOperandTrace_height (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) :
    ∀ x,x∈a.rootOperandTrace p → x≤2^(A+2*p) := by
  have hpow : 2^A≤2^(A+2*p) := Nat.pow_le_pow_right (by decide) (by omega)
  have hnat : a.numerator.toNat≤a.numerator.natAbs := by cases a.numerator <;> simp
  have hshift : a.numerator.toNat <<< (2*p)≤2^(A+2*p) := by
    rw [Nat.shiftLeft_eq,pow_add]
    exact Nat.mul_le_mul_right _ (hnat.trans ha.2)
  have hdiv : (a.numerator.toNat <<< (2*p))/a.denominator≤2^(A+2*p) :=
    (Nat.div_le_self _ _).trans hshift
  have hprecision : 2*p≤2^(A+2*p) := (by omega : 2*p≤A+2*p).trans (natural_le_power_two _)
  intro x hx
  simp only [rootOperandTrace,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ha.2.trans hpow
  · exact ha.1.trans hpow
  · exact (hnat.trans ha.2).trans hpow
  · omega
  · exact hprecision
  · rw [expressionPowerTwo_eq]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact hshift
  · exact hdiv
  · exact (Nat.sqrt_le_self _).trans hdiv

theorem integerStoppingThresholdOperandTrace_height (t : ℕ) :
    ∀ x,x∈integerStoppingThresholdOperandTrace t → x≤2^(2*t+1) := by
  intro x hx
  simp only [integerStoppingThresholdOperandTrace,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · have h:=Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 1≤2*t+1)
    simpa only [pow_one] using h
  · exact (natural_le_power_two _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [expressionPowerTwo_eq]
    exact Nat.pow_le_pow_right (by decide) (by omega)

theorem IntegerScalar.rootOperandTrace_binaryLength (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) (x : ℕ) (hx : x∈a.rootOperandTrace p) :
    Nat.clog 2 (x+1)≤A+2*p+1 := by
  have h:=commonDenominator_binary_bound x (A+2*p) (rootOperandTrace_height a A p ha x hx)
  omega

theorem IntegerScalar.root_numerator_in_operandTrace (a : IntegerScalar) (p : ℕ) :
    (a.root p).numerator.natAbs∈a.rootOperandTrace p := by
  simp [root,rootOperandTrace]

theorem IntegerScalar.root_denominator_in_operandTrace (a : IntegerScalar) (p : ℕ) :
    (a.root p).denominator∈a.rootOperandTrace p := by
  simp [root,rootOperandTrace]

end CircuitRecursion
