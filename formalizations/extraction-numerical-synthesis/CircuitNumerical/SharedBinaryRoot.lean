import CircuitNumerical.RawOperationGrowth

namespace CircuitRecursion

/-- One stored numerator, division fuel, quotient, root fuel and root value.
The annotation uses those same stored fuels and never reruns division to
recover the quotient. Computing the annotation's ordinary integer arithmetic
is still separate from the charged value-subprogram primitive semantics. -/
def IntegerScalar.sharedBinaryRoot (a : IntegerScalar) (p : ℕ) : ScalarIntegerEvaluation :=
  let numerator:=a.numerator.toNat <<< (2*p)
  let divisionFuel:=binaryIntegerSqrtFuel numerator
  let divided:=binaryDivDigits a.denominator divisionFuel numerator
  let quotient:=divided.1
  let rootFuel:=binaryIntegerSqrtFuel quotient
  let rootValue:=binarySqrtDigits rootFuel quotient
  ⟨⟨(rootValue:ℤ),expressionPowerTwo p,by rw [expressionPowerTwo_eq];positivity⟩,
    10*divisionFuel+1+6*rootFuel+4⟩

theorem IntegerScalar.sharedBinaryRoot_quotient (a : IntegerScalar) (p : ℕ) :
    (binaryDivDigits a.denominator (binaryIntegerSqrtFuel (a.numerator.toNat <<< (2*p)))
      (a.numerator.toNat <<< (2*p))).1=
      binaryIntegerDiv (a.numerator.toNat <<< (2*p)) a.denominator := by
  simp only [binaryIntegerDiv,binaryIntegerDivMod,ite_eq_right a.denominator_pos.ne']

theorem IntegerScalar.sharedBinaryRoot_value (a : IntegerScalar) (p : ℕ) :
    (a.sharedBinaryRoot p).value=a.binaryRoot p := by
  simp only [sharedBinaryRoot,binaryRoot,sharedBinaryRoot_quotient]
  rfl

theorem IntegerScalar.sharedBinaryRoot_charge (a : IntegerScalar) (p : ℕ) :
    (a.sharedBinaryRoot p).rootCharge=a.binaryRootPrimitiveOperations p := by
  simp only [sharedBinaryRoot,sharedBinaryRoot_quotient,binaryRootPrimitiveOperations,
    binaryDivDigitOperations,binarySqrtDigitOperations_eq]

theorem IntegerScalar.sharedBinaryRoot_eq (a : IntegerScalar) (p : ℕ) :
    a.sharedBinaryRoot p=⟨a.binaryRoot p,a.binaryRootPrimitiveOperations p⟩ := by
  have hv:=sharedBinaryRoot_value a p
  have hc:=sharedBinaryRoot_charge a p
  cases h : a.sharedBinaryRoot p
  simp only [h] at hv hc
  cases hv
  cases hc
  rfl

theorem IntegerScalar.sharedBinaryRoot_correct (a : IntegerScalar) (p : ℕ) :
    (a.sharedBinaryRoot p).value.value=rationalSqrtApprox a.value p := by
  rw [sharedBinaryRoot_value,binaryRoot_eq]
  exact root_value a p

theorem IntegerScalar.sharedBinaryRoot_height (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) : IntegerScalarHeight (a.sharedBinaryRoot p).value (A+2*p) := by
  rw [sharedBinaryRoot_value,binaryRoot_eq]
  exact root_height a A p ha

theorem IntegerScalar.sharedBinaryRoot_charge_bound (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) : (a.sharedBinaryRoot p).rootCharge≤16*(A+2*p+2)+5 := by
  rw [sharedBinaryRoot_charge]
  exact binaryRootPrimitiveOperations_bound a A p ha

end CircuitRecursion
