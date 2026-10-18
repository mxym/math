import EffectiveEncoding.ProviderTerminal
import CircuitNumerical.RawIntegerPacketExpressions

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- A raw integer fraction. No canonical rational is constructed by this
runtime function. Its denominator proof is erased during execution. -/
def integerFraction (N D : ℕ) (hD : 0<D) : IntegerScalar := ⟨(N:ℤ),D,hD⟩

def integerHalf : IntegerScalar := ⟨1,2,by decide⟩

theorem integerScalar_ext_value (a b : IntegerScalar) (hv : a.value=b.value)
    (hd : a.denominator=b.denominator) : a=b := by
  have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
  change (a.numerator:ℚ)/(a.denominator:ℚ)=(b.numerator:ℚ)/(b.denominator:ℚ) at hv
  rw [← hd] at hv
  have hn : a.numerator=b.numerator := by exact_mod_cast (div_left_inj' ha).mp hv
  cases a;cases b;cases hd;cases hn;rfl

theorem integerLiteral_zero : IntegerScalar.ofRat 0=IntegerScalar.ofInt 0 := by
  simp [IntegerScalar.ofRat,IntegerScalar.ofInt]

theorem integerLiteral_one : IntegerScalar.ofRat 1=IntegerScalar.ofInt 1 := by
  simp [IntegerScalar.ofRat,IntegerScalar.ofInt]

theorem integerLiteral_half : IntegerScalar.ofRat (1/2)=integerHalf := by
  apply integerScalar_ext_value
  · rw [IntegerScalar.ofRat_value]
    norm_num [integerHalf,IntegerScalar.value]
  · norm_num [IntegerScalar.ofRat,integerHalf]

theorem integerLiteral_halfInv : IntegerScalar.ofRat (2:ℚ)⁻¹=integerHalf := by
  simpa only [one_div] using integerLiteral_half

/-- The rounded square-root payload depends only on the input value and the
requested dyadic precision, even for noncanonical integer fractions. -/
theorem integerRoot_congr_value (a b : IntegerScalar) (hv : a.value=b.value) (p : ℕ) :
    a.binaryRoot p=b.root p := by
  apply integerScalar_ext_value
  · rw [IntegerScalar.binaryRoot_eq,IntegerScalar.root_value,IntegerScalar.root_value,hv]
  · rfl

def rawAtomCos (a : AngleAtom) (p : ℕ) : IntegerScalar :=
  match a with
  | .pi => IntegerScalar.ofInt (-1)
  | .merge A B j => if h : j=0 ∨ A+B=0 then IntegerScalar.ofInt 1 else
      (integerFraction A (A+B) (by omega)).binaryRoot (p+1)

def rawAtomSin (a : AngleAtom) (p : ℕ) : IntegerScalar :=
  match a with
  | .pi => IntegerScalar.ofInt 0
  | .merge A B j => if h : j=0 ∨ A+B=0 then IntegerScalar.ofInt 0 else
      (integerFraction B (A+B) (by omega)).binaryRoot (p+1)

theorem rawAtomCos_eq (a : AngleAtom) (p : ℕ) :
    rawAtomCos a p=(a.cosExpression p).integerRun := by
  cases a with
  | pi => rfl
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simp only [rawAtomCos,AngleAtom.cosExpression,if_pos h,dite_eq_left h,constantExpression,ScalarExpression.integerRun,integerLiteral_zero,integerLiteral_one]
    · simp only [rawAtomCos,AngleAtom.cosExpression,if_neg h,dite_eq_right h,expressionSqrt,constantExpression,
        ScalarExpression.integerRun]
      apply integerRoot_congr_value
      rw [IntegerScalar.ofRat_value]
      simp only [integerFraction,IntegerScalar.value,Int.cast_natCast,Nat.cast_add]

theorem rawAtomSin_eq (a : AngleAtom) (p : ℕ) :
    rawAtomSin a p=(a.sinExpression p).integerRun := by
  cases a with
  | pi => rfl
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simp only [rawAtomSin,AngleAtom.sinExpression,if_pos h,dite_eq_left h,constantExpression,ScalarExpression.integerRun,integerLiteral_zero,integerLiteral_one]
    · simp only [rawAtomSin,AngleAtom.sinExpression,if_neg h,dite_eq_right h,expressionSqrt,constantExpression,
        ScalarExpression.integerRun]
      apply integerRoot_congr_value
      rw [IntegerScalar.ofRat_value]
      simp only [integerFraction,IntegerScalar.value,Int.cast_natCast,Nat.cast_add]

abbrev RawScalarOracle := ℕ → IntegerScalar

def rawHalfCos : ℕ → RawScalarOracle → RawScalarOracle
  | 0,f => f
  | n+1,f => fun p => (integerHalf.mul ((IntegerScalar.ofInt 1).add
      (rawHalfCos n f (2*p+2)))).binaryRoot (p+1)

def rawHalfSin : ℕ → RawScalarOracle → RawScalarOracle → RawScalarOracle
  | 0,_,g => g
  | n+1,f,_ => fun p => (rawHalfCos n f (2*p+2)).meanMinus.binaryRoot (p+1)

theorem rawHalfCos_eq (n : ℕ) (f : RawScalarOracle) (g : ScalarExpressionOracle)
    (h : ∀ p,f p=(g p).integerRun) (p : ℕ) :
    rawHalfCos n f p=(halfCosExpression n g p).integerRun := by
  induction n generalizing p with
  | zero => exact h p
  | succ n ih =>
    simp only [rawHalfCos,halfCosExpression,expressionSqrt,meanPlusExpression,
      ScalarExpression.integerRun,IntegerScalar.binaryRoot_eq,ih,integerLiteral_half,integerLiteral_one]

theorem rawHalfSin_eq (n : ℕ) (f g : RawScalarOracle) (a b : ScalarExpressionOracle)
    (hf : ∀ p,f p=(a p).integerRun) (hg : ∀ p,g p=(b p).integerRun) (p : ℕ) :
    rawHalfSin n f g p=(halfSinExpression n a b p).integerRun := by
  cases n with
  | zero => exact hg p
  | succ n =>
    simp only [rawHalfSin,halfSinExpression,expressionSqrt,expressionMeanMinus,
      ScalarExpression.integerRun,IntegerScalar.binaryRoot_eq,rawHalfCos_eq n f a hf]

def AngleCode.rawCos (a : AngleCode) : RawScalarOracle := rawHalfCos a.halvings (rawAtomCos a.atom)

def AngleCode.rawSin (a : AngleCode) : RawScalarOracle := fun p =>
  let s := rawHalfSin a.halvings (rawAtomCos a.atom) (rawAtomSin a.atom) p
  if a.negative then s.neg else s

theorem AngleCode.rawCos_eq (a : AngleCode) (p : ℕ) :
    a.rawCos p=(a.cosExpression p).integerRun :=
  rawHalfCos_eq a.halvings _ _ (rawAtomCos_eq a.atom) p

theorem AngleCode.rawSin_eq (a : AngleCode) (p : ℕ) :
    a.rawSin p=(a.sinExpression p).integerRun := by
  cases hn : a.negative <;> simp only [rawSin,sinExpression,hn,Bool.false_eq_true,ite_false,ite_true,
    expressionNeg,ScalarExpression.integerRun,rawHalfSin_eq a.halvings _ _ _ _
      (rawAtomCos_eq a.atom) (rawAtomSin_eq a.atom)]

def rawPhaseCos (a b : AngleCode) (p : ℕ) : IntegerScalar :=
  (((a.half 1).rawCos (p+3)).mul ((b.half 1).rawCos (p+3))).add
    (((a.half 1).rawSin (p+3)).mul ((b.half 1).rawSin (p+3)))

def rawPhaseSin (a b : AngleCode) (p : ℕ) : IntegerScalar :=
  (((a.half 1).rawSin (p+3)).mul ((b.half 1).rawCos (p+3))).add
    (((a.half 1).rawCos (p+3)).mul ((b.half 1).rawSin (p+3))).neg

theorem rawPhaseCos_eq (a b : AngleCode) (p : ℕ) :
    rawPhaseCos a b p=(phaseCosExpression a b p).integerRun := by
  simp only [rawPhaseCos,phaseCosExpression,expressionAdd,expressionMul,ScalarExpression.integerRun,
    Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,AngleCode.rawCos_eq,AngleCode.rawSin_eq]

theorem rawPhaseSin_eq (a b : AngleCode) (p : ℕ) :
    rawPhaseSin a b p=(phaseSinExpression a b p).integerRun := by
  simp only [rawPhaseSin,phaseSinExpression,expressionAdd,expressionMul,expressionNeg,ScalarExpression.integerRun,
    Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,AngleCode.rawCos_eq,AngleCode.rawSin_eq]

/-- The complete actual target provider uses raw integer literals, arithmetic,
binary long division and binary digit sqrt. Rational values occur only in
its correctness theorems, never in this runtime definition. -/
def SingleCode.rawPacket : SingleCode → ℕ → IntegerPacket
  | .hadamard,p => IntegerPacket.ofScalars ![IntegerScalar.ofInt 0,
      (integerHalf.binaryRoot (p+1)).neg,IntegerScalar.ofInt 0,(integerHalf.binaryRoot (p+1)).neg]
  | .yBasis,_ => IntegerPacket.ofScalars ![integerHalf,integerHalf,integerHalf,integerHalf]
  | .phase a b,p => IntegerPacket.ofScalars ![rawPhaseCos a b p,rawPhaseSin a b p,
      IntegerScalar.ofInt 0,IntegerScalar.ofInt 0]
  | .inverse u,p => (u.rawPacket p).inverse

/-- Equality of the full integer payload, rather than only equality after
converting to rational values. This transports the proved actual heights. -/
theorem SingleCode.rawPacket_eq (u : SingleCode) (p : ℕ) : u.rawPacket p=u.integerPacket p := by
  induction u with
  | hadamard =>
    simp only [rawPacket,integerPacket,packetExpression,PacketExpression.integerRun,IntegerScalar.binaryRoot_eq]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> simp [ScalarExpression.integerRun,integerLiteral_zero,integerLiteral_halfInv]
  | yBasis =>
    simp only [rawPacket,integerPacket,packetExpression,PacketExpression.integerRun]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> simp [ScalarExpression.integerRun,integerLiteral_halfInv]
  | phase a b =>
    simp only [rawPacket,integerPacket,packetExpression,PacketExpression.integerRun]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i
    · exact rawPhaseCos_eq a b p
    · exact rawPhaseSin_eq a b p
    · rfl
    · rfl
  | inverse u ih =>
    simp only [rawPacket,integerPacket,packetExpression,expressionPacketInverse,PacketExpression.integerRun]
    exact congrArg IntegerPacket.inverse ih

theorem SingleCode.rawPacket_value (u : SingleCode) (p : ℕ) :
    (u.rawPacket p).value=u.quaternionOracle p := by rw [rawPacket_eq,integerPacket_value]

theorem extractionCode_rawPacket_height {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    IntegerPacketHeight (u.rawPacket p) (1000000*(k+3)^7*(p+5)) := by
  rw [SingleCode.rawPacket_eq]
  exact extractionCode_provider_integerHeight hu p

end EffectiveEncoding
