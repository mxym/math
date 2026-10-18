import CircuitNumerical.IntegerNumericalProgram

namespace CircuitRecursion

theorem IntegerScalar.ofRat_intCast (n : ℤ) : IntegerScalar.ofRat (n:ℚ)=IntegerScalar.ofInt n := by
  simp [IntegerScalar.ofRat,IntegerScalar.ofInt]

theorem IntegerScalar.ofInt_positive_inv (d : ℕ) (hd : 0<d) :
    (IntegerScalar.ofInt (d:ℤ)).inv=⟨1,d,hd⟩ := by
  have hn : (d:ℤ)≠0 := by exact_mod_cast hd.ne'
  have hs : (d:ℤ).sign=1 := Int.sign_eq_one_of_pos (by exact_mod_cast hd)
  simp only [IntegerScalar.inv,IntegerScalar.ofInt,dite_eq_right hn,hs,one_mul,Int.natAbs_natCast]
  norm_num

/-- This embeds only numerator/denominator integers as denominator-one
rational literal data. It never forms the fraction `a.value`. -/
def rawScalarExpression (a : IntegerScalar) : ScalarExpression :=
  .mul (.literal (a.numerator:ℚ)) (.inv (.literal ((a.denominator:ℤ):ℚ)))

theorem rawScalarExpression_integerProgramRun (a : IntegerScalar) :
    (rawScalarExpression a).integerProgramRun=a := by
  simp only [rawScalarExpression,ScalarExpression.integerProgramRun,IntegerScalar.ofRat_intCast,
    IntegerScalar.ofInt_positive_inv a.denominator a.denominator_pos]
  cases a
  simp only [IntegerScalar.mul,IntegerScalar.ofInt,mul_one,one_mul]

def rawPacketExpression (a : IntegerPacket) : PacketExpression :=
  .tuple (fun i => rawScalarExpression (a.coordinate i))

theorem rawPacketExpression_integerProgramRun (a : IntegerPacket) :
    (rawPacketExpression a).integerProgramRun=IntegerPacket.ofScalars (fun i => a.coordinate i) := by
  simp only [rawPacketExpression,PacketExpression.integerProgramRun,rawScalarExpression_integerProgramRun]

theorem rawPacketExpression_eval (a : IntegerPacket) : (rawPacketExpression a).eval=a.value := by
  rw [← PacketExpression.integerProgramRun_correct,rawPacketExpression_integerProgramRun,IntegerPacket.ofScalars_value]
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_ofFn,IntegerPacket.coordinate_value]

theorem rawScalarExpression_operations (a : IntegerScalar) : (rawScalarExpression a).operations=4 := rfl

theorem rawPacketExpression_operations (a : IntegerPacket) : (rawPacketExpression a).operations=20 := by
  simp only [rawPacketExpression,PacketExpression.operations,rawScalarExpression_operations,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem rationalBinaryExponent_intCast_le (n : ℤ) (B : ℕ) (hn : n.natAbs≤2^B) :
    rationalBinaryExponent (n:ℚ)≤B+1 := by
  have h : IntegerScalarHeight (IntegerScalar.ofInt n) B := ⟨Nat.one_le_pow _ _ (by decide),hn⟩
  have hr:=rationalBinaryExponent_le (IntegerScalar.ofInt n) B h
  simpa only [IntegerScalar.ofInt,IntegerScalar.value,Nat.cast_one,div_one] using hr

theorem rawScalarExpression_integerBitBudget (a : IntegerScalar) (B : ℕ)
    (ha : IntegerScalarHeight a B) : (rawScalarExpression a).integerBitBudget≤2*(B+1) := by
  have hn:=rationalBinaryExponent_intCast_le a.numerator B ha.2
  have hd:=rationalBinaryExponent_intCast_le (a.denominator:ℤ) B (by simpa only [Int.natAbs_natCast] using ha.1)
  change rationalBinaryExponent (a.numerator:ℚ)+rationalBinaryExponent ((a.denominator:ℤ):ℚ)≤2*(B+1)
  omega

theorem rawPacketExpression_integerBitBudget (a : IntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a B) : (rawPacketExpression a).integerBitBudget≤8*(B+1) := by
  have hs : ∀ i,(rawScalarExpression (a.coordinate i)).integerBitBudget≤2*(B+1) :=
    fun i => rawScalarExpression_integerBitBudget _ B (IntegerPacket.coordinate_height a B ha i)
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hs i)
  have he : 4*(2*(B+1))=8*(B+1) := by ring
  simpa only [rawPacketExpression,PacketExpression.integerBitBudget,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,he] using hsum

theorem rawPacketExpression_integerProgramRun_height (a : IntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a B) : IntegerPacketHeight (rawPacketExpression a).integerProgramRun (4*B) := by
  rw [rawPacketExpression_integerProgramRun]
  have h:=IntegerPacket.ofScalars_height (fun i => a.coordinate i) (fun _ => B)
    (fun i => IntegerPacket.coordinate_height a B ha i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

def rawPacketExpressionOracle (f : ℕ → IntegerPacket) : PacketExpressionOracle := fun p =>
  rawPacketExpression (f p)

theorem rawPacketExpressionOracle_eval (f : ℕ → IntegerPacket) :
    evaluatePacketOracle (rawPacketExpressionOracle f)=(fun p => (f p).value) := by
  funext p
  exact rawPacketExpression_eval (f p)

theorem rawPacketExpressionOracle_bitEnvelope (f : ℕ → IntegerPacket) (B : ℕ)
    (hf : ∀ p,IntegerPacketHeight (f p) B) :
    PacketBitEnvelope (rawPacketExpressionOracle f) (0,8*(B+1)) := by
  intro p
  simpa only [rawPacketExpressionOracle,zero_mul,zero_add] using rawPacketExpression_integerBitBudget (f p) B (hf p)

end CircuitRecursion
