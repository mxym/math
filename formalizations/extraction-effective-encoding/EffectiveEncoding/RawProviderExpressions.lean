import EffectiveEncoding.SharedRawCompiler

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

def AngleAtom.rawCosExpression (a : AngleAtom) (p : ℕ) : ScalarExpression :=
  match a with
  | .pi => .literal (-1)
  | .merge A B j => if h : j=0 ∨ A+B=0 then .literal 1 else
      .sqrt (rawScalarExpression (integerFraction A (A+B) (by omega))) (p+1)

def AngleAtom.rawSinExpression (a : AngleAtom) (p : ℕ) : ScalarExpression :=
  match a with
  | .pi => .literal 0
  | .merge A B j => if h : j=0 ∨ A+B=0 then .literal 0 else
      .sqrt (rawScalarExpression (integerFraction B (A+B) (by omega))) (p+1)


theorem AngleAtom.rawCosExpression_run (a : AngleAtom) (p : ℕ) :
    (a.rawCosExpression p).integerProgramRun=rawAtomCos a p := by
  cases a with
  | pi => rfl
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simp only [rawCosExpression,rawAtomCos,dite_eq_left h,ScalarExpression.integerProgramRun,integerLiteral_one]
    · simp only [rawCosExpression,rawAtomCos,dite_eq_right h,ScalarExpression.integerProgramRun,
        rawScalarExpression_integerProgramRun]

theorem AngleAtom.rawSinExpression_run (a : AngleAtom) (p : ℕ) :
    (a.rawSinExpression p).integerProgramRun=rawAtomSin a p := by
  cases a with
  | pi => exact integerLiteral_zero
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simp only [rawSinExpression,rawAtomSin,dite_eq_left h,ScalarExpression.integerProgramRun,integerLiteral_zero]
    · simp only [rawSinExpression,rawAtomSin,dite_eq_right h,ScalarExpression.integerProgramRun,
        rawScalarExpression_integerProgramRun]


def AngleCode.rawCosExpression (a : AngleCode) : ScalarExpressionOracle :=
  halfCosExpression a.halvings a.atom.rawCosExpression

def AngleCode.rawSinExpression (a : AngleCode) : ScalarExpressionOracle := fun p =>
  let s:=halfSinExpression a.halvings a.atom.rawCosExpression a.atom.rawSinExpression p
  if a.negative then .neg s else s


theorem AngleCode.rawCosExpression_run (a : AngleCode) (p : ℕ) :
    (a.rawCosExpression p).integerProgramRun=a.rawCos p := by
  rw [ScalarExpression.integerProgramRun_eq]
  exact (rawHalfCos_eq a.halvings (rawAtomCos a.atom) a.atom.rawCosExpression
    (fun q => by rw [← ScalarExpression.integerProgramRun_eq,AngleAtom.rawCosExpression_run]) p).symm

theorem AngleCode.rawSinExpression_run (a : AngleCode) (p : ℕ) :
    (a.rawSinExpression p).integerProgramRun=a.rawSin p := by
  have h := rawHalfSin_eq a.halvings (rawAtomCos a.atom) (rawAtomSin a.atom)
    a.atom.rawCosExpression a.atom.rawSinExpression
    (fun q => by rw [← ScalarExpression.integerProgramRun_eq,AngleAtom.rawCosExpression_run])
    (fun q => by rw [← ScalarExpression.integerProgramRun_eq,AngleAtom.rawSinExpression_run]) p
  cases hn : a.negative <;> simp only [rawSinExpression,rawSin,hn,Bool.false_eq_true,ite_false,ite_true,
    ScalarExpression.integerProgramRun,ScalarExpression.integerProgramRun_eq,ScalarExpression.integerRun,← h]


def rawPhaseCosExpression (a b : AngleCode) (p : ℕ) : ScalarExpression :=
  .add (.mul ((a.half 1).rawCosExpression (p+3)) ((b.half 1).rawCosExpression (p+3)))
    (.mul ((a.half 1).rawSinExpression (p+3)) ((b.half 1).rawSinExpression (p+3)))

def rawPhaseSinExpression (a b : AngleCode) (p : ℕ) : ScalarExpression :=
  .add (.mul ((a.half 1).rawSinExpression (p+3)) ((b.half 1).rawCosExpression (p+3)))
    (.neg (.mul ((a.half 1).rawCosExpression (p+3)) ((b.half 1).rawSinExpression (p+3))))


theorem rawPhaseCosExpression_run (a b : AngleCode) (p : ℕ) :
    (rawPhaseCosExpression a b p).integerProgramRun=rawPhaseCos a b p := by
  simp only [rawPhaseCosExpression,rawPhaseCos,ScalarExpression.integerProgramRun,
    AngleCode.rawCosExpression_run,AngleCode.rawSinExpression_run]

theorem rawPhaseSinExpression_run (a b : AngleCode) (p : ℕ) :
    (rawPhaseSinExpression a b p).integerProgramRun=rawPhaseSin a b p := by
  simp only [rawPhaseSinExpression,rawPhaseSin,ScalarExpression.integerProgramRun,
    AngleCode.rawCosExpression_run,AngleCode.rawSinExpression_run]

/-- Dynamic fractions are encoded by raw numerator/denominator fields.
Only fixed rational constants and denominator-one literal data occur. -/
def SingleCode.rawPacketExpression : SingleCode → PacketExpressionOracle
  | .hadamard,p => .tuple ![.literal 0,.neg (.sqrt (.literal (1/2)) (p+1)),
      .literal 0,.neg (.sqrt (.literal (1/2)) (p+1))]
  | .yBasis,_ => .tuple ![.literal (1/2),.literal (1/2),.literal (1/2),.literal (1/2)]
  | .phase a b,p => .tuple ![rawPhaseCosExpression a b p,rawPhaseSinExpression a b p,.literal 0,.literal 0]
  | .inverse u,p => .inverse (u.rawPacketExpression p)


theorem SingleCode.rawPacketExpression_run (u : SingleCode) (p : ℕ) :
    (u.rawPacketExpression p).integerProgramRun=u.rawPacket p := by
  induction u with
  | hadamard =>
    simp only [rawPacketExpression,rawPacket,PacketExpression.integerProgramRun]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> simp [ScalarExpression.integerProgramRun,integerLiteral_zero,integerLiteral_halfInv]
  | yBasis =>
    simp only [rawPacketExpression,rawPacket,PacketExpression.integerProgramRun]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> simp [ScalarExpression.integerProgramRun,integerLiteral_halfInv]
  | phase a b =>
    simp only [rawPacketExpression,rawPacket,PacketExpression.integerProgramRun]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i
    · exact rawPhaseCosExpression_run a b p
    · exact rawPhaseSinExpression_run a b p
    · rfl
    · rfl
  | inverse u ih => simp only [rawPacketExpression,rawPacket,PacketExpression.integerProgramRun,ih]

/-- Actual shared binary-root execution of the target provider itself.
The returned root annotation excludes other primitives and its own bookkeeping. -/
def SingleCode.rawPacketProgram (u : SingleCode) (p : ℕ) : PacketIntegerEvaluation :=
  (u.rawPacketExpression p).sharedCostedIntegerRun


theorem SingleCode.rawPacketProgram_value (u : SingleCode) (p : ℕ) :
    (u.rawPacketProgram p).value=u.rawPacket p := by
  rw [rawPacketProgram,PacketExpression.sharedCostedIntegerRun_value,rawPacketExpression_run]

end EffectiveEncoding
