import CircuitNumerical.NativeExpressionBudgets

namespace CircuitRecursion

def wordPacketFrame (j : Fin 4) : WordIntegerPacket :=
  ⟨List.Vector.ofFn (fun i => if i=j then ⟨false,[true]⟩ else ⟨false,[]⟩),[true],by
      intro i
      simp only [List.Vector.get_ofFn]
      split_ifs
      · exact ⟨.one,by intro _;rfl⟩
      · exact ⟨.nil,by intro _;rfl⟩,
    .one,by decide⟩

def evaluateNativeScalarOracle (f : NativeScalarExpressionOracle) : RationalOracle :=
  evaluateScalarOracle (interpretNativeScalarOracle f)
def evaluateNativePacketOracle (f : NativePacketExpressionOracle) : QuaternionOracle :=
  evaluatePacketOracle (interpretNativePacketOracle f)

theorem nativeScalarOne_eval : (NativeScalarExpression.literal wordScalarOne).interpret.eval=1 := by
  change (rawScalarExpression wordScalarOne.decode).eval=1
  rw [←ScalarExpression.integerProgramRun_correct,rawScalarExpression_integerProgramRun,wordScalarOne_decode]
  norm_num [IntegerScalar.ofInt,IntegerScalar.value]

theorem nativeScalarZero_eval : (NativeScalarExpression.literal wordScalarZero).interpret.eval=0 := by
  change (rawScalarExpression wordScalarZero.decode).eval=0
  rw [←ScalarExpression.integerProgramRun_correct,rawScalarExpression_integerProgramRun]
  norm_num [wordScalarZero,WordIntegerScalar.decode,SignedBinaryWord.value,binaryWordValue,IntegerScalar.value]

@[simp] theorem evaluateNativeScalarOne : evaluateNativeScalarOracle (fun _ => .literal wordScalarOne)=(fun _ => 1) :=
  funext (fun _ => nativeScalarOne_eval)
@[simp] theorem evaluateNativeScalarZero : evaluateNativeScalarOracle (fun _ => .literal wordScalarZero)=(fun _ => 0) :=
  funext (fun _ => nativeScalarZero_eval)

def nativeExpressionTuple (a : Fin 4 → NativeScalarExpressionOracle) : NativePacketExpressionOracle :=
  fun p => .tuple (fun i => a i p)
def nativeExpressionSelectMax (scores : Fin 4 → NativeScalarExpression)
    (branches : Fin 4 → NativePacketExpressionOracle) : NativePacketExpressionOracle :=
  fun p => .selectMax scores (fun i => branches i p)

@[simp] theorem nativeExpressionTuple_eval (a : Fin 4 → NativeScalarExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionTuple a)=
      (fun p => List.Vector.ofFn (fun i => evaluateNativeScalarOracle (a i) p)) := rfl
@[simp] theorem nativeExpressionSelectMax_eval (scores : Fin 4 → NativeScalarExpression)
    (branches : Fin 4 → NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionSelectMax scores branches)=
      (fun p => let values:=List.Vector.ofFn (fun i => (scores i).interpret.eval)
        evaluateNativePacketOracle (branches (rationalMaxIndex 3 values.get)) p) := rfl

def nativeExpressionAdd (f g : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p =>
  .add (f (p+1)) (g (p+1))
def nativeExpressionNeg (f : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p => .neg (f p)
def nativeExpressionMul (b : ℕ) (f g : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p =>
  .mul (f (p+b+2)) (g (p+b+2))
def nativeExpressionInv (b : ℕ) (f : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p =>
  .inv (f (p+2*b+2))
def nativeExpressionSqrt (f : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p =>
  .sqrt (f (2*p+2)) (p+1)
def nativeExpressionMeanMinus (f : NativeScalarExpressionOracle) : NativeScalarExpressionOracle := fun p =>
  .meanMinus (f p)
def nativeExpressionCoordinate (f : NativePacketExpressionOracle) (i : Fin 4) : NativeScalarExpressionOracle := fun p =>
  .coordinate (f p) i
def nativeExpressionPacketMul (f g : NativePacketExpressionOracle) : NativePacketExpressionOracle := fun p =>
  .mul (f (p+4)) (g (p+4))
def nativeExpressionPacketInverse (f : NativePacketExpressionOracle) : NativePacketExpressionOracle := fun p =>
  .inverse (f p)
def nativeExpressionPacketOne : NativePacketExpressionOracle := fun _ => .literal wordPacketOne
def nativeExpressionFrame (j : Fin 4) : NativePacketExpressionOracle := fun _ =>
  .literal (wordPacketFrame j)
def nativeExpressionDistance (f g : NativePacketExpressionOracle) (p : ℕ) : NativeScalarExpression :=
  .distance (f (p+6)) (g (p+6))

@[simp] theorem nativeExpressionAdd_eval (f g : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionAdd f g)=oracleAdd (evaluateNativeScalarOracle f) (evaluateNativeScalarOracle g) := rfl
@[simp] theorem nativeExpressionNeg_eval (f : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionNeg f)=oracleNeg (evaluateNativeScalarOracle f) := rfl
@[simp] theorem nativeExpressionMul_eval (b : ℕ) (f g : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionMul b f g)=oracleMul b (evaluateNativeScalarOracle f) (evaluateNativeScalarOracle g) := rfl
@[simp] theorem nativeExpressionInv_eval (b : ℕ) (f : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionInv b f)=oracleInv b (evaluateNativeScalarOracle f) := rfl
@[simp] theorem nativeExpressionSqrt_eval (f : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionSqrt f)=oracleSqrt (evaluateNativeScalarOracle f) := rfl
@[simp] theorem nativeExpressionMeanMinus_eval (f : NativeScalarExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionMeanMinus f)=oracleMeanMinus (evaluateNativeScalarOracle f) := rfl
@[simp] theorem nativeExpressionCoordinate_eval (f : NativePacketExpressionOracle) (i : Fin 4) :
    evaluateNativeScalarOracle (nativeExpressionCoordinate f i)=coordinateOracle (evaluateNativePacketOracle f) i := rfl
@[simp] theorem nativeExpressionPacketMul_eval (f g : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionPacketMul f g)=
      quaternionOracleMul (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) := rfl
@[simp] theorem nativeExpressionPacketInverse_eval (f : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionPacketInverse f)=quaternionOracleInverse (evaluateNativePacketOracle f) := rfl
@[simp] theorem nativeExpressionPacketOne_eval : evaluateNativePacketOracle nativeExpressionPacketOne=quaternionOracleOne := by
  funext p
  change (rawPacketExpression wordPacketOne.decode).eval=_
  rw [rawPacketExpression_eval,wordPacketOne_decode]
  exact IntegerPacket.one_value p
@[simp] theorem nativeExpressionFrame_eval (j : Fin 4) : evaluateNativePacketOracle (nativeExpressionFrame j)=frameOracle j := by
  funext p
  change (rawPacketExpression (wordPacketFrame j).decode).eval=_
  rw [rawPacketExpression_eval]
  apply List.Vector.ext
  intro i
  fin_cases j <;> fin_cases i <;>
    simp [wordPacketFrame,WordIntegerPacket.decode,IntegerPacket.value,frameOracle,SignedBinaryWord.value,binaryWordValue,binaryBitValue]
@[simp] theorem nativeExpressionDistance_eval (f g : NativePacketExpressionOracle) (p : ℕ) :
    (nativeExpressionDistance f g p).interpret.eval=distanceScore (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) p := rfl

end CircuitRecursion
