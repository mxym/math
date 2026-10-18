import CircuitNumerical.InputCacheBudgets

namespace CircuitRecursion

abbrev InputScalarExpressionOracle (m : ℕ) := ℕ → InputScalarExpression m
abbrev InputPacketExpressionOracle (m : ℕ) := ℕ → InputPacketExpression m

def resolveInputScalarOracle {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (f : InputScalarExpressionOracle m) : NativeScalarExpressionOracle := fun q => (f q).resolve cache
def resolveInputPacketOracle {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (f : InputPacketExpressionOracle m) : NativePacketExpressionOracle := fun q => (f q).resolve cache

def inputExpressionTuple {m : ℕ} (a : Fin 4 → InputScalarExpressionOracle m) : InputPacketExpressionOracle m :=
  fun p => .tuple (fun i => a i p)

def inputExpressionSelectMax {m : ℕ} (scores : Fin 4 → InputScalarExpression m)
    (branches : Fin 4 → InputPacketExpressionOracle m) : InputPacketExpressionOracle m :=
  fun p => .selectMax scores (fun i => branches i p)

def inputExpressionAdd {m : ℕ} (f g : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p =>
  .add (f (p+1)) (g (p+1))

def inputExpressionNeg {m : ℕ} (f : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p => .neg (f p)

def inputExpressionMul {m : ℕ} (b : ℕ) (f g : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p =>
  .mul (f (p+b+2)) (g (p+b+2))

def inputExpressionInv {m : ℕ} (b : ℕ) (f : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p =>
  .inv (f (p+2*b+2))

def inputExpressionSqrt {m : ℕ} (f : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p =>
  .sqrt (f (2*p+2)) (p+1)

def inputExpressionMeanMinus {m : ℕ} (f : InputScalarExpressionOracle m) : InputScalarExpressionOracle m := fun p =>
  .meanMinus (f p)

def inputExpressionCoordinate {m : ℕ} (f : InputPacketExpressionOracle m) (i : Fin 4) : InputScalarExpressionOracle m := fun p =>
  .coordinate (f p) i

def inputExpressionPacketMul {m : ℕ} (f g : InputPacketExpressionOracle m) : InputPacketExpressionOracle m := fun p =>
  .mul (f (p+4)) (g (p+4))

def inputExpressionPacketInverse {m : ℕ} (f : InputPacketExpressionOracle m) : InputPacketExpressionOracle m := fun p =>
  .inverse (f p)

def inputExpressionPacketOne {m : ℕ} : InputPacketExpressionOracle m := fun _ => .literal wordPacketOne

def inputExpressionFrame {m : ℕ} (j : Fin 4) : InputPacketExpressionOracle m := fun _ =>
  .literal (wordPacketFrame j)

def inputExpressionDistance {m : ℕ} (f g : InputPacketExpressionOracle m) (p : ℕ) : InputScalarExpression m :=
  .distance (f (p+6)) (g (p+6))

def inputExpressionBalancedS {m : ℕ} (f : InputPacketExpressionOracle m) : InputScalarExpressionOracle m :=
  inputExpressionSqrt (inputExpressionSqrt (inputExpressionMeanMinus (inputExpressionCoordinate f 0)))

def inputExpressionBalancedC {m : ℕ} (f : InputPacketExpressionOracle m) : InputScalarExpressionOracle m :=
  inputExpressionSqrt (inputExpressionAdd (fun _ => .literal wordScalarOne)
    (inputExpressionNeg (inputExpressionMul 0 (inputExpressionBalancedS f) (inputExpressionBalancedS f))))

def inputExpressionReferenceX {m : ℕ} (f : InputPacketExpressionOracle m) : InputPacketExpressionOracle m :=
  inputExpressionTuple ![inputExpressionBalancedC f,(fun _ => .literal wordScalarZero),(fun _ => .literal wordScalarZero),inputExpressionBalancedS f]

def inputExpressionReferenceY {m : ℕ} (f : InputPacketExpressionOracle m) : InputPacketExpressionOracle m :=
  inputExpressionTuple ![inputExpressionBalancedC f,(fun _ => .literal wordScalarZero),inputExpressionBalancedS f,(fun _ => .literal wordScalarZero)]

def inputExpressionBalancedReference {m : ℕ} (f : InputPacketExpressionOracle m) : InputPacketExpressionOracle m :=
  inputExpressionPacketMul
    (inputExpressionPacketMul (inputExpressionPacketMul (inputExpressionReferenceX f) (inputExpressionReferenceY f))
      (inputExpressionPacketInverse (inputExpressionReferenceX f)))
    (inputExpressionPacketInverse (inputExpressionReferenceY f))

def inputExpressionChartTarget {m : ℕ} (f : InputPacketExpressionOracle m) (j : Fin 4) : InputPacketExpressionOracle m :=
  inputExpressionPacketMul (inputExpressionPacketMul (inputExpressionFrame j) f)
    (inputExpressionPacketInverse (inputExpressionFrame j))

def inputExpressionChartMass {m : ℕ} (f g : InputPacketExpressionOracle m) (p : ℕ) (j : Fin 4) : InputScalarExpression m :=
  inputExpressionDistance f (inputExpressionPacketInverse (inputExpressionChartTarget g j)) p

def inputExpressionRadius {m : ℕ} (f g : InputPacketExpressionOracle m) (j : Fin 4) : InputScalarExpressionOracle m :=
  inputExpressionSqrt (fun p => inputExpressionChartMass f g p j)

def inputExpressionNormalized {m : ℕ} (f g : InputPacketExpressionOracle m) (t : ℕ) (j : Fin 4) : InputPacketExpressionOracle m :=
  let radiusInv := inputExpressionInv (t+1) (inputExpressionRadius f g j)
  let adjoint := inputExpressionPacketInverse (inputExpressionChartTarget g j)
  inputExpressionTuple (fun i => inputExpressionMul (t+2)
    (inputExpressionAdd (inputExpressionCoordinate f i) (inputExpressionNeg (inputExpressionCoordinate adjoint i))) radiusInv)

def inputExpressionConjugator {m : ℕ} (f : InputPacketExpressionOracle m) (t : ℕ) : InputPacketExpressionOracle m :=
  let g := inputExpressionBalancedReference f
  inputExpressionSelectMax (inputExpressionChartMass f g (2*t+2))
    (fun j => inputExpressionPacketMul (inputExpressionNormalized f g t j) (inputExpressionFrame j))

def inputExpressionConjugate {m : ℕ} (f g : InputPacketExpressionOracle m) : InputPacketExpressionOracle m :=
  inputExpressionPacketMul (inputExpressionPacketMul f g) (inputExpressionPacketInverse f)

def inputExpressionFactorX {m : ℕ} (f : InputPacketExpressionOracle m) (t : ℕ) : InputPacketExpressionOracle m :=
  inputExpressionConjugate (inputExpressionConjugator f t) (inputExpressionReferenceX f)

def inputExpressionFactorY {m : ℕ} (f : InputPacketExpressionOracle m) (t : ℕ) : InputPacketExpressionOracle m :=
  inputExpressionConjugate (inputExpressionConjugator f t) (inputExpressionReferenceY f)

@[simp] theorem inputExpressionAdd_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionAdd f g)=nativeExpressionAdd (resolveInputScalarOracle cache f) (resolveInputScalarOracle cache g) := rfl

@[simp] theorem inputExpressionMul_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (b : ℕ) (f g : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionMul b f g)=nativeExpressionMul b (resolveInputScalarOracle cache f) (resolveInputScalarOracle cache g) := rfl

@[simp] theorem inputExpressionNeg_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionNeg f)=nativeExpressionNeg (resolveInputScalarOracle cache f) := rfl

@[simp] theorem inputExpressionSqrt_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionSqrt f)=nativeExpressionSqrt (resolveInputScalarOracle cache f) := rfl

@[simp] theorem inputExpressionMeanMinus_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionMeanMinus f)=nativeExpressionMeanMinus (resolveInputScalarOracle cache f) := rfl

@[simp] theorem inputExpressionInv_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (b : ℕ) (f : InputScalarExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionInv b f)=nativeExpressionInv b (resolveInputScalarOracle cache f) := rfl

@[simp] theorem inputExpressionCoordinate_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) (i : Fin 4) :
    resolveInputScalarOracle cache (inputExpressionCoordinate f i)=nativeExpressionCoordinate (resolveInputPacketOracle cache f) i := rfl

@[simp] theorem inputExpressionPacketMul_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionPacketMul f g)=nativeExpressionPacketMul (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) := rfl

@[simp] theorem inputExpressionPacketInverse_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionPacketInverse f)=nativeExpressionPacketInverse (resolveInputPacketOracle cache f) := rfl

@[simp] theorem inputExpressionPacketOne_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P)  :
    resolveInputPacketOracle cache (inputExpressionPacketOne)=nativeExpressionPacketOne := rfl

@[simp] theorem inputExpressionFrame_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (j : Fin 4) :
    resolveInputPacketOracle cache (inputExpressionFrame j)=nativeExpressionFrame j := rfl

@[simp] theorem inputExpressionDistance_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) (q : ℕ) :
    (inputExpressionDistance f g q).resolve cache=nativeExpressionDistance (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) q := rfl

@[simp] theorem inputExpressionTuple_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (a : Fin 4 → InputScalarExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionTuple a)=nativeExpressionTuple (fun i => resolveInputScalarOracle cache (a i)) := rfl

@[simp] theorem inputExpressionSelectMax_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (scores : Fin 4 → InputScalarExpression m) (branches : Fin 4 → InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionSelectMax scores branches)=nativeExpressionSelectMax (fun i => (scores i).resolve cache) (fun i => resolveInputPacketOracle cache (branches i)) := rfl

@[simp] theorem inputExpressionBalancedS_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionBalancedS f)=nativeExpressionBalancedS (resolveInputPacketOracle cache f) := rfl

@[simp] theorem inputExpressionBalancedC_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputScalarOracle cache (inputExpressionBalancedC f)=nativeExpressionBalancedC (resolveInputPacketOracle cache f) := rfl

@[simp] theorem inputExpressionReferenceX_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionReferenceX f)=nativeExpressionReferenceX (resolveInputPacketOracle cache f) := by
  funext q
  apply congrArg NativePacketExpression.tuple
  funext i
  fin_cases i <;> rfl

@[simp] theorem inputExpressionReferenceY_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionReferenceY f)=nativeExpressionReferenceY (resolveInputPacketOracle cache f) := by
  funext q
  apply congrArg NativePacketExpression.tuple
  funext i
  fin_cases i <;> rfl

@[simp] theorem inputExpressionBalancedReference_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionBalancedReference f)=nativeExpressionBalancedReference (resolveInputPacketOracle cache f) := by
  simp only [inputExpressionBalancedReference,inputExpressionPacketMul_resolve,inputExpressionPacketInverse_resolve,inputExpressionReferenceX_resolve,inputExpressionReferenceY_resolve,nativeExpressionBalancedReference]

@[simp] theorem inputExpressionChartTarget_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) (j : Fin 4) :
    resolveInputPacketOracle cache (inputExpressionChartTarget f j)=nativeExpressionChartTarget (resolveInputPacketOracle cache f) j := rfl

@[simp] theorem inputExpressionChartMass_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) (q : ℕ) (j : Fin 4) :
    (inputExpressionChartMass f g q j).resolve cache=nativeExpressionChartMass (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) q j := rfl

@[simp] theorem inputExpressionRadius_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) (j : Fin 4) :
    resolveInputScalarOracle cache (inputExpressionRadius f g j)=nativeExpressionRadius (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) j := rfl

@[simp] theorem inputExpressionNormalized_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) (t : ℕ) (j : Fin 4) :
    resolveInputPacketOracle cache (inputExpressionNormalized f g t j)=nativeExpressionNormalized (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) t j := rfl

@[simp] theorem inputExpressionConjugator_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) (t : ℕ) :
    resolveInputPacketOracle cache (inputExpressionConjugator f t)=nativeExpressionConjugator (resolveInputPacketOracle cache f) t := by
  simp only [inputExpressionConjugator,inputExpressionSelectMax_resolve,inputExpressionChartMass_resolve,inputExpressionBalancedReference_resolve,inputExpressionPacketMul_resolve,inputExpressionNormalized_resolve,inputExpressionFrame_resolve,nativeExpressionConjugator]

@[simp] theorem inputExpressionConjugate_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f g : InputPacketExpressionOracle m) :
    resolveInputPacketOracle cache (inputExpressionConjugate f g)=nativeExpressionConjugate (resolveInputPacketOracle cache f) (resolveInputPacketOracle cache g) := rfl

@[simp] theorem inputExpressionFactorX_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) (t : ℕ) :
    resolveInputPacketOracle cache (inputExpressionFactorX f t)=nativeExpressionFactorX (resolveInputPacketOracle cache f) t := by
  simp only [inputExpressionFactorX,inputExpressionConjugate_resolve,inputExpressionConjugator_resolve,inputExpressionReferenceX_resolve,nativeExpressionFactorX]

@[simp] theorem inputExpressionFactorY_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (f : InputPacketExpressionOracle m) (t : ℕ) :
    resolveInputPacketOracle cache (inputExpressionFactorY f t)=nativeExpressionFactorY (resolveInputPacketOracle cache f) t := by
  simp only [inputExpressionFactorY,inputExpressionConjugate_resolve,inputExpressionConjugator_resolve,inputExpressionReferenceY_resolve,nativeExpressionFactorY]

def inputExpressionWord {m : ℕ} (entry : Fin m → InputPacketExpressionOracle m) :
    List (Fin m) → InputPacketExpressionOracle m
  | [] => inputExpressionPacketOne
  | i::w => inputExpressionPacketMul (inputExpressionWord entry w) (entry i)

@[simp] theorem inputExpressionWord_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (w : List (Fin m)) :
    resolveInputPacketOracle cache (inputExpressionWord entry w)=
      nativeExpressionWord (fun i => resolveInputPacketOracle cache (entry i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [inputExpressionWord,inputExpressionPacketMul_resolve,ih,nativeExpressionWord]

end CircuitRecursion
