import CircuitNumerical.SharedCostedNumericalProgram

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

mutual
theorem ScalarExpression.sharedCostedIntegerRun_eq (e : ScalarExpression) :
    e.sharedCostedIntegerRun=e.costedIntegerRun := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a,ScalarExpression.sharedCostedIntegerRun_eq b]
  | neg a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a]
  | mul a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a,ScalarExpression.sharedCostedIntegerRun_eq b]
  | inv a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a]
  | sqrt a p => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a,IntegerScalar.sharedBinaryRoot_eq]
  | meanMinus a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      ScalarExpression.sharedCostedIntegerRun_eq a]
  | coordinate a i => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      PacketExpression.sharedCostedIntegerRun_eq a]
  | distance a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.costedIntegerRun,
      PacketExpression.sharedCostedIntegerRun_eq a,PacketExpression.sharedCostedIntegerRun_eq b]
theorem PacketExpression.sharedCostedIntegerRun_eq (e : PacketExpression) :
    e.sharedCostedIntegerRun=e.costedIntegerRun := by
  cases e with
  | literal q => rfl
  | tuple a =>
    have h : (fun i => (a i).sharedCostedIntegerRun)=(fun i => (a i).costedIntegerRun) :=
      funext (fun i => ScalarExpression.sharedCostedIntegerRun_eq (a i))
    simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.costedIntegerRun,h]
  | mul a b => simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.costedIntegerRun,
      PacketExpression.sharedCostedIntegerRun_eq a,PacketExpression.sharedCostedIntegerRun_eq b]
  | inverse a => simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.costedIntegerRun,
      PacketExpression.sharedCostedIntegerRun_eq a]
  | selectMax scores branches =>
    have h : (fun i => (scores i).sharedCostedIntegerRun)=(fun i => (scores i).costedIntegerRun) :=
      funext (fun i => ScalarExpression.sharedCostedIntegerRun_eq (scores i))
    let stored:=List.Vector.ofFn (fun i => (scores i).costedIntegerRun)
    let j:=integerMaxIndex 3 (fun i => (stored.get i).value)
    have hb:=PacketExpression.sharedCostedIntegerRun_eq (branches j)
    have hr:=congrArg (fun r : PacketIntegerEvaluation =>
      PacketIntegerEvaluation.mk r.value ((∑ i : Fin 4,(stored.get i).rootCharge)+r.rootCharge)) hb
    simpa only [PacketExpression.sharedCostedIntegerRun,PacketExpression.costedIntegerRun,h,stored,j] using hr
end

theorem sharedCostedTracedBase_eq {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    sharedCostedTracedBase entry table f=costedTracedBase entry table f := by
  have h : ScalarExpression.sharedCostedIntegerRun=ScalarExpression.costedIntegerRun :=
    funext ScalarExpression.sharedCostedIntegerRun_eq
  simp only [sharedCostedTracedBase,costedTracedBase,h]

theorem sharedCostedTracedCorrection_eq {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → CostedArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) :
    sharedCostedTracedCorrection entry inverseLabel approx t f=costedTracedCorrection entry inverseLabel approx t f := by
  simp only [sharedCostedTracedCorrection,costedTracedCorrection,ScalarExpression.sharedCostedIntegerRun_eq]

theorem sharedCostedTracedPairWord_eq {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    sharedCostedTracedPairWord entry inverseLabel table k f=costedTracedPairWord entry inverseLabel table k f := by
  have hc : sharedCostedTracedCorrection entry inverseLabel=costedTracedCorrection entry inverseLabel := by
    funext approx t f
    exact sharedCostedTracedCorrection_eq entry inverseLabel approx t f
  induction k generalizing f with
  | zero => exact sharedCostedTracedBase_eq entry table f
  | succ k ih =>
    have hi : sharedCostedTracedPairWord entry inverseLabel table k=costedTracedPairWord entry inverseLabel table k :=
      funext ih
    simp only [sharedCostedTracedPairWord,costedTracedPairWord,hc,hi]

theorem sharedCostedCachedArithmeticRun_eq {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    sharedCostedCachedArithmeticRun entry inverseLabel table L p f=costedCachedArithmeticRun entry inverseLabel table L p f :=
  sharedCostedTracedPairWord_eq _ inverseLabel table _ _

end CircuitRecursion
