import CircuitNumerical.IntegerSelection

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

mutual
def ScalarExpression.integerProgramRun : ScalarExpression → IntegerScalar
  | .literal q => IntegerScalar.ofRat q
  | .stoppingThreshold t => integerStoppingThreshold t
  | .add a b => a.integerProgramRun.add b.integerProgramRun
  | .neg a => a.integerProgramRun.neg
  | .mul a b => a.integerProgramRun.mul b.integerProgramRun
  | .inv a => a.integerProgramRun.inv
  | .sqrt a p => a.integerProgramRun.binaryRoot p
  | .meanMinus a => a.integerProgramRun.meanMinus
  | .coordinate a i => a.integerProgramRun.coordinate i
  | .distance a b => a.integerProgramRun.distanceScalar b.integerProgramRun
def PacketExpression.integerProgramRun : PacketExpression → IntegerPacket
  | .literal q => IntegerPacket.ofVector q
  | .tuple a => IntegerPacket.ofScalars (fun i => (a i).integerProgramRun)
  | .mul a b => a.integerProgramRun.mul b.integerProgramRun
  | .inverse a => a.integerProgramRun.inverse
  | .selectMax scores branches =>
    (branches (integerMaxIndex 3 (fun i => (scores i).integerProgramRun))).integerProgramRun
end

mutual
theorem ScalarExpression.integerProgramRun_eq (e : ScalarExpression) : e.integerProgramRun=e.integerRun := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a,ScalarExpression.integerProgramRun_eq b]
  | neg a => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a]
  | mul a b => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a,ScalarExpression.integerProgramRun_eq b]
  | inv a => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a]
  | sqrt a p => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a,IntegerScalar.binaryRoot_eq]
  | meanMinus a => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,ScalarExpression.integerProgramRun_eq a]
  | coordinate a i => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,PacketExpression.integerProgramRun_eq a]
  | distance a b => simp only [ScalarExpression.integerProgramRun,ScalarExpression.integerRun,PacketExpression.integerProgramRun_eq a,PacketExpression.integerProgramRun_eq b]
theorem PacketExpression.integerProgramRun_eq (e : PacketExpression) : e.integerProgramRun=e.integerRun := by
  cases e with
  | literal q => rfl
  | tuple a =>
    have h : (fun i => (a i).integerProgramRun)=(fun i => (a i).integerRun) :=
      funext (fun i => ScalarExpression.integerProgramRun_eq (a i))
    simp only [PacketExpression.integerProgramRun,PacketExpression.integerRun,integerMaxIndex_eq,h,List.Vector.get_ofFn]
  | mul a b => simp only [PacketExpression.integerProgramRun,PacketExpression.integerRun,PacketExpression.integerProgramRun_eq a,PacketExpression.integerProgramRun_eq b]
  | inverse a => simp only [PacketExpression.integerProgramRun,PacketExpression.integerRun,PacketExpression.integerProgramRun_eq a]
  | selectMax scores branches =>
    let score:=fun i => (scores i).integerRun.value
    have h : (fun i => (scores i).integerProgramRun.value)=score :=
      funext (fun i => congrArg IntegerScalar.value (ScalarExpression.integerProgramRun_eq (scores i)))
    have hget : (List.Vector.ofFn score).get=score := by
      funext i
      exact List.Vector.get_ofFn score i
    change (branches (integerMaxIndex 3 (fun i => (scores i).integerProgramRun))).integerProgramRun=
      (branches (rationalMaxIndex 3 (List.Vector.ofFn score).get)).integerRun
    rw [integerMaxIndex_eq,h,hget]
    exact PacketExpression.integerProgramRun_eq (branches (rationalMaxIndex 3 score))
end

theorem ScalarExpression.integerProgramRun_correct (e : ScalarExpression) : e.integerProgramRun.value=e.eval := by
  rw [ScalarExpression.integerProgramRun_eq]
  exact ScalarExpression.integerRun_correct e

theorem PacketExpression.integerProgramRun_correct (e : PacketExpression) : e.integerProgramRun.value=e.eval := by
  rw [PacketExpression.integerProgramRun_eq]
  exact PacketExpression.integerRun_correct e

end CircuitRecursion
