import CircuitNumerical.SharedBinaryRoot

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

mutual
def ScalarExpression.sharedCostedIntegerRun : ScalarExpression → ScalarIntegerEvaluation
  | .literal q => ⟨IntegerScalar.ofRat q,0⟩
  | .stoppingThreshold t => ⟨integerStoppingThreshold t,0⟩
  | .add a b =>
    let x:=a.sharedCostedIntegerRun
    let y:=b.sharedCostedIntegerRun
    ⟨x.value.add y.value,x.rootCharge+y.rootCharge⟩
  | .neg a => let x:=a.sharedCostedIntegerRun;⟨x.value.neg,x.rootCharge⟩
  | .mul a b =>
    let x:=a.sharedCostedIntegerRun
    let y:=b.sharedCostedIntegerRun
    ⟨x.value.mul y.value,x.rootCharge+y.rootCharge⟩
  | .inv a => let x:=a.sharedCostedIntegerRun;⟨x.value.inv,x.rootCharge⟩
  | .sqrt a p =>
    let x:=a.sharedCostedIntegerRun
    let rooted:=x.value.sharedBinaryRoot p
    ⟨rooted.value,x.rootCharge+rooted.rootCharge⟩
  | .meanMinus a => let x:=a.sharedCostedIntegerRun;⟨x.value.meanMinus,x.rootCharge⟩
  | .coordinate a i => let x:=a.sharedCostedIntegerRun;⟨x.value.coordinate i,x.rootCharge⟩
  | .distance a b =>
    let x:=a.sharedCostedIntegerRun
    let y:=b.sharedCostedIntegerRun
    ⟨x.value.distanceScalar y.value,x.rootCharge+y.rootCharge⟩
def PacketExpression.sharedCostedIntegerRun : PacketExpression → PacketIntegerEvaluation
  | .literal q => ⟨IntegerPacket.ofVector q,0⟩
  | .tuple a =>
    let stored:=List.Vector.ofFn (fun i => (a i).sharedCostedIntegerRun)
    ⟨IntegerPacket.ofScalars (fun i => (stored.get i).value),∑ i : Fin 4,(stored.get i).rootCharge⟩
  | .mul a b =>
    let x:=a.sharedCostedIntegerRun
    let y:=b.sharedCostedIntegerRun
    ⟨x.value.mul y.value,x.rootCharge+y.rootCharge⟩
  | .inverse a => let x:=a.sharedCostedIntegerRun;⟨x.value.inverse,x.rootCharge⟩
  | .selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).sharedCostedIntegerRun)
    let j:=integerMaxIndex 3 (fun i => (stored.get i).value)
    let selected:=(branches j).sharedCostedIntegerRun
    ⟨selected.value,(∑ i : Fin 4,(stored.get i).rootCharge)+selected.rootCharge⟩
end

mutual
theorem ScalarExpression.sharedCostedIntegerRun_value (e : ScalarExpression) :
    e.sharedCostedIntegerRun.value=e.integerProgramRun := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a,ScalarExpression.sharedCostedIntegerRun_value b]
  | neg a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a]
  | mul a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a,ScalarExpression.sharedCostedIntegerRun_value b]
  | inv a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a]
  | sqrt a p => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a,IntegerScalar.sharedBinaryRoot_value]
  | meanMinus a => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.sharedCostedIntegerRun_value a]
  | coordinate a i => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      PacketExpression.sharedCostedIntegerRun_value a]
  | distance a b => simp only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.integerProgramRun,
      PacketExpression.sharedCostedIntegerRun_value a,PacketExpression.sharedCostedIntegerRun_value b]
theorem PacketExpression.sharedCostedIntegerRun_value (e : PacketExpression) :
    e.sharedCostedIntegerRun.value=e.integerProgramRun := by
  cases e with
  | literal q => rfl
  | tuple a =>
    have h : (fun i => ((List.Vector.ofFn (fun j => (a j).sharedCostedIntegerRun)).get i).value)=
        (fun i => (a i).integerProgramRun) := by
      funext i
      simpa only [List.Vector.get_ofFn] using ScalarExpression.sharedCostedIntegerRun_value (a i)
    simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.integerProgramRun,h]
  | mul a b => simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.integerProgramRun,
      PacketExpression.sharedCostedIntegerRun_value a,PacketExpression.sharedCostedIntegerRun_value b]
  | inverse a => simp only [PacketExpression.sharedCostedIntegerRun,PacketExpression.integerProgramRun,
      PacketExpression.sharedCostedIntegerRun_value a]
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).sharedCostedIntegerRun)
    have h : (fun i => (stored.get i).value)=(fun i => (scores i).integerProgramRun) := by
      funext i
      simpa only [stored,List.Vector.get_ofFn] using ScalarExpression.sharedCostedIntegerRun_value (scores i)
    change (branches (integerMaxIndex 3 (fun i => (stored.get i).value))).sharedCostedIntegerRun.value=
      (branches (integerMaxIndex 3 (fun i => (scores i).integerProgramRun))).integerProgramRun
    rw [h]
    exact PacketExpression.sharedCostedIntegerRun_value _
end

mutual
theorem ScalarExpression.sharedCostedIntegerRun_rootCharge (e : ScalarExpression) :
    e.sharedCostedIntegerRun.rootCharge≤e.binaryRootPrimitiveOperations := by
  cases e with
  | literal q => exact le_refl _
  | stoppingThreshold t => exact le_refl _
  | add a b =>
    exact Nat.add_le_add (ScalarExpression.sharedCostedIntegerRun_rootCharge a)
      (ScalarExpression.sharedCostedIntegerRun_rootCharge b)
  | neg a => exact ScalarExpression.sharedCostedIntegerRun_rootCharge a
  | mul a b =>
    exact Nat.add_le_add (ScalarExpression.sharedCostedIntegerRun_rootCharge a)
      (ScalarExpression.sharedCostedIntegerRun_rootCharge b)
  | inv a => exact ScalarExpression.sharedCostedIntegerRun_rootCharge a
  | sqrt a p =>
    simpa only [ScalarExpression.sharedCostedIntegerRun,ScalarExpression.binaryRootPrimitiveOperations,
      IntegerScalar.sharedBinaryRoot_charge,ScalarExpression.sharedCostedIntegerRun_value,ScalarExpression.integerProgramRun_eq] using
      Nat.add_le_add_right (ScalarExpression.sharedCostedIntegerRun_rootCharge a)
        (a.integerRun.binaryRootPrimitiveOperations p)
  | meanMinus a => exact ScalarExpression.sharedCostedIntegerRun_rootCharge a
  | coordinate a i => exact PacketExpression.sharedCostedIntegerRun_rootCharge a
  | distance a b =>
    exact Nat.add_le_add (PacketExpression.sharedCostedIntegerRun_rootCharge a)
      (PacketExpression.sharedCostedIntegerRun_rootCharge b)
theorem PacketExpression.sharedCostedIntegerRun_rootCharge (e : PacketExpression) :
    e.sharedCostedIntegerRun.rootCharge≤e.binaryRootPrimitiveOperations := by
  cases e with
  | literal q => exact le_refl _
  | tuple a =>
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => ScalarExpression.sharedCostedIntegerRun_rootCharge (a i))
    simpa only [PacketExpression.sharedCostedIntegerRun,PacketExpression.binaryRootPrimitiveOperations,
      List.Vector.get_ofFn] using hs
  | mul a b =>
    exact Nat.add_le_add (PacketExpression.sharedCostedIntegerRun_rootCharge a)
      (PacketExpression.sharedCostedIntegerRun_rootCharge b)
  | inverse a => exact PacketExpression.sharedCostedIntegerRun_rootCharge a
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).sharedCostedIntegerRun)
    let j:=integerMaxIndex 3 (fun i => (stored.get i).value)
    have hs : (∑ i : Fin 4,(stored.get i).rootCharge)≤∑ i : Fin 4,(scores i).binaryRootPrimitiveOperations := by
      simpa only [stored,List.Vector.get_ofFn] using Finset.sum_le_sum (s:=Finset.univ)
        (fun i (_ : i∈Finset.univ) => ScalarExpression.sharedCostedIntegerRun_rootCharge (scores i))
    have hb : (branches j).sharedCostedIntegerRun.rootCharge≤∑ i : Fin 4,(branches i).binaryRootPrimitiveOperations :=
      (PacketExpression.sharedCostedIntegerRun_rootCharge (branches j)).trans (Finset.single_le_sum
        (fun i (_ : i∈Finset.univ) => Nat.zero_le ((branches i).binaryRootPrimitiveOperations)) (Finset.mem_univ j))
    exact Nat.add_le_add hs hb
end

theorem ScalarExpression.sharedCostedIntegerRun_correct (e : ScalarExpression) :
    e.sharedCostedIntegerRun.value.value=e.eval := by
  rw [ScalarExpression.sharedCostedIntegerRun_value]
  exact ScalarExpression.integerProgramRun_correct e

theorem PacketExpression.sharedCostedIntegerRun_correct (e : PacketExpression) :
    e.sharedCostedIntegerRun.value.value=e.eval := by
  rw [PacketExpression.sharedCostedIntegerRun_value]
  exact PacketExpression.integerProgramRun_correct e

end CircuitRecursion
