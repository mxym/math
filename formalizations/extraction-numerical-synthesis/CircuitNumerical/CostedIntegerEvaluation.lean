import CircuitNumerical.IntegerNumericalProgram

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure ScalarIntegerEvaluation where
  value : IntegerScalar
  rootCharge : ℕ

structure PacketIntegerEvaluation where
  value : IntegerPacket
  rootCharge : ℕ

/- A finite cost semantics for the explicit root subprograms. Every recursive
operand is evaluated into a stored record before its fields are read. Tuple
coordinates and selector scores are materialized in finite vectors, so those
recursive evaluations occur once. Only the selected branch is evaluated.
Other primitive, syntax construction, memory and provider costs are separate. -/
mutual
def ScalarExpression.costedIntegerRun : ScalarExpression → ScalarIntegerEvaluation
  | .literal q => ⟨IntegerScalar.ofRat q,0⟩
  | .stoppingThreshold t => ⟨integerStoppingThreshold t,0⟩
  | .add a b =>
    let x:=a.costedIntegerRun
    let y:=b.costedIntegerRun
    ⟨x.value.add y.value,x.rootCharge+y.rootCharge⟩
  | .neg a => let x:=a.costedIntegerRun;⟨x.value.neg,x.rootCharge⟩
  | .mul a b =>
    let x:=a.costedIntegerRun
    let y:=b.costedIntegerRun
    ⟨x.value.mul y.value,x.rootCharge+y.rootCharge⟩
  | .inv a => let x:=a.costedIntegerRun;⟨x.value.inv,x.rootCharge⟩
  | .sqrt a p =>
    let x:=a.costedIntegerRun
    ⟨x.value.binaryRoot p,x.rootCharge+x.value.binaryRootPrimitiveOperations p⟩
  | .meanMinus a => let x:=a.costedIntegerRun;⟨x.value.meanMinus,x.rootCharge⟩
  | .coordinate a i => let x:=a.costedIntegerRun;⟨x.value.coordinate i,x.rootCharge⟩
  | .distance a b =>
    let x:=a.costedIntegerRun
    let y:=b.costedIntegerRun
    ⟨x.value.distanceScalar y.value,x.rootCharge+y.rootCharge⟩
def PacketExpression.costedIntegerRun : PacketExpression → PacketIntegerEvaluation
  | .literal q => ⟨IntegerPacket.ofVector q,0⟩
  | .tuple a =>
    let stored:=List.Vector.ofFn (fun i => (a i).costedIntegerRun)
    ⟨IntegerPacket.ofScalars (fun i => (stored.get i).value),∑ i : Fin 4,(stored.get i).rootCharge⟩
  | .mul a b =>
    let x:=a.costedIntegerRun
    let y:=b.costedIntegerRun
    ⟨x.value.mul y.value,x.rootCharge+y.rootCharge⟩
  | .inverse a => let x:=a.costedIntegerRun;⟨x.value.inverse,x.rootCharge⟩
  | .selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).costedIntegerRun)
    let j:=integerMaxIndex 3 (fun i => (stored.get i).value)
    let selected:=(branches j).costedIntegerRun
    ⟨selected.value,(∑ i : Fin 4,(stored.get i).rootCharge)+selected.rootCharge⟩
end

mutual
theorem ScalarExpression.costedIntegerRun_value (e : ScalarExpression) :
    e.costedIntegerRun.value=e.integerProgramRun := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a,ScalarExpression.costedIntegerRun_value b]
  | neg a => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a]
  | mul a b => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a,ScalarExpression.costedIntegerRun_value b]
  | inv a => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a]
  | sqrt a p => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a]
  | meanMinus a => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      ScalarExpression.costedIntegerRun_value a]
  | coordinate a i => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      PacketExpression.costedIntegerRun_value a]
  | distance a b => simp only [ScalarExpression.costedIntegerRun,ScalarExpression.integerProgramRun,
      PacketExpression.costedIntegerRun_value a,PacketExpression.costedIntegerRun_value b]
theorem PacketExpression.costedIntegerRun_value (e : PacketExpression) :
    e.costedIntegerRun.value=e.integerProgramRun := by
  cases e with
  | literal q => rfl
  | tuple a =>
    have h : (fun i => ((List.Vector.ofFn (fun j => (a j).costedIntegerRun)).get i).value)=
        (fun i => (a i).integerProgramRun) := by
      funext i
      simpa only [List.Vector.get_ofFn] using ScalarExpression.costedIntegerRun_value (a i)
    simp only [PacketExpression.costedIntegerRun,PacketExpression.integerProgramRun,h]
  | mul a b => simp only [PacketExpression.costedIntegerRun,PacketExpression.integerProgramRun,
      PacketExpression.costedIntegerRun_value a,PacketExpression.costedIntegerRun_value b]
  | inverse a => simp only [PacketExpression.costedIntegerRun,PacketExpression.integerProgramRun,
      PacketExpression.costedIntegerRun_value a]
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).costedIntegerRun)
    have h : (fun i => (stored.get i).value)=(fun i => (scores i).integerProgramRun) := by
      funext i
      simpa only [stored,List.Vector.get_ofFn] using ScalarExpression.costedIntegerRun_value (scores i)
    change (branches (integerMaxIndex 3 (fun i => (stored.get i).value))).costedIntegerRun.value=
      (branches (integerMaxIndex 3 (fun i => (scores i).integerProgramRun))).integerProgramRun
    rw [h]
    exact PacketExpression.costedIntegerRun_value _
end

mutual
theorem ScalarExpression.costedIntegerRun_rootCharge (e : ScalarExpression) :
    e.costedIntegerRun.rootCharge≤e.binaryRootPrimitiveOperations := by
  cases e with
  | literal q => exact le_refl _
  | stoppingThreshold t => exact le_refl _
  | add a b =>
    exact Nat.add_le_add (ScalarExpression.costedIntegerRun_rootCharge a)
      (ScalarExpression.costedIntegerRun_rootCharge b)
  | neg a => exact ScalarExpression.costedIntegerRun_rootCharge a
  | mul a b =>
    exact Nat.add_le_add (ScalarExpression.costedIntegerRun_rootCharge a)
      (ScalarExpression.costedIntegerRun_rootCharge b)
  | inv a => exact ScalarExpression.costedIntegerRun_rootCharge a
  | sqrt a p =>
    simpa only [ScalarExpression.costedIntegerRun,ScalarExpression.binaryRootPrimitiveOperations,
      ScalarExpression.costedIntegerRun_value,ScalarExpression.integerProgramRun_eq] using
      Nat.add_le_add_right (ScalarExpression.costedIntegerRun_rootCharge a)
        (a.integerRun.binaryRootPrimitiveOperations p)
  | meanMinus a => exact ScalarExpression.costedIntegerRun_rootCharge a
  | coordinate a i => exact PacketExpression.costedIntegerRun_rootCharge a
  | distance a b =>
    exact Nat.add_le_add (PacketExpression.costedIntegerRun_rootCharge a)
      (PacketExpression.costedIntegerRun_rootCharge b)
theorem PacketExpression.costedIntegerRun_rootCharge (e : PacketExpression) :
    e.costedIntegerRun.rootCharge≤e.binaryRootPrimitiveOperations := by
  cases e with
  | literal q => exact le_refl _
  | tuple a =>
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => ScalarExpression.costedIntegerRun_rootCharge (a i))
    simpa only [PacketExpression.costedIntegerRun,PacketExpression.binaryRootPrimitiveOperations,
      List.Vector.get_ofFn] using hs
  | mul a b =>
    exact Nat.add_le_add (PacketExpression.costedIntegerRun_rootCharge a)
      (PacketExpression.costedIntegerRun_rootCharge b)
  | inverse a => exact PacketExpression.costedIntegerRun_rootCharge a
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).costedIntegerRun)
    let j:=integerMaxIndex 3 (fun i => (stored.get i).value)
    have hs : (∑ i : Fin 4,(stored.get i).rootCharge)≤∑ i : Fin 4,(scores i).binaryRootPrimitiveOperations := by
      simpa only [stored,List.Vector.get_ofFn] using Finset.sum_le_sum (s:=Finset.univ)
        (fun i (_ : i∈Finset.univ) => ScalarExpression.costedIntegerRun_rootCharge (scores i))
    have hb : (branches j).costedIntegerRun.rootCharge≤∑ i : Fin 4,(branches i).binaryRootPrimitiveOperations :=
      (PacketExpression.costedIntegerRun_rootCharge (branches j)).trans (Finset.single_le_sum
        (fun i (_ : i∈Finset.univ) => Nat.zero_le ((branches i).binaryRootPrimitiveOperations)) (Finset.mem_univ j))
    exact Nat.add_le_add hs hb
end

theorem ScalarExpression.costedIntegerRun_correct (e : ScalarExpression) :
    e.costedIntegerRun.value.value=e.eval := by
  rw [ScalarExpression.costedIntegerRun_value]
  exact ScalarExpression.integerProgramRun_correct e

theorem PacketExpression.costedIntegerRun_correct (e : PacketExpression) :
    e.costedIntegerRun.value.value=e.eval := by
  rw [PacketExpression.costedIntegerRun_value]
  exact PacketExpression.integerProgramRun_correct e

end CircuitRecursion
