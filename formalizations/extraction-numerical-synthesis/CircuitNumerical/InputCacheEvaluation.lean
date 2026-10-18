import CircuitNumerical.InputCacheExpressions

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure InputScalarEvaluation (m : ℕ) where
  numerical : ScalarWordEvaluation
  reads : List (NativeCacheInputRead m)
structure InputPacketEvaluation (m : ℕ) where
  numerical : PacketWordEvaluation
  reads : List (NativeCacheInputRead m)

def inputFourReads {m : ℕ} {α : Type*} (values : List.Vector α 4)
    (reads : α → List (NativeCacheInputRead m)) : List (NativeCacheInputRead m) :=
  reads (values.get 0)++reads (values.get 1)++reads (values.get 2)++reads (values.get 3)

/- Every recursive child is stored once, and each visited input leaf runs
one actual list-cache read. Both the numerical record and query records are
retained. Only the selected branch executes. Resolution is never called. -/
mutual
def InputScalarExpression.inputRun {m P : ℕ} (cache : NativeCacheEnvironment m P) :
    InputScalarExpression m → InputScalarEvaluation m
  | .literal a => ⟨⟨a,.scalarLiteral a⟩,[]⟩
  | .stoppingThreshold t =>
    let run:=wordStoppingThresholdProgram t
    ⟨⟨run.scalar,.threshold run⟩,[]⟩
  | .add a b =>
    let x:=a.inputRun cache
    let y:=b.inputRun cache
    let run:=wordScalarAddProgram x.numerical.value y.numerical.value
    ⟨⟨run.scalar,.add x.numerical.trace y.numerical.trace run⟩,x.reads++y.reads⟩
  | .neg a =>
    let x:=a.inputRun cache
    let run:=wordScalarNegateProgram x.numerical.value
    ⟨⟨run.scalar,.neg x.numerical.trace run⟩,x.reads⟩
  | .mul a b =>
    let x:=a.inputRun cache
    let y:=b.inputRun cache
    let run:=wordScalarMultiplyProgram x.numerical.value y.numerical.value
    ⟨⟨run.scalar,.mul x.numerical.trace y.numerical.trace run⟩,x.reads++y.reads⟩
  | .inv a =>
    let x:=a.inputRun cache
    let run:=wordScalarInverseProgram x.numerical.value
    ⟨⟨run.scalar,.inv x.numerical.trace run⟩,x.reads⟩
  | .sqrt a p =>
    let x:=a.inputRun cache
    let run:=wordScalarRootProgram x.numerical.value p
    ⟨⟨run.scalar,.sqrt x.numerical.trace run⟩,x.reads⟩
  | .meanMinus a =>
    let x:=a.inputRun cache
    let run:=wordScalarMeanMinusProgram x.numerical.value
    ⟨⟨run.scalar,.meanMinus x.numerical.trace run⟩,x.reads⟩
  | .coordinate a i =>
    let x:=a.inputRun cache
    ⟨⟨x.numerical.value.coordinate i,.coordinate x.numerical.trace i⟩,x.reads⟩
  | .distance a b =>
    let x:=a.inputRun cache
    let y:=b.inputRun cache
    let run:=wordPacketDistanceProgram x.numerical.value y.numerical.value
    ⟨⟨run.scalar,.distance x.numerical.trace y.numerical.trace run⟩,x.reads++y.reads⟩
def InputPacketExpression.inputRun {m P : ℕ} (cache : NativeCacheEnvironment m P) :
    InputPacketExpression m → InputPacketEvaluation m
  | .literal a => ⟨(NativePacketExpression.literal a).wordRun,[]⟩
  | .input label q =>
    let read:=nativeCacheInputRead cache label q
    let numerical:=(NativePacketExpression.literal read.packet).wordRun
    ⟨numerical,[read]⟩
  | .tuple a =>
    let stored:=List.Vector.ofFn (fun i => (a i).inputRun cache)
    let run:=wordPacketTupleProgram (stored.map (fun x => x.numerical.value))
    ⟨⟨run.packet,.tuple (stored.get 0).numerical.trace (stored.get 1).numerical.trace
      (stored.get 2).numerical.trace (stored.get 3).numerical.trace run⟩,inputFourReads stored InputScalarEvaluation.reads⟩
  | .mul a b =>
    let x:=a.inputRun cache
    let y:=b.inputRun cache
    let run:=wordPacketMultiplyProgram x.numerical.value y.numerical.value
    ⟨⟨run.packet,.packetMul x.numerical.trace y.numerical.trace run⟩,x.reads++y.reads⟩
  | .inverse a =>
    let x:=a.inputRun cache
    let run:=wordPacketInverseProgram x.numerical.value
    ⟨⟨run.packet,.packetInverse x.numerical.trace run⟩,x.reads⟩
  | .selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).inputRun cache)
    let selection:=wordMaximumProgram 3 (stored.map (fun x => x.numerical.value))
    let selected:=(branches selection.index).inputRun cache
    ⟨⟨selected.numerical.value,.selectMax (stored.get 0).numerical.trace (stored.get 1).numerical.trace
      (stored.get 2).numerical.trace (stored.get 3).numerical.trace selection selected.numerical.trace⟩,
      inputFourReads stored InputScalarEvaluation.reads++selected.reads⟩
end

theorem inputVectorMapOfFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    (List.Vector.ofFn f).map g=List.Vector.ofFn (fun i => g (f i)) := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,List.Vector.get_ofFn]

mutual
theorem InputScalarExpression.inputRun_numerical {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) : (e.inputRun cache).numerical=(e.resolve cache).wordRun := by
  cases e with
  | literal a => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a,InputScalarExpression.inputRun_numerical cache b]
  | neg a => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a]
  | mul a b => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a,InputScalarExpression.inputRun_numerical cache b]
  | inv a => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a]
  | sqrt a p => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a]
  | meanMinus a => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputScalarExpression.inputRun_numerical cache a]
  | coordinate a i => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputPacketExpression.inputRun_numerical cache a]
  | distance a b => simp only [InputScalarExpression.inputRun,InputScalarExpression.resolve,NativeScalarExpression.wordRun,
      InputPacketExpression.inputRun_numerical cache a,InputPacketExpression.inputRun_numerical cache b]
theorem InputPacketExpression.inputRun_numerical {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputPacketExpression m) : (e.inputRun cache).numerical=(e.resolve cache).wordRun := by
  cases e with
  | literal a => rfl
  | input label q => rfl
  | tuple a => simp only [InputPacketExpression.inputRun,InputPacketExpression.resolve,NativePacketExpression.wordRun,
      inputVectorMapOfFn,List.Vector.get_ofFn,InputScalarExpression.inputRun_numerical]
  | mul a b => simp only [InputPacketExpression.inputRun,InputPacketExpression.resolve,NativePacketExpression.wordRun,
      InputPacketExpression.inputRun_numerical cache a,InputPacketExpression.inputRun_numerical cache b]
  | inverse a => simp only [InputPacketExpression.inputRun,InputPacketExpression.resolve,NativePacketExpression.wordRun,
      InputPacketExpression.inputRun_numerical cache a]
  | selectMax scores branches => simp only [InputPacketExpression.inputRun,InputPacketExpression.resolve,NativePacketExpression.wordRun,
      inputVectorMapOfFn,List.Vector.get_ofFn,InputScalarExpression.inputRun_numerical,InputPacketExpression.inputRun_numerical]
end

end CircuitRecursion
