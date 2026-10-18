import CircuitNumerical.NativeWordExpressions

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/- This program never calls Nat.bits, wordScalarInput, a rational literal
adapter, or interpret. WordExpressionTrace is reused only for the numerical
Boolean charge/tree: its host literalAdapters statistic is not a native
adapter-call count, because native leaves directly receive binary data. -/
mutual
def NativeScalarExpression.wordRun : NativeScalarExpression → ScalarWordEvaluation
  | .literal a => ⟨a,.scalarLiteral a⟩
  | .stoppingThreshold t =>
    let run:=wordStoppingThresholdProgram t
    ⟨run.scalar,.threshold run⟩
  | .add a b =>
    let x:=a.wordRun
    let y:=b.wordRun
    let run:=wordScalarAddProgram x.value y.value
    ⟨run.scalar,.add x.trace y.trace run⟩
  | .neg a =>
    let x:=a.wordRun
    let run:=wordScalarNegateProgram x.value
    ⟨run.scalar,.neg x.trace run⟩
  | .mul a b =>
    let x:=a.wordRun
    let y:=b.wordRun
    let run:=wordScalarMultiplyProgram x.value y.value
    ⟨run.scalar,.mul x.trace y.trace run⟩
  | .inv a =>
    let x:=a.wordRun
    let run:=wordScalarInverseProgram x.value
    ⟨run.scalar,.inv x.trace run⟩
  | .sqrt a p =>
    let x:=a.wordRun
    let run:=wordScalarRootProgram x.value p
    ⟨run.scalar,.sqrt x.trace run⟩
  | .meanMinus a =>
    let x:=a.wordRun
    let run:=wordScalarMeanMinusProgram x.value
    ⟨run.scalar,.meanMinus x.trace run⟩
  | .coordinate a i =>
    let x:=a.wordRun
    ⟨x.value.coordinate i,.coordinate x.trace i⟩
  | .distance a b =>
    let x:=a.wordRun
    let y:=b.wordRun
    let run:=wordPacketDistanceProgram x.value y.value
    ⟨run.scalar,.distance x.trace y.trace run⟩
def NativePacketExpression.wordRun : NativePacketExpression → PacketWordEvaluation
  | .literal a =>
    let stored:=List.Vector.ofFn a.coordinate
    let run:=wordPacketTupleProgram stored
    ⟨run.packet,.packetLiteral stored run⟩
  | .tuple a =>
    let stored:=List.Vector.ofFn (fun i => (a i).wordRun)
    let run:=wordPacketTupleProgram (stored.map ScalarWordEvaluation.value)
    ⟨run.packet,.tuple (stored.get 0).trace (stored.get 1).trace (stored.get 2).trace (stored.get 3).trace run⟩
  | .mul a b =>
    let x:=a.wordRun
    let y:=b.wordRun
    let run:=wordPacketMultiplyProgram x.value y.value
    ⟨run.packet,.packetMul x.trace y.trace run⟩
  | .inverse a =>
    let x:=a.wordRun
    let run:=wordPacketInverseProgram x.value
    ⟨run.packet,.packetInverse x.trace run⟩
  | .selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    let selection:=wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)
    let selected:=(branches selection.index).wordRun
    ⟨selected.value,.selectMax (stored.get 0).trace (stored.get 1).trace
      (stored.get 2).trace (stored.get 3).trace selection selected.trace⟩
end

mutual
theorem NativeScalarExpression.wordRun_decode (e : NativeScalarExpression) :
    e.wordRun.value.decode=e.interpret.integerProgramRun := by
  cases e with
  | literal a => exact (rawScalarExpression_integerProgramRun a.decode).symm
  | stoppingThreshold t => exact wordStoppingThresholdProgram_decode t
  | add a b => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarAddProgram_decode,NativeScalarExpression.wordRun_decode a,NativeScalarExpression.wordRun_decode b]
  | neg a => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarNegateProgram_decode,NativeScalarExpression.wordRun_decode a]
  | mul a b => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarMultiplyProgram_decode,NativeScalarExpression.wordRun_decode a,NativeScalarExpression.wordRun_decode b]
  | inv a => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarInverseProgram_decode,NativeScalarExpression.wordRun_decode a]
  | sqrt a p => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarRootProgram_decode,NativeScalarExpression.wordRun_decode a,IntegerScalar.binaryRoot_eq]
  | meanMinus a => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordScalarMeanMinusProgram_decode,NativeScalarExpression.wordRun_decode a]
  | coordinate a i => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      WordIntegerPacket.coordinate_decode,NativePacketExpression.wordRun_decode a]
  | distance a b => simp only [NativeScalarExpression.wordRun,NativeScalarExpression.interpret,ScalarExpression.integerProgramRun,
      wordPacketDistanceProgram_decode,NativePacketExpression.wordRun_decode a,NativePacketExpression.wordRun_decode b]
theorem NativePacketExpression.wordRun_decode (e : NativePacketExpression) :
    e.wordRun.value.decode=e.interpret.integerProgramRun := by
  cases e with
  | literal a =>
    simp only [NativePacketExpression.wordRun,NativePacketExpression.interpret,wordPacketTupleProgram_decode,
      List.Vector.get_ofFn,WordIntegerPacket.coordinate_decode,rawPacketExpression_integerProgramRun]
  | tuple a =>
    simp only [NativePacketExpression.wordRun,NativePacketExpression.interpret,PacketExpression.integerProgramRun,
      wordPacketTupleProgram_decode,List.Vector.get_map,List.Vector.get_ofFn,NativeScalarExpression.wordRun_decode]
  | mul a b => simp only [NativePacketExpression.wordRun,NativePacketExpression.interpret,PacketExpression.integerProgramRun,
      wordPacketMultiplyProgram_decode,NativePacketExpression.wordRun_decode a,NativePacketExpression.wordRun_decode b]
  | inverse a => simp only [NativePacketExpression.wordRun,NativePacketExpression.interpret,PacketExpression.integerProgramRun,
      wordPacketInverseProgram_decode,NativePacketExpression.wordRun_decode a]
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    have hscore : (fun i => ((stored.map ScalarWordEvaluation.value).get i).decode)=
        (fun i => (scores i).interpret.integerProgramRun) := by
      funext i
      simpa only [stored,List.Vector.get_map,List.Vector.get_ofFn] using NativeScalarExpression.wordRun_decode (scores i)
    have hindex : (wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)).index=
        integerMaxIndex 3 (fun i => (scores i).interpret.integerProgramRun) := by
      rw [wordMaximumProgram_index,hscore]
    change ((branches (wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)).index).wordRun).value.decode=_
    rw [hindex]
    exact NativePacketExpression.wordRun_decode _
end

theorem NativeScalarExpression.wordRun_correct (e : NativeScalarExpression) :
    e.wordRun.value.decode.value=e.interpret.eval := by
  rw [NativeScalarExpression.wordRun_decode]
  exact ScalarExpression.integerProgramRun_correct e.interpret

theorem NativePacketExpression.wordRun_correct (e : NativePacketExpression) :
    e.wordRun.value.decode.value=e.interpret.eval := by
  rw [NativePacketExpression.wordRun_decode]
  exact PacketExpression.integerProgramRun_correct e.interpret

end CircuitRecursion
