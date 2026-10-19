import CircuitNumerical.WordScalarConstants

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/-- The actual evaluation tree retains the executed local word programs.
Literal adapters are identified separately from their later Boolean work. -/
inductive WordExpressionTrace where
  | scalarLiteral : WordIntegerScalar → WordExpressionTrace
  | packetLiteral : List.Vector WordIntegerScalar 4 → WordPacketTupleResult → WordExpressionTrace
  | threshold : WordStoppingThresholdResult → WordExpressionTrace
  | add : WordExpressionTrace → WordExpressionTrace → WordScalarAdditionResult → WordExpressionTrace
  | neg : WordExpressionTrace → WordScalarNegationResult → WordExpressionTrace
  | mul : WordExpressionTrace → WordExpressionTrace → WordScalarMultiplicationResult → WordExpressionTrace
  | inv : WordExpressionTrace → WordScalarReciprocalResult → WordExpressionTrace
  | sqrt : WordExpressionTrace → WordScalarRootResult → WordExpressionTrace
  | meanMinus : WordExpressionTrace → WordScalarMeanMinusResult → WordExpressionTrace
  | coordinate : WordExpressionTrace → Fin 4 → WordExpressionTrace
  | distance : WordExpressionTrace → WordExpressionTrace → WordPacketDistanceResult → WordExpressionTrace
  | tuple : WordExpressionTrace → WordExpressionTrace → WordExpressionTrace → WordExpressionTrace →
      WordPacketTupleResult → WordExpressionTrace
  | packetMul : WordExpressionTrace → WordExpressionTrace → WordPacketMultiplicationResult → WordExpressionTrace
  | packetInverse : WordExpressionTrace → WordPacketInverseResult → WordExpressionTrace
  | selectMax : WordExpressionTrace → WordExpressionTrace → WordExpressionTrace → WordExpressionTrace →
      WordMaximumResult 3 → WordExpressionTrace → WordExpressionTrace

structure ScalarWordEvaluation where
  value : WordIntegerScalar
  trace : WordExpressionTrace

structure PacketWordEvaluation where
  value : WordIntegerPacket
  trace : WordExpressionTrace

/- Each recursive operand becomes one stored record. Tuples and selector
scores are materialized in a vector before any fields are read. Only the
selected branch is evaluated. No semantic decode is used to compute words. -/
mutual
def ScalarExpression.wordRun : ScalarExpression → ScalarWordEvaluation
  | .literal q =>
    let literal:=wordScalarLiteralProgram q
    ⟨literal,.scalarLiteral literal⟩
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
def PacketExpression.wordRun : PacketExpression → PacketWordEvaluation
  | .literal q =>
    let stored:=List.Vector.ofFn (fun i => wordScalarLiteralProgram (q.get i))
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
theorem ScalarExpression.wordRun_decode (e : ScalarExpression) :
    e.wordRun.value.decode=e.integerProgramRun := by
  cases e with
  | literal q => exact wordScalarLiteralProgram_decode q
  | stoppingThreshold t => exact wordStoppingThresholdProgram_decode t
  | add a b => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarAddProgram_decode,ScalarExpression.wordRun_decode a,ScalarExpression.wordRun_decode b]
  | neg a => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarNegateProgram_decode,ScalarExpression.wordRun_decode a]
  | mul a b => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarMultiplyProgram_decode,ScalarExpression.wordRun_decode a,ScalarExpression.wordRun_decode b]
  | inv a => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarInverseProgram_decode,ScalarExpression.wordRun_decode a]
  | sqrt a p => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarRootProgram_decode,ScalarExpression.wordRun_decode a,IntegerScalar.binaryRoot_eq]
  | meanMinus a => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordScalarMeanMinusProgram_decode,ScalarExpression.wordRun_decode a]
  | coordinate a i => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      WordIntegerPacket.coordinate_decode,PacketExpression.wordRun_decode a]
  | distance a b => simp only [ScalarExpression.wordRun,ScalarExpression.integerProgramRun,
      wordPacketDistanceProgram_decode,PacketExpression.wordRun_decode a,PacketExpression.wordRun_decode b]
theorem PacketExpression.wordRun_decode (e : PacketExpression) :
    e.wordRun.value.decode=e.integerProgramRun := by
  cases e with
  | literal q =>
    simp only [PacketExpression.wordRun,PacketExpression.integerProgramRun,wordPacketTupleProgram_decode,
      List.Vector.get_ofFn,wordScalarLiteralProgram_decode,IntegerPacket.ofVector]
  | tuple a =>
    simp only [PacketExpression.wordRun,PacketExpression.integerProgramRun,wordPacketTupleProgram_decode,
      List.Vector.get_map,List.Vector.get_ofFn,ScalarExpression.wordRun_decode]
  | mul a b => simp only [PacketExpression.wordRun,PacketExpression.integerProgramRun,
      wordPacketMultiplyProgram_decode,PacketExpression.wordRun_decode a,PacketExpression.wordRun_decode b]
  | inverse a => simp only [PacketExpression.wordRun,PacketExpression.integerProgramRun,
      wordPacketInverseProgram_decode,PacketExpression.wordRun_decode a]
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    have hscore : (fun i => ((stored.map ScalarWordEvaluation.value).get i).decode)=
        (fun i => (scores i).integerProgramRun) := by
      funext i
      simpa only [stored,List.Vector.get_map,List.Vector.get_ofFn] using ScalarExpression.wordRun_decode (scores i)
    have hindex : (wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)).index=
        integerMaxIndex 3 (fun i => (scores i).integerProgramRun) := by
      rw [wordMaximumProgram_index,hscore]
    change ((branches (wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)).index).wordRun).value.decode=_
    rw [hindex]
    exact PacketExpression.wordRun_decode _
end

theorem ScalarExpression.wordRun_correct (e : ScalarExpression) :
    e.wordRun.value.decode.value=e.eval := by
  rw [ScalarExpression.wordRun_decode]
  exact ScalarExpression.integerProgramRun_correct e

theorem PacketExpression.wordRun_correct (e : PacketExpression) :
    e.wordRun.value.decode.value=e.eval := by
  rw [PacketExpression.wordRun_decode]
  exact PacketExpression.integerProgramRun_correct e

end CircuitRecursion
