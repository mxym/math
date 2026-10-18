import CircuitNumerical.WordExpressionEvaluation

namespace CircuitRecursion

/-- Local Boolean/list/record model charge. Host literal-input adapters,
annotation arithmetic and general machine allocation/indexing are separate. -/
def WordExpressionTrace.localActions : WordExpressionTrace → ℕ
  | .scalarLiteral _ => 4
  | .packetLiteral _ run => run.actions+8
  | .threshold run => run.actions+8
  | .add _ _ run => run.actions+8
  | .neg _ run => run.normalizationRun.actions+8
  | .mul _ _ run => run.actions+8
  | .inv _ run => run.actions+8
  | .sqrt _ run => run.actions+8
  | .meanMinus _ run => run.actions+8
  | .coordinate _ _ => 8
  | .distance _ _ run => run.actions+8
  | .tuple _ _ _ _ run => run.actions+16
  | .packetMul _ _ run => run.actions+8
  | .packetInverse _ run => run.actions+8
  | .selectMax _ _ _ _ selection _ => selection.actions+16

def WordExpressionTrace.booleanActions (trace : WordExpressionTrace) : ℕ :=
  trace.localActions+match trace with
  | .scalarLiteral _ | .packetLiteral _ _ | .threshold _ => 0
  | .add x y _ | .mul x y _ | .distance x y _ | .packetMul x y _ => x.booleanActions+y.booleanActions
  | .neg x _ | .inv x _ | .sqrt x _ | .meanMinus x _ | .coordinate x _ | .packetInverse x _ => x.booleanActions
  | .tuple a b c d _ => a.booleanActions+b.booleanActions+c.booleanActions+d.booleanActions
  | .selectMax a b c d _ selected =>
      a.booleanActions+b.booleanActions+c.booleanActions+d.booleanActions+selected.booleanActions

def WordExpressionTrace.nodes : WordExpressionTrace → ℕ
  | .scalarLiteral _ | .packetLiteral _ _ | .threshold _ => 1
  | .add x y _ | .mul x y _ | .distance x y _ | .packetMul x y _ => x.nodes+y.nodes+1
  | .neg x _ | .inv x _ | .sqrt x _ | .meanMinus x _ | .coordinate x _ | .packetInverse x _ => x.nodes+1
  | .tuple a b c d _ => a.nodes+b.nodes+c.nodes+d.nodes+1
  | .selectMax a b c d _ selected => a.nodes+b.nodes+c.nodes+d.nodes+selected.nodes+1

def WordExpressionTrace.literalAdapters : WordExpressionTrace → ℕ
  | .scalarLiteral _ => 1
  | .packetLiteral _ _ => 4
  | .threshold _ => 0
  | .add x y _ | .mul x y _ | .distance x y _ | .packetMul x y _ => x.literalAdapters+y.literalAdapters
  | .neg x _ | .inv x _ | .sqrt x _ | .meanMinus x _ | .coordinate x _ | .packetInverse x _ => x.literalAdapters
  | .tuple a b c d _ => a.literalAdapters+b.literalAdapters+c.literalAdapters+d.literalAdapters
  | .selectMax a b c d _ selected =>
      a.literalAdapters+b.literalAdapters+c.literalAdapters+d.literalAdapters+selected.literalAdapters

/-- Output volume of the executed input adapters, not their execution cost. -/
def WordExpressionTrace.inputVolume : WordExpressionTrace → ℕ
  | .scalarLiteral a => a.numerator.bits.length+a.denominator.length+1
  | .packetLiteral inputs _ =>
      ∑ i : Fin 4,((inputs.get i).numerator.bits.length+(inputs.get i).denominator.length+1)
  | .threshold _ => 0
  | .add x y _ | .mul x y _ | .distance x y _ | .packetMul x y _ => x.inputVolume+y.inputVolume
  | .neg x _ | .inv x _ | .sqrt x _ | .meanMinus x _ | .coordinate x _ | .packetInverse x _ => x.inputVolume
  | .tuple a b c d _ => a.inputVolume+b.inputVolume+c.inputVolume+d.inputVolume
  | .selectMax a b c d _ selected => a.inputVolume+b.inputVolume+c.inputVolume+d.inputVolume+selected.inputVolume

theorem WordExpressionTrace.literalAdapters_le_nodes (trace : WordExpressionTrace) :
    trace.literalAdapters≤4*trace.nodes := by
  induction trace <;> simp_all only [literalAdapters,nodes] <;> omega

def WordExpressionTrace.AllLocalBound (C : ℕ) (trace : WordExpressionTrace) : Prop :=
  trace.localActions≤C ∧ match trace with
  | .scalarLiteral _ | .packetLiteral _ _ | .threshold _ => True
  | .add x y _ | .mul x y _ | .distance x y _ | .packetMul x y _ => x.AllLocalBound C ∧ y.AllLocalBound C
  | .neg x _ | .inv x _ | .sqrt x _ | .meanMinus x _ | .coordinate x _ | .packetInverse x _ => x.AllLocalBound C
  | .tuple a b c d _ => a.AllLocalBound C ∧ b.AllLocalBound C ∧ c.AllLocalBound C ∧ d.AllLocalBound C
  | .selectMax a b c d _ selected =>
      a.AllLocalBound C ∧ b.AllLocalBound C ∧ c.AllLocalBound C ∧ d.AllLocalBound C ∧ selected.AllLocalBound C

theorem WordExpressionTrace.booleanActions_le (trace : WordExpressionTrace) (C : ℕ)
    (h : trace.AllLocalBound C) : trace.booleanActions≤C*trace.nodes := by
  induction trace <;> simp_all only [AllLocalBound,booleanActions,nodes,true_implies] <;> nlinarith

mutual
theorem ScalarExpression.wordRun_nodes (e : ScalarExpression) : e.wordRun.trace.nodes≤e.operations := by
  cases e with
  | literal q => exact le_refl _
  | stoppingThreshold t => change (1:ℕ)≤4;decide
  | add a b =>
    have ha:=ScalarExpression.wordRun_nodes a
    have hb:=ScalarExpression.wordRun_nodes b
    simp only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations]
    omega
  | neg a =>
    simpa only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations] using
      Nat.add_le_add_right (ScalarExpression.wordRun_nodes a) 1
  | mul a b =>
    have ha:=ScalarExpression.wordRun_nodes a
    have hb:=ScalarExpression.wordRun_nodes b
    simp only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations]
    omega
  | inv a =>
    simpa only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations] using
      Nat.add_le_add_right (ScalarExpression.wordRun_nodes a) 1
  | sqrt a p =>
    have h:=ScalarExpression.wordRun_nodes a
    simp only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations]
    omega
  | meanMinus a =>
    have h:=ScalarExpression.wordRun_nodes a
    simp only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations]
    omega
  | coordinate a i =>
    simpa only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations] using
      Nat.add_le_add_right (PacketExpression.wordRun_nodes a) 1
  | distance a b =>
    have ha:=PacketExpression.wordRun_nodes a
    have hb:=PacketExpression.wordRun_nodes b
    simp only [ScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations]
    omega
theorem PacketExpression.wordRun_nodes (e : PacketExpression) : e.wordRun.trace.nodes≤e.operations := by
  cases e with
  | literal q => exact le_refl _
  | tuple a =>
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => ScalarExpression.wordRun_nodes (a i))
    simp only [Fin.sum_univ_four] at hs
    simp only [PacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations,
      List.Vector.get_ofFn,Fin.sum_univ_four]
    omega
  | mul a b =>
    have ha:=PacketExpression.wordRun_nodes a
    have hb:=PacketExpression.wordRun_nodes b
    simp only [PacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations]
    omega
  | inverse a =>
    have h:=PacketExpression.wordRun_nodes a
    simp only [PacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations]
    omega
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    let selection:=wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => ScalarExpression.wordRun_nodes (scores i))
    have hb : (branches selection.index).wordRun.trace.nodes≤∑ i : Fin 4,(branches i).operations :=
      (PacketExpression.wordRun_nodes _).trans (Finset.single_le_sum
        (fun i (_ : i∈Finset.univ) => Nat.zero_le ((branches i).operations)) (Finset.mem_univ _))
    simp only [Fin.sum_univ_four] at hs
    change (scores 0).wordRun.trace.nodes+(scores 1).wordRun.trace.nodes+
      (scores 2).wordRun.trace.nodes+(scores 3).wordRun.trace.nodes+(branches selection.index).wordRun.trace.nodes+1≤_
    change _≤(∑ i : Fin 4,(scores i).operations)+(∑ i : Fin 4,(branches i).operations)+3
    rw [Fin.sum_univ_four (fun i => (scores i).operations)]
    omega
end

theorem ScalarExpression.wordRun_literalAdapters (e : ScalarExpression) :
    e.wordRun.trace.literalAdapters≤4*e.operations :=
  (WordExpressionTrace.literalAdapters_le_nodes _).trans (Nat.mul_le_mul_left 4 (ScalarExpression.wordRun_nodes e))

theorem PacketExpression.wordRun_literalAdapters (e : PacketExpression) :
    e.wordRun.trace.literalAdapters≤4*e.operations :=
  (WordExpressionTrace.literalAdapters_le_nodes _).trans (Nat.mul_le_mul_left 4 (PacketExpression.wordRun_nodes e))

end CircuitRecursion
