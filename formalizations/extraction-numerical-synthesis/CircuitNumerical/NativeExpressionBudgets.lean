import CircuitNumerical.NativePacketCache

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/- The interpretation is used only to define a conservative structural
budget and prove it. The native evaluator receives binary literal data
directly. No execution of interpret or a host literal adapter is charged or
needed in the native value program. -/
theorem NativeScalarExpression.wordRun_height (e : NativeScalarExpression) (B : ℕ)
    (h : e.interpret.integerBitBudget≤B) : IntegerScalarHeight e.wordRun.value.decode B := by
  rw [NativeScalarExpression.wordRun_decode,ScalarExpression.integerProgramRun_eq]
  exact IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height _) h

theorem NativePacketExpression.wordRun_height (e : NativePacketExpression) (B : ℕ)
    (h : e.interpret.integerBitBudget≤B) : IntegerPacketHeight e.wordRun.value.decode B := by
  rw [NativePacketExpression.wordRun_decode,PacketExpression.integerProgramRun_eq]
  exact IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height _) h

mutual
theorem NativeScalarExpression.wordRun_nodes (e : NativeScalarExpression) : e.wordRun.trace.nodes≤e.interpret.operations := by
  cases e with
  | literal q => change (1:ℕ)≤4;decide
  | stoppingThreshold t => change (1:ℕ)≤4;decide
  | add a b =>
    have ha:=NativeScalarExpression.wordRun_nodes a
    have hb:=NativeScalarExpression.wordRun_nodes b
    simp only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | neg a =>
    simpa only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret] using
      Nat.add_le_add_right (NativeScalarExpression.wordRun_nodes a) 1
  | mul a b =>
    have ha:=NativeScalarExpression.wordRun_nodes a
    have hb:=NativeScalarExpression.wordRun_nodes b
    simp only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | inv a =>
    simpa only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret] using
      Nat.add_le_add_right (NativeScalarExpression.wordRun_nodes a) 1
  | sqrt a p =>
    have h:=NativeScalarExpression.wordRun_nodes a
    simp only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | meanMinus a =>
    have h:=NativeScalarExpression.wordRun_nodes a
    simp only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | coordinate a i =>
    simpa only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret] using
      Nat.add_le_add_right (NativePacketExpression.wordRun_nodes a) 1
  | distance a b =>
    have ha:=NativePacketExpression.wordRun_nodes a
    have hb:=NativePacketExpression.wordRun_nodes b
    simp only [NativeScalarExpression.wordRun,WordExpressionTrace.nodes,ScalarExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
theorem NativePacketExpression.wordRun_nodes (e : NativePacketExpression) : e.wordRun.trace.nodes≤e.interpret.operations := by
  cases e with
  | literal q => change (1:ℕ)≤(rawPacketExpression q.decode).operations;rw [rawPacketExpression_operations];decide
  | tuple a =>
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => NativeScalarExpression.wordRun_nodes (a i))
    simp only [Fin.sum_univ_four] at hs
    simp only [NativePacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret,
      List.Vector.get_ofFn,Fin.sum_univ_four]
    omega
  | mul a b =>
    have ha:=NativePacketExpression.wordRun_nodes a
    have hb:=NativePacketExpression.wordRun_nodes b
    simp only [NativePacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | inverse a =>
    have h:=NativePacketExpression.wordRun_nodes a
    simp only [NativePacketExpression.wordRun,WordExpressionTrace.nodes,PacketExpression.operations,NativeScalarExpression.interpret,NativePacketExpression.interpret]
    omega
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    let selection:=wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)
    have hs:=Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => NativeScalarExpression.wordRun_nodes (scores i))
    have hb : (branches selection.index).wordRun.trace.nodes≤∑ i : Fin 4,(branches i).interpret.operations :=
      (NativePacketExpression.wordRun_nodes _).trans (Finset.single_le_sum
        (fun i (_ : i∈Finset.univ) => Nat.zero_le ((branches i).interpret.operations)) (Finset.mem_univ _))
    simp only [Fin.sum_univ_four] at hs
    change (scores 0).wordRun.trace.nodes+(scores 1).wordRun.trace.nodes+
      (scores 2).wordRun.trace.nodes+(scores 3).wordRun.trace.nodes+(branches selection.index).wordRun.trace.nodes+1≤_
    change _≤(∑ i : Fin 4,(scores i).interpret.operations)+(∑ i : Fin 4,(branches i).interpret.operations)+3
    rw [Fin.sum_univ_four (fun i => (scores i).interpret.operations)]
    omega
end

mutual
theorem NativeScalarExpression.wordRun_allLocalBound (e : NativeScalarExpression) (B : ℕ)
    (h : e.interpret.integerBitBudget≤B) : e.wordRun.trace.AllLocalBound (wordNodeBooleanBudget B) := by
  have hmin:=wordNodeBooleanBudget_minimum B
  cases e with
  | literal q => exact ⟨by change 4≤_;omega,True.intro⟩
  | stoppingThreshold t =>
    change 2*t+1≤B at h
    have hc:=wordStoppingThresholdProgram_actions t
    have hp:=wordNodeBooleanBudget_linear B 32 (t+2) (by omega) (by omega)
    exact ⟨by change (wordStoppingThresholdProgram t).actions+8≤_;omega,True.intro⟩
  | add a b =>
    change a.interpret.integerBitBudget+b.interpret.integerBitBudget+1≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hb : b.interpret.integerBitBudget≤B := by omega
    have hc:=wordScalarAddProgram_height_actions a.wordRun.value b.wordRun.value B
      (NativeScalarExpression.wordRun_height a B ha) (NativeScalarExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 500 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarAddProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound a B ha,NativeScalarExpression.wordRun_allLocalBound b B hb⟩
  | neg a =>
    change a.interpret.integerBitBudget≤B at h
    have hh:=NativeScalarExpression.wordRun_height a B h
    have hw:=(a.wordRun.value.height_width B hh).1
    have hc:=wordScalarNegateProgram_actions a.wordRun.value
    have hp:=wordNodeBooleanBudget_linear B 6 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarNegateProgram a.wordRun.value).normalizationRun.actions+8≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound a B h⟩
  | mul a b =>
    change a.interpret.integerBitBudget+b.interpret.integerBitBudget≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hb : b.interpret.integerBitBudget≤B := by omega
    have hc:=wordScalarMultiplyProgram_height_actions a.wordRun.value b.wordRun.value B
      (NativeScalarExpression.wordRun_height a B ha) (NativeScalarExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 208 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarMultiplyProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound a B ha,NativeScalarExpression.wordRun_allLocalBound b B hb⟩
  | inv a =>
    change a.interpret.integerBitBudget≤B at h
    have hp:=wordNodeBooleanBudget_linear B 20 1 (by omega) (by omega)
    exact ⟨by change (wordScalarInverseProgram a.wordRun.value).actions+8≤_
              simp only [WordScalarReciprocalResult.actions];omega,
      NativeScalarExpression.wordRun_allLocalBound a B h⟩
  | sqrt a p =>
    change a.interpret.integerBitBudget+2*p≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hc:=wordScalarRootProgram_height_actions a.wordRun.value B p (NativeScalarExpression.wordRun_height a B ha)
    have hp:=wordNodeBooleanBudget_square B 256 (B+2*p+2) (by omega) (by omega)
    exact ⟨by change (wordScalarRootProgram a.wordRun.value p).actions+8≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound a B ha⟩
  | meanMinus a =>
    change a.interpret.integerBitBudget+2≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hc:=wordScalarMeanMinusProgram_height_actions a.wordRun.value B (NativeScalarExpression.wordRun_height a B ha)
    have hp:=wordNodeBooleanBudget_square B 1000 (B+3) (by omega) (by omega)
    exact ⟨by change (wordScalarMeanMinusProgram a.wordRun.value).actions+8≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound a B ha⟩
  | coordinate a i =>
    change a.interpret.integerBitBudget≤B at h
    exact ⟨by change 8≤_;omega,NativePacketExpression.wordRun_allLocalBound a B h⟩
  | distance a b =>
    change 2*a.interpret.integerBitBudget+2*b.interpret.integerBitBudget+4≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hb : b.interpret.integerBitBudget≤B := by omega
    have hc:=wordPacketDistanceProgram_height_actions a.wordRun.value b.wordRun.value B
      (NativePacketExpression.wordRun_height a B ha) (NativePacketExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 11000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketDistanceProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      NativePacketExpression.wordRun_allLocalBound a B ha,NativePacketExpression.wordRun_allLocalBound b B hb⟩
theorem NativePacketExpression.wordRun_allLocalBound (e : NativePacketExpression) (B : ℕ)
    (h : e.interpret.integerBitBudget≤B) : e.wordRun.trace.AllLocalBound (wordNodeBooleanBudget B) := by
  have hmin:=wordNodeBooleanBudget_minimum B
  cases e with
  | literal a =>
    change (∑ i : Fin 4,(rawScalarExpression (a.decode.coordinate i)).integerBitBudget)≤B at h
    have hi : ∀ i,IntegerScalarHeight (a.coordinate i).decode B := by
      intro i
      rw [WordIntegerPacket.coordinate_decode]
      have hb : (rawScalarExpression (a.decode.coordinate i)).integerBitBudget≤B :=
        (Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
          Nat.zero_le ((rawScalarExpression (a.decode.coordinate j)).integerBitBudget)) (Finset.mem_univ i)).trans h
      rw [←rawScalarExpression_integerProgramRun (a.decode.coordinate i),ScalarExpression.integerProgramRun_eq]
      exact IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height _) hb
    have hc:=wordPacketTupleProgram_height_actions (List.Vector.ofFn a.coordinate) B
      (by intro i;simpa only [List.Vector.get_ofFn] using hi i)
    have hp:=wordNodeBooleanBudget_square B 13000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketTupleProgram (List.Vector.ofFn a.coordinate)).actions+8≤_;omega,True.intro⟩
  | tuple a =>
    change (∑ i : Fin 4,(a i).interpret.integerBitBudget)≤B at h
    have hi : ∀ i,(a i).interpret.integerBitBudget≤B := by
      intro i
      exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((a j).interpret.integerBitBudget))
        (Finset.mem_univ i)).trans h
    have hc:=wordPacketTupleProgram_height_actions
      ((List.Vector.ofFn (fun i => (a i).wordRun)).map ScalarWordEvaluation.value) B (by
        intro i
        simpa only [List.Vector.get_map,List.Vector.get_ofFn] using NativeScalarExpression.wordRun_height (a i) B (hi i))
    have hp:=wordNodeBooleanBudget_square B 13000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketTupleProgram
        ((List.Vector.ofFn (fun i => (a i).wordRun)).map ScalarWordEvaluation.value)).actions+16≤_;omega,
      NativeScalarExpression.wordRun_allLocalBound (a 0) B (hi 0),NativeScalarExpression.wordRun_allLocalBound (a 1) B (hi 1),
      NativeScalarExpression.wordRun_allLocalBound (a 2) B (hi 2),NativeScalarExpression.wordRun_allLocalBound (a 3) B (hi 3)⟩
  | mul a b =>
    change a.interpret.integerBitBudget+b.interpret.integerBitBudget+2≤B at h
    have ha : a.interpret.integerBitBudget≤B := by omega
    have hb : b.interpret.integerBitBudget≤B := by omega
    have hc:=wordPacketMultiplyProgram_height_actions a.wordRun.value b.wordRun.value B
      (NativePacketExpression.wordRun_height a B ha) (NativePacketExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 6200 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketMultiplyProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      NativePacketExpression.wordRun_allLocalBound a B ha,NativePacketExpression.wordRun_allLocalBound b B hb⟩
  | inverse a =>
    change a.interpret.integerBitBudget≤B at h
    have hc:=wordPacketInverseProgram_height_actions a.wordRun.value B (NativePacketExpression.wordRun_height a B h)
    have hp:=wordNodeBooleanBudget_linear B 40 (B+3) (by omega) (by omega)
    exact ⟨by change (wordPacketInverseProgram a.wordRun.value).actions+8≤_;omega,
      NativePacketExpression.wordRun_allLocalBound a B h⟩
  | selectMax scores branches =>
    change (∑ i : Fin 4,(scores i).interpret.integerBitBudget)+(∑ i : Fin 4,(branches i).interpret.integerBitBudget)≤B at h
    have hs : ∀ i,(scores i).interpret.integerBitBudget≤B := by
      intro i
      have hi:=Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores j).interpret.integerBitBudget)) (Finset.mem_univ i)
      omega
    have hb : ∀ i,(branches i).interpret.integerBitBudget≤B := by
      intro i
      have hi:=Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((branches j).interpret.integerBitBudget)) (Finset.mem_univ i)
      omega
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    let selection:=wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)
    have hc:=wordMaximumProgram_four_height_actions (stored.map ScalarWordEvaluation.value) B (by
      intro i
      simpa only [stored,List.Vector.get_map,List.Vector.get_ofFn] using NativeScalarExpression.wordRun_height (scores i) B (hs i))
    have hp:=wordNodeBooleanBudget_square B 1300 (B+2) (by omega) (by omega)
    refine ⟨?_,NativeScalarExpression.wordRun_allLocalBound (scores 0) B (hs 0),
      NativeScalarExpression.wordRun_allLocalBound (scores 1) B (hs 1),
      NativeScalarExpression.wordRun_allLocalBound (scores 2) B (hs 2),
      NativeScalarExpression.wordRun_allLocalBound (scores 3) B (hs 3),
      NativePacketExpression.wordRun_allLocalBound (branches selection.index) B (hb _)⟩
    change selection.actions+16≤_
    change selection.actions≤_ at hc
    omega
end

theorem NativeScalarExpression.wordRun_booleanActions (e : NativeScalarExpression) (B : ℕ) (h : e.interpret.integerBitBudget≤B) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget B*e.interpret.operations :=
  (WordExpressionTrace.booleanActions_le _ _ (NativeScalarExpression.wordRun_allLocalBound e B h)).trans
    (Nat.mul_le_mul_left _ (NativeScalarExpression.wordRun_nodes e))

theorem NativePacketExpression.wordRun_booleanActions (e : NativePacketExpression) (B : ℕ) (h : e.interpret.integerBitBudget≤B) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget B*e.interpret.operations :=
  (WordExpressionTrace.booleanActions_le _ _ (NativePacketExpression.wordRun_allLocalBound e B h)).trans
    (Nat.mul_le_mul_left _ (NativePacketExpression.wordRun_nodes e))

theorem NativeScalarExpression.wordRun_booleanActions_internal (e : NativeScalarExpression) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget e.interpret.integerBitBudget*e.interpret.operations :=
  NativeScalarExpression.wordRun_booleanActions e _ (le_refl _)

theorem NativePacketExpression.wordRun_booleanActions_internal (e : NativePacketExpression) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget e.interpret.integerBitBudget*e.interpret.operations :=
  NativePacketExpression.wordRun_booleanActions e _ (le_refl _)

end CircuitRecursion
