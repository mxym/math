import CircuitNumerical.WordNodeBudget

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/- No local-cost certificate is supplied to this theorem. The actual AST
integerBitBudget internally bounds every operand and every root precision. -/
mutual
theorem ScalarExpression.wordRun_allLocalBound (e : ScalarExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.wordRun.trace.AllLocalBound (wordNodeBooleanBudget B) := by
  have hmin:=wordNodeBooleanBudget_minimum B
  cases e with
  | literal q => exact ⟨by change 4≤_;omega,True.intro⟩
  | stoppingThreshold t =>
    change 2*t+1≤B at h
    have hc:=wordStoppingThresholdProgram_actions t
    have hp:=wordNodeBooleanBudget_linear B 32 (t+2) (by omega) (by omega)
    exact ⟨by change (wordStoppingThresholdProgram t).actions+8≤_;omega,True.intro⟩
  | add a b =>
    change a.integerBitBudget+b.integerBitBudget+1≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hb : b.integerBitBudget≤B := by omega
    have hc:=wordScalarAddProgram_height_actions a.wordRun.value b.wordRun.value B
      (ScalarExpression.wordRun_height a B ha) (ScalarExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 500 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarAddProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      ScalarExpression.wordRun_allLocalBound a B ha,ScalarExpression.wordRun_allLocalBound b B hb⟩
  | neg a =>
    change a.integerBitBudget≤B at h
    have hh:=ScalarExpression.wordRun_height a B h
    have hw:=(a.wordRun.value.height_width B hh).1
    have hc:=wordScalarNegateProgram_actions a.wordRun.value
    have hp:=wordNodeBooleanBudget_linear B 6 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarNegateProgram a.wordRun.value).normalizationRun.actions+8≤_;omega,
      ScalarExpression.wordRun_allLocalBound a B h⟩
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hb : b.integerBitBudget≤B := by omega
    have hc:=wordScalarMultiplyProgram_height_actions a.wordRun.value b.wordRun.value B
      (ScalarExpression.wordRun_height a B ha) (ScalarExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 208 (B+2) (by omega) (by omega)
    exact ⟨by change (wordScalarMultiplyProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      ScalarExpression.wordRun_allLocalBound a B ha,ScalarExpression.wordRun_allLocalBound b B hb⟩
  | inv a =>
    change a.integerBitBudget≤B at h
    have hp:=wordNodeBooleanBudget_linear B 20 1 (by omega) (by omega)
    exact ⟨by change (wordScalarInverseProgram a.wordRun.value).actions+8≤_
              simp only [WordScalarReciprocalResult.actions];omega,
      ScalarExpression.wordRun_allLocalBound a B h⟩
  | sqrt a p =>
    change a.integerBitBudget+2*p≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hc:=wordScalarRootProgram_height_actions a.wordRun.value B p (ScalarExpression.wordRun_height a B ha)
    have hp:=wordNodeBooleanBudget_square B 256 (B+2*p+2) (by omega) (by omega)
    exact ⟨by change (wordScalarRootProgram a.wordRun.value p).actions+8≤_;omega,
      ScalarExpression.wordRun_allLocalBound a B ha⟩
  | meanMinus a =>
    change a.integerBitBudget+2≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hc:=wordScalarMeanMinusProgram_height_actions a.wordRun.value B (ScalarExpression.wordRun_height a B ha)
    have hp:=wordNodeBooleanBudget_square B 1000 (B+3) (by omega) (by omega)
    exact ⟨by change (wordScalarMeanMinusProgram a.wordRun.value).actions+8≤_;omega,
      ScalarExpression.wordRun_allLocalBound a B ha⟩
  | coordinate a i =>
    change a.integerBitBudget≤B at h
    exact ⟨by change 8≤_;omega,PacketExpression.wordRun_allLocalBound a B h⟩
  | distance a b =>
    change 2*a.integerBitBudget+2*b.integerBitBudget+4≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hb : b.integerBitBudget≤B := by omega
    have hc:=wordPacketDistanceProgram_height_actions a.wordRun.value b.wordRun.value B
      (PacketExpression.wordRun_height a B ha) (PacketExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 11000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketDistanceProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      PacketExpression.wordRun_allLocalBound a B ha,PacketExpression.wordRun_allLocalBound b B hb⟩
theorem PacketExpression.wordRun_allLocalBound (e : PacketExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.wordRun.trace.AllLocalBound (wordNodeBooleanBudget B) := by
  have hmin:=wordNodeBooleanBudget_minimum B
  cases e with
  | literal q =>
    change (∑ i : Fin 4,rationalBinaryExponent (q.get i))≤B at h
    have hi : ∀ i,IntegerScalarHeight (wordScalarLiteralProgram (q.get i)).decode B := by
      intro i
      rw [wordScalarLiteralProgram_decode]
      apply IntegerScalarHeight.mono _ _ _ (rationalBinaryExponent_height (q.get i))
      exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le (rationalBinaryExponent (q.get j)))
        (Finset.mem_univ i)).trans h
    have hc:=wordPacketTupleProgram_height_actions (List.Vector.ofFn (fun i => wordScalarLiteralProgram (q.get i))) B
      (by intro i;simpa only [List.Vector.get_ofFn] using hi i)
    have hp:=wordNodeBooleanBudget_square B 13000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketTupleProgram (List.Vector.ofFn (fun i => wordScalarLiteralProgram (q.get i)))).actions+8≤_;omega,
      True.intro⟩
  | tuple a =>
    change (∑ i : Fin 4,(a i).integerBitBudget)≤B at h
    have hi : ∀ i,(a i).integerBitBudget≤B := by
      intro i
      exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((a j).integerBitBudget))
        (Finset.mem_univ i)).trans h
    have hc:=wordPacketTupleProgram_height_actions
      ((List.Vector.ofFn (fun i => (a i).wordRun)).map ScalarWordEvaluation.value) B (by
        intro i
        simpa only [List.Vector.get_map,List.Vector.get_ofFn] using ScalarExpression.wordRun_height (a i) B (hi i))
    have hp:=wordNodeBooleanBudget_square B 13000 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketTupleProgram
        ((List.Vector.ofFn (fun i => (a i).wordRun)).map ScalarWordEvaluation.value)).actions+16≤_;omega,
      ScalarExpression.wordRun_allLocalBound (a 0) B (hi 0),ScalarExpression.wordRun_allLocalBound (a 1) B (hi 1),
      ScalarExpression.wordRun_allLocalBound (a 2) B (hi 2),ScalarExpression.wordRun_allLocalBound (a 3) B (hi 3)⟩
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget+2≤B at h
    have ha : a.integerBitBudget≤B := by omega
    have hb : b.integerBitBudget≤B := by omega
    have hc:=wordPacketMultiplyProgram_height_actions a.wordRun.value b.wordRun.value B
      (PacketExpression.wordRun_height a B ha) (PacketExpression.wordRun_height b B hb)
    have hp:=wordNodeBooleanBudget_square B 6200 (B+2) (by omega) (by omega)
    exact ⟨by change (wordPacketMultiplyProgram a.wordRun.value b.wordRun.value).actions+8≤_;omega,
      PacketExpression.wordRun_allLocalBound a B ha,PacketExpression.wordRun_allLocalBound b B hb⟩
  | inverse a =>
    change a.integerBitBudget≤B at h
    have hc:=wordPacketInverseProgram_height_actions a.wordRun.value B (PacketExpression.wordRun_height a B h)
    have hp:=wordNodeBooleanBudget_linear B 40 (B+3) (by omega) (by omega)
    exact ⟨by change (wordPacketInverseProgram a.wordRun.value).actions+8≤_;omega,
      PacketExpression.wordRun_allLocalBound a B h⟩
  | selectMax scores branches =>
    change (∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)≤B at h
    have hs : ∀ i,(scores i).integerBitBudget≤B := by
      intro i
      have hi:=Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores j).integerBitBudget)) (Finset.mem_univ i)
      omega
    have hb : ∀ i,(branches i).integerBitBudget≤B := by
      intro i
      have hi:=Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((branches j).integerBitBudget)) (Finset.mem_univ i)
      omega
    let stored:=List.Vector.ofFn (fun i => (scores i).wordRun)
    let selection:=wordMaximumProgram 3 (stored.map ScalarWordEvaluation.value)
    have hc:=wordMaximumProgram_four_height_actions (stored.map ScalarWordEvaluation.value) B (by
      intro i
      simpa only [stored,List.Vector.get_map,List.Vector.get_ofFn] using ScalarExpression.wordRun_height (scores i) B (hs i))
    have hp:=wordNodeBooleanBudget_square B 1300 (B+2) (by omega) (by omega)
    refine ⟨?_,ScalarExpression.wordRun_allLocalBound (scores 0) B (hs 0),
      ScalarExpression.wordRun_allLocalBound (scores 1) B (hs 1),
      ScalarExpression.wordRun_allLocalBound (scores 2) B (hs 2),
      ScalarExpression.wordRun_allLocalBound (scores 3) B (hs 3),
      PacketExpression.wordRun_allLocalBound (branches selection.index) B (hb _)⟩
    change selection.actions+16≤_
    change selection.actions≤_ at hc
    omega
end

theorem ScalarExpression.wordRun_booleanActions (e : ScalarExpression) (B : ℕ) (h : e.integerBitBudget≤B) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget B*e.operations :=
  (WordExpressionTrace.booleanActions_le _ _ (ScalarExpression.wordRun_allLocalBound e B h)).trans
    (Nat.mul_le_mul_left _ (ScalarExpression.wordRun_nodes e))

theorem PacketExpression.wordRun_booleanActions (e : PacketExpression) (B : ℕ) (h : e.integerBitBudget≤B) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget B*e.operations :=
  (WordExpressionTrace.booleanActions_le _ _ (PacketExpression.wordRun_allLocalBound e B h)).trans
    (Nat.mul_le_mul_left _ (PacketExpression.wordRun_nodes e))

theorem ScalarExpression.wordRun_booleanActions_internal (e : ScalarExpression) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget e.integerBitBudget*e.operations :=
  ScalarExpression.wordRun_booleanActions e _ (le_refl _)

theorem PacketExpression.wordRun_booleanActions_internal (e : PacketExpression) :
    e.wordRun.trace.booleanActions≤wordNodeBooleanBudget e.integerBitBudget*e.operations :=
  PacketExpression.wordRun_booleanActions e _ (le_refl _)

end CircuitRecursion
