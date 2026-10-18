import EffectiveEncoding.PureIntegerCompiler
import EffectiveEncoding.ProviderTrace

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem rawPacketCache_height (f : ℕ → IntegerPacket) (P B : ℕ)
    (hf : ∀ r,r≤P → IntegerPacketHeight (f r) B) (r : ℕ) :
    IntegerPacketHeight (readRawPacketCache (buildRawPacketCache f P) r) B := by
  by_cases h : r≤P
  · simpa only [readRawPacketCache,dite_eq_left h,buildRawPacketCache,List.Vector.get_ofFn] using hf r h
  · simp only [readRawPacketCache,dite_eq_right h]
    exact IntegerPacketHeight.mono _ 0 B IntegerPacket.one_height (Nat.zero_le B)

theorem rawCachedIntegerRun_integerBitBudget {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q B : ℕ)
    (hL : ∀ j,(table j).length≤L) (target : ℕ → IntegerPacket)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (q+1)) → IntegerPacketHeight (entry i r) B)
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (q+1)) → IntegerPacketHeight (target r) B) :
    (rawCachedIntegerRun entry inverseLabel table L q target).integerBitBudget≤
      1000000000002*(n+1)*(8*(B+1)+2)*(L+1)*traceRGrowth*(q+1)^128 := by
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  have hg i:=rawPacketExpressionOracle_bitEnvelope
    (readRawPacketCache (buildRawPacketCache (entry i) P)) B
    (rawPacketCache_height (entry i) P B (he i))
  have ht:=rawPacketExpressionOracle_bitEnvelope (readRawPacketCache (buildRawPacketCache target P)) B
    (rawPacketCache_height target P B hf)
  have hb:=tracedPairWord_flat_integerBitBudget _ (8*(B+1)) hg inverseLabel table L
    (Nat.clog 2 (q+1)) hL _ ht
  have hc : (rawCachedIntegerRun entry inverseLabel table L q target).integerBitBudget≤
      1000000000002*(n+1)*(8*(B+1)+2)*(L+1)*traceRGrowth^Nat.clog 2 (q+1) := by
    simpa only [rawCachedIntegerRun,integerTracedPairWord_eq,List.Vector.get_ofFn,P] using hb
  exact hc.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (1000000000002*(n+1)*(8*(B+1)+2)*(L+1)) (traceRGrowth_precision_bound q))

theorem rawBudget_double (C B L R Q : ℕ) :
    C*(8*(B+1)+2)*L*R*Q≤2*(C*(4*(B+1)+2)*L*R*Q) := by
  have h : 8*(B+1)+2≤2*(4*(B+1)+2) := by omega
  calc
    _≤C*(2*(4*(B+1)+2))*L*R*Q := by gcongr
    _=_ := by ring

theorem rawDescriptorRun_integerBitBudget {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (rawDescriptorRun entry inverseLabel table L q u).integerBitBudget≤2*actualDescriptorTraceBudget n L k q := by
  have hg j r (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) : IntegerPacketHeight (dyadicIntegerPacket (entry j) r) (actualTargetCacheHeight k L q) := by
    apply IntegerPacketHeight.mono _ _ _ (dyadicIntegerPacket_height (entry j) (G j) (he j) r)
    exact (Nat.add_le_add_right (hr.trans (numericalDemand_precision_bound L q)) 1).trans
      (actualTargetCacheHeight_ge k L q)
  have hf r (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) : IntegerPacketHeight (u.rawPacket r) (actualTargetCacheHeight k L q) := by
    rw [SingleCode.rawPacket_eq]
    exact extractionCode_targetCache_height hu L q r hr
  apply (rawCachedIntegerRun_integerBitBudget _ inverseLabel table L q _ hL _ hg hf).trans
  exact rawBudget_double (1000000000002*(n+1)) (actualTargetCacheHeight k L q)
    (L+1) traceRGrowth ((q+1)^128)

theorem rawDescriptorRun_polynomial {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (rawDescriptorRun entry inverseLabel table L q u).integerBitBudget≤
      2*(actualTraceConstant n L*(k+3)^7*(q+1)^137) :=
  (rawDescriptorRun_integerBitBudget entry G he inverseLabel table L q hL hu).trans
    (Nat.mul_le_mul_left 2 (actualDescriptorTraceBudget_polynomial n L k q))

theorem rawExtraction_expression_budget {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (e : ScalarExpression) (hmem : e∈(rawDescriptorRun entry inverseLabel table L
      (extractionPrecision k p) u).expressions) :
    e.integerBitBudget≤2*extractionOperandPolynomial n L k p := by
  have hb:=(List.le_sum_of_mem (List.mem_map.mpr ⟨e,hmem,rfl⟩)).trans
    (rawDescriptorRun_polynomial entry G he inverseLabel table L (extractionPrecision k p) hL hu)
  have hp : (extractionPrecision k p+1)^137≤(pipelinePrecisionPolynomial k p+1)^137 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (extractionPrecision_polynomial k p) 1) 137
  apply hb.trans
  apply Nat.mul_le_mul_left 2
  exact (Nat.mul_le_mul_left _ hp).trans (Nat.le_add_right _ _)

theorem rawExtraction_expression_subtreeBound {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (e : ScalarExpression) (hmem : e∈(rawDescriptorRun entry inverseLabel table L
      (extractionPrecision k p) u).expressions) :
    e.IntegerSubtreeBound (2*extractionOperandPolynomial n L k p) :=
  ScalarExpression.integerSubtreeBound e _
    (rawExtraction_expression_budget entry G he inverseLabel table L p hL hu e hmem)

/-- The actual integer evaluator's root payload is covered, not only the
semantic rational evaluation of the represented expression. -/
theorem rawExtraction_integerProgramRun_height {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (e : ScalarExpression) (hmem : e∈(rawDescriptorRun entry inverseLabel table L
      (extractionPrecision k p) u).expressions) :
    IntegerScalarHeight e.integerProgramRun (2*extractionOperandPolynomial n L k p) := by
  rw [ScalarExpression.integerProgramRun_eq]
  exact IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height e)
    (rawExtraction_expression_budget entry G he inverseLabel table L p hL hu e hmem)

end EffectiveEncoding
