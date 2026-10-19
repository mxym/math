import CircuitNumerical.RootOperandTrace

namespace CircuitRecursion

mutual
def ScalarExpression.rootOperandTrace : ScalarExpression → List ℕ
  | .literal _ => []
  | .stoppingThreshold t => integerStoppingThresholdOperandTrace t
  | .add a b | .mul a b => a.rootOperandTrace++b.rootOperandTrace
  | .neg a | .inv a | .meanMinus a => a.rootOperandTrace
  | .sqrt a p => a.rootOperandTrace++a.integerRun.rootOperandTrace p
  | .coordinate a _ => a.rootOperandTrace
  | .distance a b => a.rootOperandTrace++b.rootOperandTrace
def PacketExpression.rootOperandTrace : PacketExpression → List ℕ
  | .literal _ => []
  | .tuple a => (List.finRange 4).flatMap (fun i => (a i).rootOperandTrace)
  | .mul a b => a.rootOperandTrace++b.rootOperandTrace
  | .inverse a => a.rootOperandTrace
  | .selectMax scores branches =>
    (List.finRange 4).flatMap (fun i => (scores i).rootOperandTrace)++
    (List.finRange 4).flatMap (fun i => (branches i).rootOperandTrace)
end

mutual
theorem ScalarExpression.rootOperandTrace_height (e : ScalarExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) (x : ℕ) (hx : x∈e.rootOperandTrace) : x≤2^B := by
  cases e with
  | literal q => simp only [ScalarExpression.rootOperandTrace,List.not_mem_nil] at hx
  | stoppingThreshold t =>
    have ht:=integerStoppingThresholdOperandTrace_height t x hx
    exact ht.trans (Nat.pow_le_pow_right (by decide) h)
  | add a b =>
    change a.integerBitBudget+b.integerBitBudget+1≤B at h
    rcases List.mem_append.mp hx with ha|hb
    · exact ScalarExpression.rootOperandTrace_height a B (by omega) x ha
    · exact ScalarExpression.rootOperandTrace_height b B (by omega) x hb
  | neg a => exact ScalarExpression.rootOperandTrace_height a B h x hx
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget≤B at h
    rcases List.mem_append.mp hx with ha|hb
    · exact ScalarExpression.rootOperandTrace_height a B (by omega) x ha
    · exact ScalarExpression.rootOperandTrace_height b B (by omega) x hb
  | inv a => exact ScalarExpression.rootOperandTrace_height a B h x hx
  | sqrt a p =>
    change a.integerBitBudget+2*p≤B at h
    rcases List.mem_append.mp hx with ha|hr
    · exact ScalarExpression.rootOperandTrace_height a B (by omega) x ha
    · exact (IntegerScalar.rootOperandTrace_height a.integerRun a.integerBitBudget p
        (ScalarExpression.integerRun_height a) x hr).trans (Nat.pow_le_pow_right (by decide) h)
  | meanMinus a =>
    change a.integerBitBudget+2≤B at h
    exact ScalarExpression.rootOperandTrace_height a B (by omega) x hx
  | coordinate a i => exact PacketExpression.rootOperandTrace_height a B h x hx
  | distance a b =>
    change 2*a.integerBitBudget+2*b.integerBitBudget+4≤B at h
    rcases List.mem_append.mp hx with ha|hb
    · exact PacketExpression.rootOperandTrace_height a B (by omega) x ha
    · exact PacketExpression.rootOperandTrace_height b B (by omega) x hb
theorem PacketExpression.rootOperandTrace_height (e : PacketExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) (x : ℕ) (hx : x∈e.rootOperandTrace) : x≤2^B := by
  cases e with
  | literal q => simp only [PacketExpression.rootOperandTrace,List.not_mem_nil] at hx
  | tuple a =>
    obtain ⟨i,hi,hmem⟩:=List.mem_flatMap.mp hx
    apply ScalarExpression.rootOperandTrace_height (a i) B _ x hmem
    exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((a j).integerBitBudget))
      (Finset.mem_univ i)).trans h
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget+2≤B at h
    rcases List.mem_append.mp hx with ha|hb
    · exact PacketExpression.rootOperandTrace_height a B (by omega) x ha
    · exact PacketExpression.rootOperandTrace_height b B (by omega) x hb
  | inverse a => exact PacketExpression.rootOperandTrace_height a B h x hx
  | selectMax scores branches =>
    change (∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)≤B at h
    rcases List.mem_append.mp hx with hs|hb
    · obtain ⟨i,hi,hmem⟩:=List.mem_flatMap.mp hs
      apply ScalarExpression.rootOperandTrace_height (scores i) B _ x hmem
      have hs:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores j).integerBitBudget)) (Finset.mem_univ i)
      omega
    · obtain ⟨i,hi,hmem⟩:=List.mem_flatMap.mp hb
      apply PacketExpression.rootOperandTrace_height (branches i) B _ x hmem
      have hb:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((branches j).integerBitBudget)) (Finset.mem_univ i)
      omega
end

def ArithmeticWordResult.rootOperandTrace {m : ℕ} (r : ArithmeticWordResult m) : List ℕ :=
  r.expressions.flatMap ScalarExpression.rootOperandTrace

theorem ArithmeticWordResult.rootOperandTrace_height {m : ℕ} (r : ArithmeticWordResult m)
    (B : ℕ) (h : r.integerBitBudget≤B) (x : ℕ) (hx : x∈r.rootOperandTrace) : x≤2^B := by
  obtain ⟨e,he,hmem⟩:=List.mem_flatMap.mp hx
  apply ScalarExpression.rootOperandTrace_height e B _ x hmem
  exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)).trans h

theorem cachedArithmeticRun_rootOperandTrace_height {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U)
    (x : ℕ) (hx : x∈(cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i))
      inverseLabel table L p (dyadicQuaternionOracle f)).rootOperandTrace) :
    x≤2^(cachedIntegerBudgetConstant n L*(p+1)^137) := by
  exact ArithmeticWordResult.rootOperandTrace_height _ _
    (cachedArithmeticRun_integerBitBudget entry G he inverseLabel table L p hL f U hf) x hx

theorem cachedArithmeticRun_rational_rootOperandTrace_height {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketBitEnvelope
      (cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1)))) (0,B))
    (hf : PacketBitEnvelope
      (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) (0,B))
    (x : ℕ) (hx : x∈(cachedArithmeticRun entry inverseLabel table L p f).rootOperandTrace) :
    x≤2^(1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128) := by
  exact ArithmeticWordResult.rootOperandTrace_height _ _
    (cachedArithmeticRun_envelope_integerBitBudget entry inverseLabel table L p B hL f he hf) x hx

end CircuitRecursion
