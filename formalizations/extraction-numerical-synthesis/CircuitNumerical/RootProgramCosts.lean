import CircuitNumerical.BinaryRootResources

namespace CircuitRecursion

/- Only the explicit root subprograms are charged here; other AST nodes
contribute their recursively evaluated children. Selection charges every
alternative, giving an upper bound for either chosen branch. -/
mutual
def ScalarExpression.binaryRootPrimitiveOperations : ScalarExpression → ℕ
  | .literal _ | .stoppingThreshold _ => 0
  | .add a b | .mul a b => a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations
  | .neg a | .inv a | .meanMinus a => a.binaryRootPrimitiveOperations
  | .sqrt a p => a.binaryRootPrimitiveOperations+a.integerRun.binaryRootPrimitiveOperations p
  | .coordinate a _ => a.binaryRootPrimitiveOperations
  | .distance a b => a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations
def PacketExpression.binaryRootPrimitiveOperations : PacketExpression → ℕ
  | .literal _ => 0
  | .tuple a => ∑ i : Fin 4,(a i).binaryRootPrimitiveOperations
  | .mul a b => a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations
  | .inverse a => a.binaryRootPrimitiveOperations
  | .selectMax scores branches =>
    (∑ i : Fin 4,(scores i).binaryRootPrimitiveOperations)+
    (∑ i : Fin 4,(branches i).binaryRootPrimitiveOperations)
end

mutual
theorem ScalarExpression.binaryRootPrimitiveOperations_bound (e : ScalarExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.binaryRootPrimitiveOperations≤(16*(B+2)+5)*e.operations := by
  cases e with
  | literal q => exact Nat.zero_le _
  | stoppingThreshold t => exact Nat.zero_le _
  | add a b =>
    change a.integerBitBudget+b.integerBitBudget+1≤B at h
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    have hb:=ScalarExpression.binaryRootPrimitiveOperations_bound b B (by omega)
    change a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations≤
      (16*(B+2)+5)*(a.operations+b.operations+1)
    nlinarith
  | neg a =>
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B h
    change a.binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a.operations+1)
    nlinarith
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget≤B at h
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    have hb:=ScalarExpression.binaryRootPrimitiveOperations_bound b B (by omega)
    change a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations≤
      (16*(B+2)+5)*(a.operations+b.operations+1)
    nlinarith
  | inv a =>
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B h
    change a.binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a.operations+1)
    nlinarith
  | sqrt a p =>
    change a.integerBitBudget+2*p≤B at h
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    have hr:=IntegerScalar.binaryRootPrimitiveOperations_bound a.integerRun a.integerBitBudget p
      (ScalarExpression.integerRun_height a)
    have hr' : a.integerRun.binaryRootPrimitiveOperations p≤16*(B+2)+5 :=
      hr.trans (by omega)
    change a.binaryRootPrimitiveOperations+a.integerRun.binaryRootPrimitiveOperations p≤
      (16*(B+2)+5)*(a.operations+8)
    nlinarith
  | meanMinus a =>
    change a.integerBitBudget+2≤B at h
    have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    change a.binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a.operations+2)
    nlinarith
  | coordinate a i =>
    have ha:=PacketExpression.binaryRootPrimitiveOperations_bound a B h
    change a.binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a.operations+1)
    nlinarith
  | distance a b =>
    change 2*a.integerBitBudget+2*b.integerBitBudget+4≤B at h
    have ha:=PacketExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    have hb:=PacketExpression.binaryRootPrimitiveOperations_bound b B (by omega)
    change a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations≤
      (16*(B+2)+5)*(a.operations+b.operations+16)
    nlinarith
theorem PacketExpression.binaryRootPrimitiveOperations_bound (e : PacketExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.binaryRootPrimitiveOperations≤(16*(B+2)+5)*e.operations := by
  cases e with
  | literal q => exact Nat.zero_le _
  | tuple a =>
    have hs : ∀ i,(a i).binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a i).operations := by
      intro i
      apply ScalarExpression.binaryRootPrimitiveOperations_bound (a i) B
      exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((a j).integerBitBudget))
        (Finset.mem_univ i)).trans h
    have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hs i)
    rw [← Finset.mul_sum] at hsum
    change (∑ i : Fin 4,(a i).binaryRootPrimitiveOperations)≤
      (16*(B+2)+5)*((∑ i : Fin 4,(a i).operations)+4)
    nlinarith
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget+2≤B at h
    have ha:=PacketExpression.binaryRootPrimitiveOperations_bound a B (by omega)
    have hb:=PacketExpression.binaryRootPrimitiveOperations_bound b B (by omega)
    change a.binaryRootPrimitiveOperations+b.binaryRootPrimitiveOperations≤
      (16*(B+2)+5)*(a.operations+b.operations+48)
    nlinarith
  | inverse a =>
    have ha:=PacketExpression.binaryRootPrimitiveOperations_bound a B h
    change a.binaryRootPrimitiveOperations≤(16*(B+2)+5)*(a.operations+4)
    nlinarith
  | selectMax scores branches =>
    change (∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)≤B at h
    have hs : ∀ i,(scores i).binaryRootPrimitiveOperations≤(16*(B+2)+5)*(scores i).operations := by
      intro i
      apply ScalarExpression.binaryRootPrimitiveOperations_bound (scores i) B
      have hc:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores j).integerBitBudget)) (Finset.mem_univ i)
      omega
    have hb : ∀ i,(branches i).binaryRootPrimitiveOperations≤(16*(B+2)+5)*(branches i).operations := by
      intro i
      apply PacketExpression.binaryRootPrimitiveOperations_bound (branches i) B
      have hc:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((branches j).integerBitBudget)) (Finset.mem_univ i)
      omega
    have hss:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hs i)
    have hbs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hb i)
    rw [← Finset.mul_sum] at hss hbs
    change (∑ i : Fin 4,(scores i).binaryRootPrimitiveOperations)+
      (∑ i : Fin 4,(branches i).binaryRootPrimitiveOperations)≤
      (16*(B+2)+5)*((∑ i : Fin 4,(scores i).operations)+(∑ i : Fin 4,(branches i).operations)+3)
    nlinarith
end

def ArithmeticWordResult.binaryRootPrimitiveOperations {m : ℕ} (r : ArithmeticWordResult m) : ℕ :=
  (r.expressions.map ScalarExpression.binaryRootPrimitiveOperations).sum

theorem ArithmeticWordResult.binaryRootPrimitiveOperations_bound {m : ℕ}
    (r : ArithmeticWordResult m) (B : ℕ) (h : r.integerBitBudget≤B) :
    r.binaryRootPrimitiveOperations≤(16*(B+2)+5)*r.operations := by
  have hmem : ∀ e∈r.expressions,e.integerBitBudget≤B := by
    intro e he
    exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)).trans h
  have hs : ∀ es : List ScalarExpression,(∀ e∈es,e.integerBitBudget≤B) →
      (es.map ScalarExpression.binaryRootPrimitiveOperations).sum≤
      (16*(B+2)+5)*(es.map ScalarExpression.operations).sum := by
    intro es
    induction es with
    | nil => intro hnil;rfl
    | cons a es ih =>
      intro hall
      have ha:=ScalarExpression.binaryRootPrimitiveOperations_bound a B (hall a (by simp))
      have ht:=ih (fun e he => hall e (by simp only [List.mem_cons];exact Or.inr he))
      simp only [List.map_cons,List.sum_cons]
      nlinarith
  exact (hs r.expressions hmem).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

theorem cachedArithmeticRun_binaryRootPrimitiveOperations {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) :
    (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).binaryRootPrimitiveOperations≤
    (16*(cachedIntegerBudgetConstant n L*(p+1)^137+2)+5)*
      ((1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64) := by
  exact (ArithmeticWordResult.binaryRootPrimitiveOperations_bound _ _
    (cachedArithmeticRun_integerBitBudget entry G he inverseLabel table L p hL f U hf)).trans
    (Nat.mul_le_mul_left _ (cachedArithmeticRun_operations _ inverseLabel table L p hL _))

theorem cachedArithmeticRun_envelope_binaryRootPrimitiveOperations {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketBitEnvelope
      (cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1)))) (0,B))
    (hf : PacketBitEnvelope
      (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) (0,B)) :
    let C:=1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128
    (cachedArithmeticRun entry inverseLabel table L p f).binaryRootPrimitiveOperations≤
      (16*(C+2)+5)*((1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64) := by
  dsimp only
  exact (ArithmeticWordResult.binaryRootPrimitiveOperations_bound _ _
    (cachedArithmeticRun_envelope_integerBitBudget entry inverseLabel table L p B hL f he hf)).trans
    (Nat.mul_le_mul_left _ (cachedArithmeticRun_operations entry inverseLabel table L p hL f))

theorem cachedRootCost_algebra (C D x : ℕ) (hx : 1≤x) :
    (16*(C*x^137+2)+5)*(D*x^64)≤(16*C+37)*D*x^201 := by
  have hp : 1≤x^137 := Nat.one_le_pow _ _ (by omega)
  have hbase : 16*(C*x^137+2)+5≤(16*C+37)*x^137 := by nlinarith
  have h:=Nat.mul_le_mul_right (D*x^64) hbase
  apply h.trans_eq
  rw [show 201=137+64 by decide,pow_add]
  ring

theorem cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) :
    (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).binaryRootPrimitiveOperations≤
      (16*cachedIntegerBudgetConstant n L+37)*(1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^201 :=
  (cachedArithmeticRun_binaryRootPrimitiveOperations entry G he inverseLabel table L p hL f U hf).trans
    (cachedRootCost_algebra _ _ _ (by omega))

end CircuitRecursion
