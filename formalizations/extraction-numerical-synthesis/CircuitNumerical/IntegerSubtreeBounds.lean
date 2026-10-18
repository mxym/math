import CircuitNumerical.CachedIntegerBudgets

namespace CircuitRecursion

/- These predicates include every represented scalar/packet result, including
all alternatives of a selection. They do not assert a machine implementation
cost for the integer primitives inside one AST node. -/
mutual
def ScalarExpression.IntegerSubtreeBound (e : ScalarExpression) (B : ℕ) : Prop :=
  IntegerScalarHeight e.integerRun B ∧ match e with
  | .literal _ | .stoppingThreshold _ => True
  | .add a b | .mul a b => a.IntegerSubtreeBound B ∧ b.IntegerSubtreeBound B
  | .neg a | .inv a | .sqrt a _ | .meanMinus a => a.IntegerSubtreeBound B
  | .coordinate a _ => a.IntegerSubtreeBound B
  | .distance a b => a.IntegerSubtreeBound B ∧ b.IntegerSubtreeBound B
def PacketExpression.IntegerSubtreeBound (e : PacketExpression) (B : ℕ) : Prop :=
  IntegerPacketHeight e.integerRun B ∧ match e with
  | .literal _ => True
  | .tuple a => ∀ i,(a i).IntegerSubtreeBound B
  | .mul a b => a.IntegerSubtreeBound B ∧ b.IntegerSubtreeBound B
  | .inverse a => a.IntegerSubtreeBound B
  | .selectMax scores branches =>
    (∀ i,(scores i).IntegerSubtreeBound B) ∧ (∀ i,(branches i).IntegerSubtreeBound B)
end

mutual
theorem ScalarExpression.integerSubtreeBound (e : ScalarExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.IntegerSubtreeBound B := by
  have hroot:=IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height e) h
  cases e with
  | literal q => exact ⟨hroot,True.intro⟩
  | stoppingThreshold t => exact ⟨hroot,True.intro⟩
  | add a b =>
    change a.integerBitBudget+b.integerBitBudget+1≤B at h
    exact ⟨hroot,ScalarExpression.integerSubtreeBound a B (by omega),
      ScalarExpression.integerSubtreeBound b B (by omega)⟩
  | neg a => exact ⟨hroot,ScalarExpression.integerSubtreeBound a B h⟩
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget≤B at h
    exact ⟨hroot,ScalarExpression.integerSubtreeBound a B (by omega),
      ScalarExpression.integerSubtreeBound b B (by omega)⟩
  | inv a => exact ⟨hroot,ScalarExpression.integerSubtreeBound a B h⟩
  | sqrt a p =>
    change a.integerBitBudget+2*p≤B at h
    exact ⟨hroot,ScalarExpression.integerSubtreeBound a B (by omega)⟩
  | meanMinus a =>
    change a.integerBitBudget+2≤B at h
    exact ⟨hroot,ScalarExpression.integerSubtreeBound a B (by omega)⟩
  | coordinate a i => exact ⟨hroot,PacketExpression.integerSubtreeBound a B h⟩
  | distance a b =>
    change 2*a.integerBitBudget+2*b.integerBitBudget+4≤B at h
    exact ⟨hroot,PacketExpression.integerSubtreeBound a B (by omega),
      PacketExpression.integerSubtreeBound b B (by omega)⟩
theorem PacketExpression.integerSubtreeBound (e : PacketExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : e.IntegerSubtreeBound B := by
  have hroot:=IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height e) h
  cases e with
  | literal q => exact ⟨hroot,True.intro⟩
  | tuple a =>
    refine ⟨hroot,fun i => ScalarExpression.integerSubtreeBound (a i) B ?_⟩
    exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((a j).integerBitBudget))
      (Finset.mem_univ i)).trans h
  | mul a b =>
    change a.integerBitBudget+b.integerBitBudget+2≤B at h
    exact ⟨hroot,PacketExpression.integerSubtreeBound a B (by omega),
      PacketExpression.integerSubtreeBound b B (by omega)⟩
  | inverse a => exact ⟨hroot,PacketExpression.integerSubtreeBound a B h⟩
  | selectMax scores branches =>
    change (∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)≤B at h
    refine ⟨hroot,?_,?_⟩
    · intro i
      apply ScalarExpression.integerSubtreeBound (scores i) B
      have hs:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores j).integerBitBudget)) (Finset.mem_univ i)
      omega
    · intro i
      apply PacketExpression.integerSubtreeBound (branches i) B
      have hs:=Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => Nat.zero_le ((branches j).integerBitBudget)) (Finset.mem_univ i)
      omega
end

theorem ArithmeticWordResult.expression_integerSubtreeBound {m : ℕ}
    (r : ArithmeticWordResult m) (e : ScalarExpression) (he : e∈r.expressions) :
    e.IntegerSubtreeBound r.integerBitBudget := by
  apply ScalarExpression.integerSubtreeBound
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem cachedArithmeticRun_expression_integerSubtreeBound {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U)
    (e : ScalarExpression) (hmem : e∈(cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i))
      inverseLabel table L p (dyadicQuaternionOracle f)).expressions) :
    e.IntegerSubtreeBound (cachedIntegerBudgetConstant n L*(p+1)^137) := by
  apply ScalarExpression.integerSubtreeBound
  exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,hmem,rfl⟩)).trans
    (cachedArithmeticRun_integerBitBudget entry G he inverseLabel table L p hL f U hf)

end CircuitRecursion
