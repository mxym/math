import EffectiveEncoding.ProviderPrecision

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/- Heights of all scalar/packet results at every expression-tree node.
This is a statement about the represented integer execution, not heap size. -/
mutual
def scalarIntermediateHeights (e : ScalarExpression) (B : ℕ) : Prop :=
  IntegerScalarHeight e.integerRun B ∧ match e with
    | .literal _ | .stoppingThreshold _ => True
    | .add a b | .mul a b => scalarIntermediateHeights a B ∧ scalarIntermediateHeights b B
    | .neg a | .inv a | .sqrt a _ | .meanMinus a => scalarIntermediateHeights a B
    | .coordinate a _ => packetIntermediateHeights a B
    | .distance a b => packetIntermediateHeights a B ∧ packetIntermediateHeights b B
def packetIntermediateHeights (e : PacketExpression) (B : ℕ) : Prop :=
  IntegerPacketHeight e.integerRun B ∧ match e with
    | .literal _ => True
    | .tuple a => ∀ i,scalarIntermediateHeights (a i) B
    | .mul a b => packetIntermediateHeights a B ∧ packetIntermediateHeights b B
    | .inverse a => packetIntermediateHeights a B
    | .selectMax scores branches =>
        (∀ i,scalarIntermediateHeights (scores i) B) ∧
          ∀ i,packetIntermediateHeights (branches i) B
end

mutual
theorem scalarIntermediateHeights_of_budget (e : ScalarExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : scalarIntermediateHeights e B := by
  have hh := IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height e) h
  cases e <;> refine ⟨hh,?_⟩
  case literal q => trivial
  case stoppingThreshold t => trivial
  case add a b =>
    exact ⟨scalarIntermediateHeights_of_budget a B (by change _+_+1≤B at h;omega),
      scalarIntermediateHeights_of_budget b B (by change _+_+1≤B at h;omega)⟩
  case neg a => exact scalarIntermediateHeights_of_budget a B h
  case mul a b =>
    exact ⟨scalarIntermediateHeights_of_budget a B (by change _+_≤B at h;omega),
      scalarIntermediateHeights_of_budget b B (by change _+_≤B at h;omega)⟩
  case inv a => exact scalarIntermediateHeights_of_budget a B h
  case sqrt a p => exact scalarIntermediateHeights_of_budget a B (by change _+2*p≤B at h;omega)
  case meanMinus a => exact scalarIntermediateHeights_of_budget a B (by change _+2≤B at h;omega)
  case coordinate a i => exact packetIntermediateHeights_of_budget a B h
  case distance a b =>
    exact ⟨packetIntermediateHeights_of_budget a B (by change 2*_+2*_+4≤B at h;omega),
      packetIntermediateHeights_of_budget b B (by change 2*_+2*_+4≤B at h;omega)⟩
theorem packetIntermediateHeights_of_budget (e : PacketExpression) (B : ℕ)
    (h : e.integerBitBudget≤B) : packetIntermediateHeights e B := by
  have hh := IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height e) h
  cases e <;> refine ⟨hh,?_⟩
  case literal q => trivial
  case tuple a =>
    intro i
    apply scalarIntermediateHeights_of_budget
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((a j).integerBitBudget))
      (Finset.mem_univ i)).trans h
  case mul a b =>
    exact ⟨packetIntermediateHeights_of_budget a B (by change _+_+2≤B at h;omega),
      packetIntermediateHeights_of_budget b B (by change _+_+2≤B at h;omega)⟩
  case inverse a => exact packetIntermediateHeights_of_budget a B h
  case selectMax scores branches =>
    constructor
    · intro i
      apply scalarIntermediateHeights_of_budget
      have hi := Finset.single_le_sum (fun j _ => Nat.zero_le ((scores j).integerBitBudget))
        (Finset.mem_univ i)
      change (∑ j : Fin 4,(scores j).integerBitBudget)+(∑ j : Fin 4,(branches j).integerBitBudget)≤B at h
      omega
    · intro i
      apply packetIntermediateHeights_of_budget
      have hi := Finset.single_le_sum (fun j _ => Nat.zero_le ((branches j).integerBitBudget))
        (Finset.mem_univ i)
      change (∑ j : Fin 4,(scores j).integerBitBudget)+(∑ j : Fin 4,(branches j).integerBitBudget)≤B at h
      omega
end

theorem SingleCode.packetExpression_intermediateHeights {M H : ℕ} (u : SingleCode)
    (h : u.Fits M H) (p : ℕ) :
    packetIntermediateHeights (u.packetExpression p) (providerHeightBudget M H p) :=
  packetIntermediateHeights_of_budget _ _ (u.packetExpression_budget h p)

/-- The bound includes every scalar and packet subtree, so it is stronger
than an output-numerator bound alone. -/
theorem extractionCode_provider_intermediateHeights {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    packetIntermediateHeights (u.packetExpression p) (1000000*(k+3)^7*(p+5)) :=
  packetIntermediateHeights_of_budget _ _
    ((u.packetExpression_budget (extractionCode_fits k (.single i u) hu).1 p).trans
      (providerHeightBudget_polynomial k p))

theorem extractionCode_targetCache_intermediateHeights {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q r : ℕ)
    (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) :
    packetIntermediateHeights (u.packetExpression r)
      (1000000*(k+3)^7*(cachePrecisionBudget L q+5)) :=
  packetIntermediateHeights_of_budget _ _
    (((u.packetExpression_budget (extractionCode_fits k (.single i u) hu).1 r).trans
      (providerHeightBudget_polynomial k r)).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hr.trans (numericalDemand_precision_bound L q)) 5)))

/-- The shifted numerator supplied to integer division and integer sqrt is
also bounded; no hidden real square-root input is used. -/
theorem integerRoot_work_operand_bound (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) :
    (a.numerator.toNat <<< (2*p))≤2^(A+2*p) ∧
      ((a.numerator.toNat <<< (2*p))/a.denominator)≤2^(A+2*p) := by
  have hnat : a.numerator.toNat≤a.numerator.natAbs := by cases a.numerator <;> simp
  have h := Nat.mul_le_mul_right (2^(2*p)) (hnat.trans ha.2)
  rw [← pow_add] at h
  rw [Nat.shiftLeft_eq]
  exact ⟨h,(Nat.div_le_self _ _).trans h⟩

end EffectiveEncoding
