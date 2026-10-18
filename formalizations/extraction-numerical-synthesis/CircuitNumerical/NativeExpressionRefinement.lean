import CircuitNumerical.NativeNumericalBudgets

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/-- A proof relation for two concrete expression representations. The
constant factor absorbs the native binary literals' denominator-one raw
macros; it does not describe execution of those macros by the native run. -/
structure NativeScalarRefines (e : NativeScalarExpression) (E : ScalarExpression) : Prop where
  eval_eq : e.interpret.eval=E.eval
  budget_le : e.interpret.integerBitBudget≤20*E.integerBitBudget
  operations_le : e.interpret.operations≤20*E.operations

structure NativePacketRefines (e : NativePacketExpression) (E : PacketExpression) : Prop where
  eval_eq : e.interpret.eval=E.eval
  budget_le : e.interpret.integerBitBudget≤20*E.integerBitBudget
  operations_le : e.interpret.operations≤20*E.operations

abbrev NativeScalarOracleRefines (f : NativeScalarExpressionOracle) (F : ScalarExpressionOracle) : Prop :=
  ∀ p,NativeScalarRefines (f p) (F p)
abbrev NativePacketOracleRefines (f : NativePacketExpressionOracle) (F : PacketExpressionOracle) : Prop :=
  ∀ p,NativePacketRefines (f p) (F p)

theorem NativeScalarRefines.raw (a : WordIntegerScalar) :
    NativeScalarRefines (.literal a) (rawScalarExpression a.decode) := by
  constructor
  · rfl
  · change (rawScalarExpression a.decode).integerBitBudget≤20*(rawScalarExpression a.decode).integerBitBudget
    omega
  · rw [show (NativeScalarExpression.literal a).interpret=rawScalarExpression a.decode from rfl]
    rw [rawScalarExpression_operations]
    decide

theorem NativePacketRefines.raw (a : WordIntegerPacket) :
    NativePacketRefines (.literal a) (rawPacketExpression a.decode) := by
  constructor
  · rfl
  · change (rawPacketExpression a.decode).integerBitBudget≤20*(rawPacketExpression a.decode).integerBitBudget
    omega
  · rw [show (NativePacketExpression.literal a).interpret=rawPacketExpression a.decode from rfl]
    rw [rawPacketExpression_operations]
    decide

theorem NativeScalarRefines.threshold (t : ℕ) : NativeScalarRefines (.stoppingThreshold t) (.stoppingThreshold t) := by
  constructor
  · rfl
  · change 2*t+1≤20*(2*t+1);omega
  · change (4:ℕ)≤20*4;decide

theorem NativeScalarRefines.add {a b : NativeScalarExpression} {A B : ScalarExpression}
    (ha : NativeScalarRefines a A) (hb : NativeScalarRefines b B) : NativeScalarRefines (.add a b) (.add A B) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq,hb.eval_eq]
  · change a.interpret.integerBitBudget+b.interpret.integerBitBudget+1≤20*(A.integerBitBudget+B.integerBitBudget+1)
    have := ha.budget_le;have := hb.budget_le;omega
  · change a.interpret.operations+b.interpret.operations+1≤20*(A.operations+B.operations+1)
    have := ha.operations_le;have := hb.operations_le;omega

theorem NativeScalarRefines.neg {a : NativeScalarExpression} {A : ScalarExpression}
    (ha : NativeScalarRefines a A) : NativeScalarRefines (.neg a) (.neg A) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq]
  · exact ha.budget_le
  · change a.interpret.operations+1≤20*(A.operations+1)
    have := ha.operations_le;omega

theorem NativeScalarRefines.mul {a b : NativeScalarExpression} {A B : ScalarExpression}
    (ha : NativeScalarRefines a A) (hb : NativeScalarRefines b B) : NativeScalarRefines (.mul a b) (.mul A B) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq,hb.eval_eq]
  · change a.interpret.integerBitBudget+b.interpret.integerBitBudget≤20*(A.integerBitBudget+B.integerBitBudget)
    have := ha.budget_le;have := hb.budget_le;omega
  · change a.interpret.operations+b.interpret.operations+1≤20*(A.operations+B.operations+1)
    have := ha.operations_le;have := hb.operations_le;omega

theorem NativeScalarRefines.inv {a : NativeScalarExpression} {A : ScalarExpression}
    (ha : NativeScalarRefines a A) : NativeScalarRefines (.inv a) (.inv A) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq]
  · exact ha.budget_le
  · change a.interpret.operations+1≤20*(A.operations+1)
    have := ha.operations_le;omega

theorem NativeScalarRefines.sqrt {a : NativeScalarExpression} {A : ScalarExpression}
    (ha : NativeScalarRefines a A) (p : ℕ) : NativeScalarRefines (.sqrt a p) (.sqrt A p) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq]
  · change a.interpret.integerBitBudget+2*p≤20*(A.integerBitBudget+2*p)
    have := ha.budget_le;omega
  · change a.interpret.operations+8≤20*(A.operations+8)
    have := ha.operations_le;omega

theorem NativeScalarRefines.meanMinus {a : NativeScalarExpression} {A : ScalarExpression}
    (ha : NativeScalarRefines a A) : NativeScalarRefines (.meanMinus a) (.meanMinus A) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq]
  · change a.interpret.integerBitBudget+2≤20*(A.integerBitBudget+2)
    have := ha.budget_le;omega
  · change a.interpret.operations+2≤20*(A.operations+2)
    have := ha.operations_le;omega

theorem NativeScalarRefines.coordinate {a : NativePacketExpression} {A : PacketExpression}
    (ha : NativePacketRefines a A) (i : Fin 4) : NativeScalarRefines (.coordinate a i) (.coordinate A i) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq]
  · exact ha.budget_le
  · change a.interpret.operations+1≤20*(A.operations+1)
    have := ha.operations_le;omega

theorem NativeScalarRefines.distance {a b : NativePacketExpression} {A B : PacketExpression}
    (ha : NativePacketRefines a A) (hb : NativePacketRefines b B) : NativeScalarRefines (.distance a b) (.distance A B) := by
  constructor
  · simp only [NativeScalarExpression.interpret,ScalarExpression.eval,ha.eval_eq,hb.eval_eq]
  · change 2*a.interpret.integerBitBudget+2*b.interpret.integerBitBudget+4≤20*(2*A.integerBitBudget+2*B.integerBitBudget+4)
    have := ha.budget_le;have := hb.budget_le;omega
  · change a.interpret.operations+b.interpret.operations+16≤20*(A.operations+B.operations+16)
    have := ha.operations_le;have := hb.operations_le;omega

theorem NativePacketRefines.tuple {a : Fin 4 → NativeScalarExpression} {A : Fin 4 → ScalarExpression}
    (ha : ∀ i,NativeScalarRefines (a i) (A i)) : NativePacketRefines (.tuple a) (.tuple A) := by
  constructor
  · simp only [NativePacketExpression.interpret,PacketExpression.eval]
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    exact (ha i).eval_eq
  · have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (ha i).budget_le)
    simpa only [NativePacketExpression.interpret,PacketExpression.integerBitBudget,Finset.mul_sum] using hs
  · have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (ha i).operations_le)
    rw [←Finset.mul_sum] at hs
    change (∑ i : Fin 4,(a i).interpret.operations)+4≤20*((∑ i : Fin 4,(A i).operations)+4)
    omega

theorem NativePacketRefines.mul {a b : NativePacketExpression} {A B : PacketExpression}
    (ha : NativePacketRefines a A) (hb : NativePacketRefines b B) : NativePacketRefines (.mul a b) (.mul A B) := by
  constructor
  · simp only [NativePacketExpression.interpret,PacketExpression.eval,ha.eval_eq,hb.eval_eq]
  · change a.interpret.integerBitBudget+b.interpret.integerBitBudget+2≤20*(A.integerBitBudget+B.integerBitBudget+2)
    have := ha.budget_le;have := hb.budget_le;omega
  · change a.interpret.operations+b.interpret.operations+48≤20*(A.operations+B.operations+48)
    have := ha.operations_le;have := hb.operations_le;omega

theorem NativePacketRefines.inverse {a : NativePacketExpression} {A : PacketExpression}
    (ha : NativePacketRefines a A) : NativePacketRefines (.inverse a) (.inverse A) := by
  constructor
  · simp only [NativePacketExpression.interpret,PacketExpression.eval,ha.eval_eq]
  · exact ha.budget_le
  · change a.interpret.operations+4≤20*(A.operations+4)
    have := ha.operations_le;omega

theorem NativePacketRefines.selectMax {scores : Fin 4 → NativeScalarExpression}
    {branches : Fin 4 → NativePacketExpression} {S : Fin 4 → ScalarExpression} {B : Fin 4 → PacketExpression}
    (hs : ∀ i,NativeScalarRefines (scores i) (S i)) (hb : ∀ i,NativePacketRefines (branches i) (B i)) :
    NativePacketRefines (.selectMax scores branches) (.selectMax S B) := by
  constructor
  · simp only [NativePacketExpression.interpret,PacketExpression.eval]
    have hval : List.Vector.ofFn (fun i => (scores i).interpret.eval)=List.Vector.ofFn (fun i => (S i).eval) := by
      apply List.Vector.ext
      intro i
      simpa only [List.Vector.get_ofFn] using (hs i).eval_eq
    rw [hval]
    exact (hb _).eval_eq
  · have hS:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (hs i).budget_le)
    have hB:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (hb i).budget_le)
    rw [←Finset.mul_sum] at hS hB
    change (∑ i : Fin 4,(scores i).interpret.integerBitBudget)+(∑ i : Fin 4,(branches i).interpret.integerBitBudget)≤_
    change _≤20*((∑ i : Fin 4,(S i).integerBitBudget)+(∑ i : Fin 4,(B i).integerBitBudget))
    omega
  · have hS:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (hs i).operations_le)
    have hB:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => (hb i).operations_le)
    rw [←Finset.mul_sum] at hS hB
    change (∑ i : Fin 4,(scores i).interpret.operations)+(∑ i : Fin 4,(branches i).interpret.operations)+3≤_
    change _≤20*((∑ i : Fin 4,(S i).operations)+(∑ i : Fin 4,(B i).operations)+3)
    omega

theorem nativeScalarOne_refines : NativeScalarRefines (.literal wordScalarOne) (.literal 1) := by
  constructor
  · exact nativeScalarOne_eval
  · change (rawScalarExpression wordScalarOne.decode).integerBitBudget≤20*rationalBinaryExponent 1
    have hh : IntegerScalarHeight wordScalarOne.decode 0 := by constructor <;> decide
    have h:=rawScalarExpression_integerBitBudget wordScalarOne.decode 0 hh
    have he : rationalBinaryExponent 1=1 := by decide
    rw [he];omega
  · rw [show (NativeScalarExpression.literal wordScalarOne).interpret=rawScalarExpression wordScalarOne.decode from rfl]
    rw [rawScalarExpression_operations]
    change (4:ℕ)≤20*1;decide

theorem nativeScalarZero_refines : NativeScalarRefines (.literal wordScalarZero) (.literal 0) := by
  constructor
  · exact nativeScalarZero_eval
  · change (rawScalarExpression wordScalarZero.decode).integerBitBudget≤20*rationalBinaryExponent 0
    have hh : IntegerScalarHeight wordScalarZero.decode 0 := by constructor <;> decide
    have h:=rawScalarExpression_integerBitBudget wordScalarZero.decode 0 hh
    have he : rationalBinaryExponent 0=1 := by decide
    rw [he];omega
  · rw [show (NativeScalarExpression.literal wordScalarZero).interpret=rawScalarExpression wordScalarZero.decode from rfl]
    rw [rawScalarExpression_operations]
    change (4:ℕ)≤20*1;decide

theorem nativePacketOne_refines (p : ℕ) : NativePacketRefines (nativeExpressionPacketOne p) (expressionPacketOne p) := by
  constructor
  · exact congrFun nativeExpressionPacketOne_eval p
  · have hh : IntegerPacketHeight wordPacketOne.decode 0 := by rw [wordPacketOne_decode];exact IntegerPacket.one_height
    have h:=rawPacketExpression_integerBitBudget wordPacketOne.decode 0 hh
    have he : (expressionPacketOne p).integerBitBudget=4 := by
      change (expressionPacketOne 0).integerBitBudget=4
      decide
    change (rawPacketExpression wordPacketOne.decode).integerBitBudget≤20*(expressionPacketOne p).integerBitBudget
    rw [he];omega
  · change (rawPacketExpression wordPacketOne.decode).operations≤20*1
    rw [rawPacketExpression_operations]

theorem nativeFrame_refines (j : Fin 4) (p : ℕ) : NativePacketRefines (nativeExpressionFrame j p) (expressionFrame j p) := by
  constructor
  · exact congrFun (nativeExpressionFrame_eval j) p
  · have hh : IntegerPacketHeight (wordPacketFrame j).decode 0 := by
      constructor
      · change (1:ℕ)≤1;decide
      · intro i
        fin_cases j <;> fin_cases i <;>
          norm_num [wordPacketFrame,WordIntegerPacket.decode,SignedBinaryWord.value,binaryWordValue,binaryBitValue]
    have h:=rawPacketExpression_integerBitBudget (wordPacketFrame j).decode 0 hh
    have he : (expressionFrame j p).integerBitBudget=4 := by
      change (expressionFrame j 0).integerBitBudget=4
      fin_cases j <;> decide
    change (rawPacketExpression (wordPacketFrame j).decode).integerBitBudget≤20*(expressionFrame j p).integerBitBudget
    rw [he];omega
  · change (rawPacketExpression (wordPacketFrame j).decode).operations≤20*1
    rw [rawPacketExpression_operations]

end CircuitRecursion
