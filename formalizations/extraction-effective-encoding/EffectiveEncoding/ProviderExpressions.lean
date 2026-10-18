import EffectiveEncoding.DescriptorBounds
import CircuitNumerical.IntegerExpressionBudgets

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Closed expressions for the literal gate packets. All leaves are rational
constants computed from the finite descriptor, so there is no target oracle. -/
def constantExpression (q : ℚ) : ScalarExpressionOracle := fun _ => .literal q

def meanPlusExpression (f : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .mul (.literal (1/2)) (.add (.literal 1) (f p))

def halfCosExpression : ℕ → ScalarExpressionOracle → ScalarExpressionOracle
  | 0,f => f
  | n+1,f => expressionSqrt (meanPlusExpression (halfCosExpression n f))

def halfSinExpression : ℕ → ScalarExpressionOracle → ScalarExpressionOracle → ScalarExpressionOracle
  | 0,_,g => g
  | n+1,f,_ => expressionSqrt (expressionMeanMinus (halfCosExpression n f))

theorem meanPlusExpression_eval (f : ScalarExpressionOracle) :
    evaluateScalarOracle (meanPlusExpression f)=oracleMeanPlus (evaluateScalarOracle f) := by
  funext p
  simp [evaluateScalarOracle,meanPlusExpression,ScalarExpression.eval,oracleMeanPlus]
  ring

theorem halfCosExpression_eval (n : ℕ) (f : ScalarExpressionOracle) :
    evaluateScalarOracle (halfCosExpression n f)=halfCosOracle n (evaluateScalarOracle f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [halfCosExpression,expressionSqrt_eval,meanPlusExpression_eval,ih,halfCosOracle]

theorem halfSinExpression_eval (n : ℕ) (f g : ScalarExpressionOracle) :
    evaluateScalarOracle (halfSinExpression n f g)=
      halfSinOracle n (evaluateScalarOracle f) (evaluateScalarOracle g) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [halfSinExpression,expressionSqrt_eval,expressionMeanMinus_eval,
      halfCosExpression_eval,halfSinOracle]

def AngleAtom.cosExpression : AngleAtom → ScalarExpressionOracle
  | .pi => constantExpression (-1)
  | .merge A B j => if j=0 ∨ A+B=0 then constantExpression 1
      else expressionSqrt (constantExpression ((A:ℚ)/(A+B)))

def AngleAtom.sinExpression : AngleAtom → ScalarExpressionOracle
  | .pi => constantExpression 0
  | .merge A B j => if j=0 ∨ A+B=0 then constantExpression 0
      else expressionSqrt (constantExpression ((B:ℚ)/(A+B)))

@[simp] theorem AngleAtom.cosExpression_eval (a : AngleAtom) :
    evaluateScalarOracle a.cosExpression=a.cosOracle := by
  cases a with
  | pi => rfl
  | merge A B j =>
    simp only [cosExpression,AngleAtom.cosOracle]
    split_ifs <;> rfl

@[simp] theorem AngleAtom.sinExpression_eval (a : AngleAtom) :
    evaluateScalarOracle a.sinExpression=a.sinOracle := by
  cases a with
  | pi => rfl
  | merge A B j =>
    simp only [sinExpression,AngleAtom.sinOracle]
    split_ifs <;> rfl

def AngleCode.cosExpression (a : AngleCode) : ScalarExpressionOracle :=
  halfCosExpression a.halvings a.atom.cosExpression

def AngleCode.sinExpression (a : AngleCode) : ScalarExpressionOracle :=
  if a.negative then expressionNeg (halfSinExpression a.halvings a.atom.cosExpression a.atom.sinExpression)
  else halfSinExpression a.halvings a.atom.cosExpression a.atom.sinExpression

@[simp] theorem AngleCode.cosExpression_eval (a : AngleCode) :
    evaluateScalarOracle a.cosExpression=a.cosOracle := by
  simp only [cosExpression,halfCosExpression_eval,AngleAtom.cosExpression_eval,cosOracle]

@[simp] theorem AngleCode.sinExpression_eval (a : AngleCode) :
    evaluateScalarOracle a.sinExpression=a.sinOracle := by
  cases hn : a.negative <;> simp [sinExpression,sinOracle,hn,expressionNeg_eval,
    halfSinExpression_eval]

def phaseCosExpression (a b : AngleCode) : ScalarExpressionOracle :=
  expressionAdd
    (expressionMul 0 (a.half 1).cosExpression (b.half 1).cosExpression)
    (expressionMul 0 (a.half 1).sinExpression (b.half 1).sinExpression)

def phaseSinExpression (a b : AngleCode) : ScalarExpressionOracle :=
  expressionAdd
    (expressionMul 0 (a.half 1).sinExpression (b.half 1).cosExpression)
    (expressionNeg (expressionMul 0 (a.half 1).cosExpression (b.half 1).sinExpression))

@[simp] theorem phaseCosExpression_eval (a b : AngleCode) :
    evaluateScalarOracle (phaseCosExpression a b)=phaseCosOracle a b := by
  simp only [phaseCosExpression,expressionAdd_eval,expressionMul_eval,
    AngleCode.cosExpression_eval,AngleCode.sinExpression_eval,phaseCosOracle]

@[simp] theorem phaseSinExpression_eval (a b : AngleCode) :
    evaluateScalarOracle (phaseSinExpression a b)=phaseSinOracle a b := by
  simp only [phaseSinExpression,expressionAdd_eval,expressionMul_eval,expressionNeg_eval,
    AngleCode.cosExpression_eval,AngleCode.sinExpression_eval,phaseSinOracle]

def SingleCode.packetExpression : SingleCode → PacketExpressionOracle
  | .hadamard => fun p => .tuple ![.literal 0,
      .neg (.sqrt (.literal (1/2)) (p+1)),.literal 0,.neg (.sqrt (.literal (1/2)) (p+1))]
  | .yBasis => fun _ => .tuple ![.literal (1/2),.literal (1/2),.literal (1/2),.literal (1/2)]
  | .phase a b => fun p => .tuple ![phaseCosExpression a b p,phaseSinExpression a b p,.literal 0,.literal 0]
  | .inverse u => expressionPacketInverse u.packetExpression

/-- The expression is the actual existing provider, including its exact
precision shifts and its global-phase SU2 convention. -/
theorem SingleCode.packetExpression_eval (u : SingleCode) :
    evaluatePacketOracle u.packetExpression=u.quaternionOracle := by
  induction u with
  | hadamard => rfl
  | yBasis => rfl
  | phase a b =>
    funext p
    apply List.Vector.ext
    intro i
    fin_cases i
    · exact congrFun (phaseCosExpression_eval a b) p
    · exact congrFun (phaseSinExpression_eval a b) p
    · rfl
    · rfl
  | inverse u ih =>
    rw [SingleCode.packetExpression,expressionPacketInverse_eval,ih]
    funext p
    apply List.Vector.ext
    intro i
    fin_cases i <;> rfl

/-- A concrete integer implementation of the actual target packet provider. -/
def SingleCode.integerPacket (u : SingleCode) (p : ℕ) : IntegerPacket :=
  (u.packetExpression p).integerRun

theorem SingleCode.integerPacket_value (u : SingleCode) (p : ℕ) :
    (u.integerPacket p).value=u.quaternionOracle p := by
  rw [integerPacket,PacketExpression.integerRun_correct]
  exact congrFun u.packetExpression_eval p

/-- The primitive-expression count of these closed providers is independent
of numerical precision. Integer operation bit costs are not unit charges. -/
theorem halfCosExpression_operations (n : ℕ) (f : ScalarExpressionOracle) (T : ℕ)
    (hf : ∀ p,(f p).operations≤T) (p : ℕ) :
    (halfCosExpression n f p).operations≤T+12*n := by
  induction n generalizing p with
  | zero => exact hf p
  | succ n ih =>
    have h := ih (2*p+2)
    simp only [halfCosExpression,expressionSqrt,meanPlusExpression,ScalarExpression.operations]
    omega

theorem halfSinExpression_operations (n : ℕ) (f g : ScalarExpressionOracle) (T : ℕ)
    (hf : ∀ p,(f p).operations≤T) (hg : ∀ p,(g p).operations≤T) (p : ℕ) :
    (halfSinExpression n f g p).operations≤T+12*n := by
  cases n with
  | zero => exact hg p
  | succ n =>
    have h := halfCosExpression_operations n f T hf (2*p+2)
    simp only [halfSinExpression,expressionSqrt,expressionMeanMinus,ScalarExpression.operations]
    omega

theorem AngleAtom.expression_operations (a : AngleAtom) (p : ℕ) :
    (a.cosExpression p).operations≤9 ∧ (a.sinExpression p).operations≤9 := by
  cases a with
  | pi => constructor <;> exact (by decide : 1≤9)
  | merge A B j =>
    simp only [cosExpression,sinExpression]
    split_ifs <;> simp [constantExpression,expressionSqrt,ScalarExpression.operations]

theorem AngleCode.expression_operations (a : AngleCode) (p : ℕ) :
    (a.cosExpression p).operations≤12*a.halvings+10 ∧
    (a.sinExpression p).operations≤12*a.halvings+10 := by
  have hc := halfCosExpression_operations a.halvings a.atom.cosExpression 9
    (fun q => (a.atom.expression_operations q).1) p
  have hs := halfSinExpression_operations a.halvings a.atom.cosExpression a.atom.sinExpression 9
    (fun q => (a.atom.expression_operations q).1) (fun q => (a.atom.expression_operations q).2) p
  constructor
  · unfold cosExpression;omega
  · cases hn : a.negative <;>
      simp only [sinExpression,hn,expressionNeg,Bool.false_eq_true,if_false,if_true,ScalarExpression.operations] <;> omega

theorem SingleCode.packetExpression_operations {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    (u.packetExpression p).operations≤100*(H+3)+4*u.inverseDepth := by
  induction u with
  | hadamard => simp [packetExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth];omega
  | yBasis => simp [packetExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth];omega
  | phase a b =>
    have hca := ((a.half 1).expression_operations (p+3)).1
    have hsa := ((a.half 1).expression_operations (p+3)).2
    have hcb := ((b.half 1).expression_operations (p+3)).1
    have hsb := ((b.half 1).expression_operations (p+3)).2
    have ha := h.1.2
    have hb := h.2.2
    have ha' : (a.half 1).halvings≤H+1 := Nat.add_le_add_right ha 1
    have hb' : (b.half 1).halvings≤H+1 := Nat.add_le_add_right hb 1
    have hc : (phaseCosExpression a b p).operations≤48*H+91 := by
      simp only [phaseCosExpression,expressionAdd,expressionMul,ScalarExpression.operations,
        Nat.add_zero,Nat.add_assoc,Nat.reduceAdd]
      omega
    have hs : (phaseSinExpression a b p).operations≤48*H+92 := by
      simp only [phaseSinExpression,expressionAdd,expressionMul,expressionNeg,ScalarExpression.operations,
        Nat.add_zero,Nat.add_assoc,Nat.reduceAdd]
      omega
    simp [packetExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth]
    omega
  | inverse u ih =>
    have hu := ih h
    simp only [packetExpression,expressionPacketInverse,PacketExpression.operations,inverseDepth]
    omega

/-- Rational literal height follows from the actual bounded occupation counts. -/
theorem ratioLiteral_budget (A B M : ℕ) (hAB : A+B≤M) :
    rationalBinaryExponent ((A:ℚ)/(A+B))≤binaryWidth M+1 := by
  by_cases hzero : A+B=0
  · have hA : A=0 := by omega
    norm_num [hA,rationalBinaryExponent]
  · let x : IntegerScalar := ⟨(A:ℤ),A+B,by omega⟩
    have hpow : M≤2^binaryWidth M :=
      (Nat.le_succ M).trans (Nat.le_pow_clog (by decide) (M+1))
    have hx : IntegerScalarHeight x (binaryWidth M) :=
      ⟨hAB.trans hpow,by simpa [x] using (show A≤2^binaryWidth M by omega)⟩
    simpa only [x,IntegerScalar.value,Int.cast_natCast,Nat.cast_add] using
      rationalBinaryExponent_le x (binaryWidth M) hx

theorem AngleAtom.expression_budget (a : AngleAtom) (M : ℕ)
    (h : match a with | .pi => True | .merge A B j => A+B≤M ∧ j≤M) (p : ℕ) :
    (a.cosExpression p).integerBitBudget≤binaryWidth M+3+2*p ∧
    (a.sinExpression p).integerBitBudget≤binaryWidth M+3+2*p := by
  cases a with
  | pi =>
    norm_num [cosExpression,sinExpression,constantExpression,ScalarExpression.integerBitBudget,
      rationalBinaryExponent]
    omega
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simp only [cosExpression,sinExpression,if_pos hz,constantExpression,ScalarExpression.integerBitBudget]
      norm_num [rationalBinaryExponent]
      omega
    · have hc := ratioLiteral_budget A B M h.1
      have hs := ratioLiteral_budget B A M (by omega)
      rw [add_comm (B:ℚ) (A:ℚ)] at hs
      simp only [cosExpression,sinExpression,hz,if_false,expressionSqrt,constantExpression,
        ScalarExpression.integerBitBudget]
      constructor <;> omega

def halfExpressionBudget (B n p : ℕ) : ℕ := (B+8*(n+1))*2^(n+1)*(p+2)

theorem halfExpressionBudget_mono {B n p B' n' p' : ℕ}
    (hB : B≤B') (hn : n≤n') (hp : p≤p') :
    halfExpressionBudget B n p≤halfExpressionBudget B' n' p' := by
  unfold halfExpressionBudget
  gcongr

theorem halfExpressionBudget_ge (B n p : ℕ) : p+2≤halfExpressionBudget B n p := by
  have hpow : 1≤2^(n+1) := Nat.one_le_pow _ _ (by decide)
  have hc : 1≤B+8*(n+1) := by omega
  have h := Nat.mul_le_mul_right (p+2) (Nat.mul_le_mul hc hpow)
  simpa [halfExpressionBudget] using h

theorem halfCosExpression_budget (n : ℕ) (f : ScalarExpressionOracle) (B : ℕ)
    (hf : ∀ p,(f p).integerBitBudget≤B+2*p) (p : ℕ) :
    (halfCosExpression n f p).integerBitBudget≤halfExpressionBudget B n p := by
  induction n generalizing p with
  | zero =>
    have h := hf p
    simp only [halfCosExpression,halfExpressionBudget,Nat.zero_add,pow_one]
    nlinarith
  | succ n ih =>
    have h := ih (2*p+2)
    simp only [halfCosExpression,expressionSqrt,meanPlusExpression,ScalarExpression.integerBitBudget,
      rationalBinaryExponent]
    norm_num
    simp only [halfExpressionBudget,pow_succ] at h ⊢
    have hp : 1≤2^n := Nat.one_le_pow _ _ (by decide)
    nlinarith

theorem halfSinExpression_budget (n : ℕ) (f g : ScalarExpressionOracle) (B : ℕ)
    (hf : ∀ p,(f p).integerBitBudget≤B+2*p) (hg : ∀ p,(g p).integerBitBudget≤B+2*p)
    (p : ℕ) : (halfSinExpression n f g p).integerBitBudget≤halfExpressionBudget B n p := by
  cases n with
  | zero =>
    have h := hg p
    simp only [halfSinExpression,halfExpressionBudget,Nat.zero_add,pow_one]
    nlinarith
  | succ n =>
    have h := halfCosExpression_budget n f B hf (2*p+2)
    simp only [halfSinExpression,expressionSqrt,expressionMeanMinus,ScalarExpression.integerBitBudget]
    simp only [halfExpressionBudget,pow_succ] at h ⊢
    have hp : 1≤2^n := Nat.one_le_pow _ _ (by decide)
    nlinarith

theorem AngleCode.expression_budget {M H : ℕ} (a : AngleCode) (h : a.Fits M H) (p : ℕ) :
    (a.cosExpression p).integerBitBudget≤halfExpressionBudget (binaryWidth M+3) H p ∧
    (a.sinExpression p).integerBitBudget≤halfExpressionBudget (binaryWidth M+3) H p := by
  have hc := halfCosExpression_budget a.halvings a.atom.cosExpression (binaryWidth M+3)
    (fun q => (a.atom.expression_budget M h.1 q).1) p
  have hs := halfSinExpression_budget a.halvings a.atom.cosExpression a.atom.sinExpression (binaryWidth M+3)
    (fun q => (a.atom.expression_budget M h.1 q).1) (fun q => (a.atom.expression_budget M h.1 q).2) p
  have hm := halfExpressionBudget_mono (B:=binaryWidth M+3) (p:=p) le_rfl h.2 le_rfl
  constructor
  · exact hc.trans hm
  · cases hn : a.negative <;>
      simpa only [sinExpression,hn,expressionNeg,Bool.false_eq_true,if_false,if_true,
        ScalarExpression.integerBitBudget] using hs.trans hm

def providerHeightBudget (M H p : ℕ) : ℕ :=
  8*halfExpressionBudget (binaryWidth M+3) (H+1) (p+3)+4

theorem SingleCode.packetExpression_budget {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    (u.packetExpression p).integerBitBudget≤providerHeightBudget M H p := by
  induction u with
  | hadamard =>
    have hb := halfExpressionBudget_ge (binaryWidth M+3) (H+1) (p+3)
    norm_num [packetExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold providerHeightBudget
    omega
  | yBasis =>
    have hb := halfExpressionBudget_ge (binaryWidth M+3) (H+1) (p+3)
    norm_num [packetExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold providerHeightBudget
    omega
  | phase a b =>
    have hca := ((a.half 1).expression_budget (h.1.half 1) (p+3)).1
    have hsa := ((a.half 1).expression_budget (h.1.half 1) (p+3)).2
    have hcb := ((b.half 1).expression_budget (h.2.half 1) (p+3)).1
    have hsb := ((b.half 1).expression_budget (h.2.half 1) (p+3)).2
    have hc : (phaseCosExpression a b p).integerBitBudget≤
        4*halfExpressionBudget (binaryWidth M+3) (H+1) (p+3)+1 := by
      simp only [phaseCosExpression,expressionAdd,expressionMul,ScalarExpression.integerBitBudget,
        Nat.add_zero,Nat.add_assoc,Nat.reduceAdd]
      omega
    have hs : (phaseSinExpression a b p).integerBitBudget≤
        4*halfExpressionBudget (binaryWidth M+3) (H+1) (p+3)+1 := by
      simp only [phaseSinExpression,expressionAdd,expressionMul,expressionNeg,ScalarExpression.integerBitBudget,
        Nat.add_zero,Nat.add_assoc,Nat.reduceAdd]
      omega
    norm_num [packetExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold providerHeightBudget
    omega
  | inverse u ih => exact ih h

/-- Literal numerator and denominator bounds for the actual integer packet,
without an opaque target provider assumption. -/
theorem SingleCode.integerPacket_height {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    IntegerPacketHeight (u.integerPacket p) (providerHeightBudget M H p) :=
  IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height _)
    (u.packetExpression_budget h p)

theorem extractionCode_provider_resources {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    (u.packetExpression p).operations≤100*(halvingBudget k+3)+4 ∧
    IntegerPacketHeight (u.integerPacket p) (providerHeightBudget (4*k) (halvingBudget k) p) ∧
    (u.integerPacket p).value=u.quaternionOracle p := by
  have h := extractionCode_fits k (.single i u) hu
  refine ⟨?_,u.integerPacket_height h.1 p,u.integerPacket_value p⟩
  have ho := u.packetExpression_operations h.1 p
  have hd := h.2
  omega

end EffectiveEncoding
