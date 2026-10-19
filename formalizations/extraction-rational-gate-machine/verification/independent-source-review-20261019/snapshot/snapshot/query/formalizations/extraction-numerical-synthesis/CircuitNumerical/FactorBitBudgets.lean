import CircuitNumerical.IntegerExpressionBudgets

namespace CircuitRecursion

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev BitEnvelope := ℕ×ℕ
def ScalarBitEnvelope (f : ScalarExpressionOracle) (e : BitEnvelope) : Prop :=
  ∀ p,(f p).integerBitBudget≤e.1*p+e.2
def PacketBitEnvelope (f : PacketExpressionOracle) (e : BitEnvelope) : Prop :=
  ∀ p,(f p).integerBitBudget≤e.1*p+e.2

def bitAddEnvelope (e f : BitEnvelope) : BitEnvelope := (e.1+f.1,e.1+e.2+f.1+f.2+1)
def bitMulEnvelope (b : ℕ) (e f : BitEnvelope) : BitEnvelope :=
  (e.1+f.1,(e.1+f.1)*(b+2)+e.2+f.2)
def bitInvEnvelope (b : ℕ) (e : BitEnvelope) : BitEnvelope := (e.1,e.1*(2*b+2)+e.2)
def bitSqrtEnvelope (e : BitEnvelope) : BitEnvelope := (2*e.1+2,2*e.1+e.2+2)
def bitMeanEnvelope (e : BitEnvelope) : BitEnvelope := (e.1,e.2+2)
def bitPacketMulEnvelope (e f : BitEnvelope) : BitEnvelope :=
  (e.1+f.1,4*e.1+e.2+4*f.1+f.2+2)
def bitDistanceEnvelope (e f : BitEnvelope) : BitEnvelope :=
  (2*e.1+2*f.1,12*e.1+2*e.2+12*f.1+2*f.2+4)

theorem bitAdd_bound (f g : ScalarExpressionOracle) (e d : BitEnvelope)
    (hf : ScalarBitEnvelope f e) (hg : ScalarBitEnvelope g d) :
    ScalarBitEnvelope (expressionAdd f g) (bitAddEnvelope e d) := by
  intro p
  have h1:=hf (p+1);have h2:=hg (p+1)
  simp only [expressionAdd,ScalarExpression.integerBitBudget,bitAddEnvelope,Prod.fst,Prod.snd]
  nlinarith
theorem bitNeg_bound (f : ScalarExpressionOracle) (e : BitEnvelope) (hf : ScalarBitEnvelope f e) :
    ScalarBitEnvelope (expressionNeg f) e := hf
theorem bitMul_bound (f g : ScalarExpressionOracle) (b : ℕ) (e d : BitEnvelope)
    (hf : ScalarBitEnvelope f e) (hg : ScalarBitEnvelope g d) :
    ScalarBitEnvelope (expressionMul b f g) (bitMulEnvelope b e d) := by
  intro p
  have h1:=hf (p+b+2);have h2:=hg (p+b+2)
  simp only [expressionMul,ScalarExpression.integerBitBudget,bitMulEnvelope,Prod.fst,Prod.snd]
  nlinarith
theorem bitInv_bound (f : ScalarExpressionOracle) (b : ℕ) (e : BitEnvelope) (hf : ScalarBitEnvelope f e) :
    ScalarBitEnvelope (expressionInv b f) (bitInvEnvelope b e) := by
  intro p
  have h:=hf (p+2*b+2)
  simp only [expressionInv,ScalarExpression.integerBitBudget,bitInvEnvelope,Prod.fst,Prod.snd]
  nlinarith
theorem bitSqrt_bound (f : ScalarExpressionOracle) (e : BitEnvelope) (hf : ScalarBitEnvelope f e) :
    ScalarBitEnvelope (expressionSqrt f) (bitSqrtEnvelope e) := by
  intro p
  have h:=hf (2*p+2)
  simp only [expressionSqrt,ScalarExpression.integerBitBudget,bitSqrtEnvelope,Prod.fst,Prod.snd]
  nlinarith
theorem bitMean_bound (f : ScalarExpressionOracle) (e : BitEnvelope) (hf : ScalarBitEnvelope f e) :
    ScalarBitEnvelope (expressionMeanMinus f) (bitMeanEnvelope e) := by
  intro p
  have h:=hf p
  exact Nat.add_le_add_right h 2
theorem bitCoordinate_bound (f : PacketExpressionOracle) (i : Fin 4) (e : BitEnvelope)
    (hf : PacketBitEnvelope f e) : ScalarBitEnvelope (expressionCoordinate f i) e := hf
theorem bitPacketMul_bound (f g : PacketExpressionOracle) (e d : BitEnvelope)
    (hf : PacketBitEnvelope f e) (hg : PacketBitEnvelope g d) :
    PacketBitEnvelope (expressionPacketMul f g) (bitPacketMulEnvelope e d) := by
  intro p
  have h1:=hf (p+4);have h2:=hg (p+4)
  simp only [expressionPacketMul,PacketExpression.integerBitBudget,bitPacketMulEnvelope,Prod.fst,Prod.snd]
  nlinarith
theorem bitPacketInverse_bound (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) :
    PacketBitEnvelope (expressionPacketInverse f) e := hf
theorem bitDistance_bound (f g : PacketExpressionOracle) (e d : BitEnvelope)
    (hf : PacketBitEnvelope f e) (hg : PacketBitEnvelope g d) :
    ScalarBitEnvelope (expressionDistance f g) (bitDistanceEnvelope e d) := by
  intro p
  have h1:=hf (p+6);have h2:=hg (p+6)
  simp only [expressionDistance,ScalarExpression.integerBitBudget,bitDistanceEnvelope,Prod.fst,Prod.snd]
  nlinarith

@[simp] theorem rationalBinaryExponent_zero : rationalBinaryExponent 0=1 := by decide
@[simp] theorem rationalBinaryExponent_one : rationalBinaryExponent 1=1 := by decide

theorem bitFrame_bound (j : Fin 4) : PacketBitEnvelope (expressionFrame j) (0,4) := by
  intro p
  have ht : ∀ i : Fin 4,rationalBinaryExponent (if i=j then (1:ℚ) else 0)≤1 := by
    intro i
    split_ifs <;> simp
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => ht i)
  simpa only [expressionFrame,PacketExpression.integerBitBudget,List.Vector.get_ofFn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,zero_mul,zero_add] using h

def bitBalancedSEnvelope (e : BitEnvelope) : BitEnvelope := bitSqrtEnvelope (bitSqrtEnvelope (bitMeanEnvelope e))
def bitBalancedCEnvelope (e : BitEnvelope) : BitEnvelope :=
  bitSqrtEnvelope (bitAddEnvelope (0,1) (bitMulEnvelope 0 (bitBalancedSEnvelope e) (bitBalancedSEnvelope e)))
def bitReferenceEnvelope (e : BitEnvelope) : BitEnvelope :=
  ((bitBalancedCEnvelope e).1+(bitBalancedSEnvelope e).1,
    (bitBalancedCEnvelope e).2+(bitBalancedSEnvelope e).2+2)
def bitBalancedReferenceEnvelope (e : BitEnvelope) : BitEnvelope :=
  bitPacketMulEnvelope (bitPacketMulEnvelope (bitPacketMulEnvelope (bitReferenceEnvelope e)
    (bitReferenceEnvelope e)) (bitReferenceEnvelope e)) (bitReferenceEnvelope e)
def bitChartTargetEnvelope (e : BitEnvelope) : BitEnvelope :=
  bitPacketMulEnvelope (bitPacketMulEnvelope (0,4) e) (0,4)
def bitChartMassEnvelope (e d : BitEnvelope) : BitEnvelope := bitDistanceEnvelope e (bitChartTargetEnvelope d)
def bitRadiusEnvelope (e d : BitEnvelope) : BitEnvelope := bitSqrtEnvelope (bitChartMassEnvelope e d)
def bitNormalizedEnvelope (e d : BitEnvelope) (t : ℕ) : BitEnvelope :=
  let scalar := bitMulEnvelope (t+2) (bitAddEnvelope e (bitChartTargetEnvelope d))
    (bitInvEnvelope (t+1) (bitRadiusEnvelope e d))
  (4*scalar.1,4*scalar.2)
def bitConjugatorEnvelope (e : BitEnvelope) (t : ℕ) : BitEnvelope :=
  let d:=bitBalancedReferenceEnvelope e
  let score:=bitChartMassEnvelope e d
  let branch:=bitPacketMulEnvelope (bitNormalizedEnvelope e d t) (0,4)
  (4*branch.1,4*(score.1*(2*t+2)+score.2)+4*branch.2)
def bitFactorEnvelope (e : BitEnvelope) (t : ℕ) : BitEnvelope :=
  bitPacketMulEnvelope (bitPacketMulEnvelope (bitConjugatorEnvelope e t) (bitReferenceEnvelope e))
    (bitConjugatorEnvelope e t)

theorem bitBalancedS_bound (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) :
    ScalarBitEnvelope (expressionBalancedS f) (bitBalancedSEnvelope e) :=
  bitSqrt_bound _ _ (bitSqrt_bound _ _ (bitMean_bound _ _ (bitCoordinate_bound f 0 e hf)))

theorem bitBalancedC_bound (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) :
    ScalarBitEnvelope (expressionBalancedC f) (bitBalancedCEnvelope e) := by
  have h1 : ScalarBitEnvelope (fun _ => ScalarExpression.literal 1) (0,1) := by intro p;simp [ScalarExpression.integerBitBudget]
  exact bitSqrt_bound _ _ (bitAdd_bound _ _ _ _ h1
    (bitNeg_bound _ _ (bitMul_bound _ _ 0 _ _ (bitBalancedS_bound f e hf) (bitBalancedS_bound f e hf))))

theorem bitReference_bounds (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) :
    PacketBitEnvelope (expressionReferenceX f) (bitReferenceEnvelope e) ∧
    PacketBitEnvelope (expressionReferenceY f) (bitReferenceEnvelope e) := by
  have hc:=bitBalancedC_bound f e hf
  have hs:=bitBalancedS_bound f e hf
  constructor <;> intro p
  · have h1:=hc p;have h2:=hs p
    simp [expressionReferenceX,PacketExpression.integerBitBudget,ScalarExpression.integerBitBudget,
      Fin.sum_univ_four,bitReferenceEnvelope]
    nlinarith
  · have h1:=hc p;have h2:=hs p
    simp [expressionReferenceY,PacketExpression.integerBitBudget,ScalarExpression.integerBitBudget,
      Fin.sum_univ_four,bitReferenceEnvelope]
    nlinarith

theorem bitBalancedReference_bound (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) :
    PacketBitEnvelope (expressionBalancedReference f) (bitBalancedReferenceEnvelope e) := by
  have hx:=(bitReference_bounds f e hf).1
  have hy:=(bitReference_bounds f e hf).2
  exact bitPacketMul_bound _ _ _ _ (bitPacketMul_bound _ _ _ _ (bitPacketMul_bound _ _ _ _ hx hy)
    (bitPacketInverse_bound _ _ hx)) (bitPacketInverse_bound _ _ hy)

theorem bitChartTarget_bound (g : PacketExpressionOracle) (d : BitEnvelope) (hg : PacketBitEnvelope g d) (j : Fin 4) :
    PacketBitEnvelope (expressionChartTarget g j) (bitChartTargetEnvelope d) :=
  bitPacketMul_bound _ _ _ _ (bitPacketMul_bound _ _ _ _ (bitFrame_bound j) hg) (bitPacketInverse_bound _ _ (bitFrame_bound j))

theorem bitChartMass_bound (f g : PacketExpressionOracle) (e d : BitEnvelope)
    (hf : PacketBitEnvelope f e) (hg : PacketBitEnvelope g d) (j : Fin 4) :
    ScalarBitEnvelope (fun p => expressionChartMass f g p j) (bitChartMassEnvelope e d) :=
  bitDistance_bound _ _ _ _ hf (bitPacketInverse_bound _ _ (bitChartTarget_bound g d hg j))

theorem bitNormalized_bound (f g : PacketExpressionOracle) (e d : BitEnvelope)
    (hf : PacketBitEnvelope f e) (hg : PacketBitEnvelope g d) (t : ℕ) (j : Fin 4) :
    PacketBitEnvelope (expressionNormalized f g t j) (bitNormalizedEnvelope e d t) := by
  have hr:=bitInv_bound _ (t+1) _ (bitSqrt_bound _ _ (bitChartMass_bound f g e d hf hg j))
  have hn : ∀ i,ScalarBitEnvelope
      (expressionMul (t+2) (expressionAdd (expressionCoordinate f i)
        (expressionNeg (expressionCoordinate (expressionPacketInverse (expressionChartTarget g j)) i)))
        (expressionInv (t+1) (expressionRadius f g j)))
      (bitMulEnvelope (t+2) (bitAddEnvelope e (bitChartTargetEnvelope d)) (bitInvEnvelope (t+1) (bitRadiusEnvelope e d))) := by
    intro i
    exact bitMul_bound _ _ (t+2) _ _ (bitAdd_bound _ _ _ _ (bitCoordinate_bound f i e hf)
      (bitNeg_bound _ _ (bitCoordinate_bound _ i _ (bitPacketInverse_bound _ _ (bitChartTarget_bound g d hg j))))) hr
  intro p
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hn i p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  change (∑ i : Fin 4,_ )≤_
  dsimp only at h ⊢
  convert h using 1 <;> first | rfl | simp only [bitNormalizedEnvelope];ring

theorem bitConjugator_bound (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) (t : ℕ) :
    PacketBitEnvelope (expressionConjugator f t) (bitConjugatorEnvelope e t) := by
  have hg:=bitBalancedReference_bound f e hf
  have hs:=fun j => bitChartMass_bound f _ e _ hf hg j (2*t+2)
  have hb:=fun j => bitPacketMul_bound _ _ _ _ (bitNormalized_bound f _ e _ hf hg t j) (bitFrame_bound j)
  intro p
  have h1:=Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hs j)
  have h2:=Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hb j p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h1 h2
  change (∑ j : Fin 4,_)+(∑ j : Fin 4,_)≤_
  dsimp only at h1 h2 ⊢
  have h:=Nat.add_le_add h1 h2
  convert h using 1 <;> first | rfl | simp only [bitConjugatorEnvelope];ring

theorem bitFactor_bounds (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) (t : ℕ) :
    PacketBitEnvelope (expressionFactorX f t) (bitFactorEnvelope e t) ∧
    PacketBitEnvelope (expressionFactorY f t) (bitFactorEnvelope e t) := by
  have hp:=bitConjugator_bound f e hf t
  have h1:=bitPacketMul_bound _ _ _ _
    (bitPacketMul_bound _ _ _ _ hp (bitReference_bounds f e hf).1) (bitPacketInverse_bound _ _ hp)
  have h2:=bitPacketMul_bound _ _ _ _
    (bitPacketMul_bound _ _ _ _ hp (bitReference_bounds f e hf).2) (bitPacketInverse_bound _ _ hp)
  exact ⟨h1,h2⟩

theorem fixedFactor_integerBitBudget (f : PacketExpressionOracle) (C t p : ℕ)
    (hf : PacketBitEnvelope f (0,C)) :
    (expressionFactorX f t p).integerBitBudget≤1000000*(C+p+t+1) ∧
    (expressionFactorY f t p).integerBitBudget≤1000000*(C+p+t+1) := by
  have hx:=(bitFactor_bounds f (0,C) hf t).1 p
  have hy:=(bitFactor_bounds f (0,C) hf t).2 p
  have h : (bitFactorEnvelope (0,C) t).1*p+(bitFactorEnvelope (0,C) t).2≤1000000*(C+p+t+1) := by
    norm_num [bitFactorEnvelope,bitConjugatorEnvelope,bitNormalizedEnvelope,bitRadiusEnvelope,
      bitChartMassEnvelope,bitChartTargetEnvelope,bitBalancedReferenceEnvelope,bitReferenceEnvelope,
      bitBalancedCEnvelope,bitBalancedSEnvelope,bitPacketMulEnvelope,bitDistanceEnvelope,
      bitMulEnvelope,bitInvEnvelope,bitAddEnvelope,bitSqrtEnvelope,bitMeanEnvelope]
    omega
  exact ⟨hx.trans h,hy.trans h⟩

end CircuitRecursion
