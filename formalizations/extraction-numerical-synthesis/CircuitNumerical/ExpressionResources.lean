import CircuitNumerical.TracedNumericalSK

namespace CircuitRecursion

set_option maxRecDepth 4096

def ScalarOperationBound (f : ScalarExpressionOracle) (C : ℕ) : Prop := ∀ p,(f p).operations≤C
def PacketOperationBound (f : PacketExpressionOracle) (C : ℕ) : Prop := ∀ p,(f p).operations≤C

theorem expressionAdd_bound (f g : ScalarExpressionOracle) (C D : ℕ)
    (hf : ScalarOperationBound f C) (hg : ScalarOperationBound g D) :
    ScalarOperationBound (expressionAdd f g) (C+D+1) := by
  intro p
  exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) 1
theorem expressionNeg_bound (f : ScalarExpressionOracle) (C : ℕ) (hf : ScalarOperationBound f C) :
    ScalarOperationBound (expressionNeg f) (C+1) := fun p => Nat.add_le_add_right (hf p) 1
theorem expressionMul_bound (f g : ScalarExpressionOracle) (b C D : ℕ)
    (hf : ScalarOperationBound f C) (hg : ScalarOperationBound g D) :
    ScalarOperationBound (expressionMul b f g) (C+D+1) := by
  intro p
  exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) 1
theorem expressionInv_bound (f : ScalarExpressionOracle) (b C : ℕ) (hf : ScalarOperationBound f C) :
    ScalarOperationBound (expressionInv b f) (C+1) := fun p => Nat.add_le_add_right (hf _) 1
theorem expressionSqrt_bound (f : ScalarExpressionOracle) (C : ℕ) (hf : ScalarOperationBound f C) :
    ScalarOperationBound (expressionSqrt f) (C+8) := fun p => Nat.add_le_add_right (hf _) 8
theorem expressionMeanMinus_bound (f : ScalarExpressionOracle) (C : ℕ) (hf : ScalarOperationBound f C) :
    ScalarOperationBound (expressionMeanMinus f) (C+2) := fun p => Nat.add_le_add_right (hf p) 2
theorem expressionCoordinate_bound (f : PacketExpressionOracle) (i : Fin 4) (C : ℕ) (hf : PacketOperationBound f C) :
    ScalarOperationBound (expressionCoordinate f i) (C+1) := fun p => Nat.add_le_add_right (hf p) 1
theorem expressionPacketMul_bound (f g : PacketExpressionOracle) (C D : ℕ)
    (hf : PacketOperationBound f C) (hg : PacketOperationBound g D) :
    PacketOperationBound (expressionPacketMul f g) (C+D+48) := by
  intro p
  exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) 48
theorem expressionPacketInverse_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionPacketInverse f) (C+4) := fun p => Nat.add_le_add_right (hf p) 4
theorem expressionDistance_bound (f g : PacketExpressionOracle) (C D : ℕ)
    (hf : PacketOperationBound f C) (hg : PacketOperationBound g D) (p : ℕ) :
    (expressionDistance f g p).operations≤C+D+16 := by
  exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) 16

theorem expressionBalancedS_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    ScalarOperationBound (expressionBalancedS f) (C+19) := by
  exact expressionSqrt_bound _ _ (expressionSqrt_bound _ _
    (expressionMeanMinus_bound _ _ (expressionCoordinate_bound f 0 C hf)))
theorem expressionBalancedC_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    ScalarOperationBound (expressionBalancedC f) (2*C+50) := by
  have hs := expressionBalancedS_bound f C hf
  have h := expressionSqrt_bound _ _ (expressionAdd_bound (fun _ => ScalarExpression.literal 1) _ 1 _ (fun _ => le_refl 1)
    (expressionNeg_bound _ _ (expressionMul_bound _ _ 0 _ _ hs hs)))
  convert h using 1 <;> first | rfl | ring

theorem expressionReferenceX_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionReferenceX f) (3*C+75) := by
  intro p
  have hc := expressionBalancedC_bound f C hf p
  have hs := expressionBalancedS_bound f C hf p
  simp [expressionReferenceX,PacketExpression.operations,Fin.sum_univ_four,ScalarExpression.operations]
  omega
theorem expressionReferenceY_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionReferenceY f) (3*C+75) := by
  intro p
  have hc := expressionBalancedC_bound f C hf p
  have hs := expressionBalancedS_bound f C hf p
  simp [expressionReferenceY,PacketExpression.operations,Fin.sum_univ_four,ScalarExpression.operations]
  omega
theorem expressionBalancedReference_bound (f : PacketExpressionOracle) (C : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionBalancedReference f) (12*C+452) := by
  have hx := expressionReferenceX_bound f C hf
  have hy := expressionReferenceY_bound f C hf
  have h := expressionPacketMul_bound _ _ _ _
    (expressionPacketMul_bound _ _ _ _ (expressionPacketMul_bound _ _ _ _ hx hy)
      (expressionPacketInverse_bound _ _ hx)) (expressionPacketInverse_bound _ _ hy)
  convert h using 1 <;> first | rfl | ring
theorem expressionChartTarget_bound (g : PacketExpressionOracle) (j : Fin 4) (D : ℕ) (hg : PacketOperationBound g D) :
    PacketOperationBound (expressionChartTarget g j) (D+102) := by
  have hj : PacketOperationBound (expressionFrame j) 1 := fun _ => le_refl 1
  have h := expressionPacketMul_bound _ _ _ _ (expressionPacketMul_bound _ _ _ _ hj hg)
    (expressionPacketInverse_bound _ _ hj)
  convert h using 1 <;> first | rfl | ring
theorem expressionChartMass_bound (f g : PacketExpressionOracle) (C D : ℕ)
    (hf : PacketOperationBound f C) (hg : PacketOperationBound g D) (p : ℕ) (j : Fin 4) :
    (expressionChartMass f g p j).operations≤C+D+122 := by
  have h := expressionDistance_bound _ _ _ _ hf
    (expressionPacketInverse_bound _ _ (expressionChartTarget_bound g j D hg)) p
  convert h using 1 <;> first | rfl | ring
theorem expressionNormalized_bound (f g : PacketExpressionOracle) (C D t : ℕ)
    (hf : PacketOperationBound f C) (hg : PacketOperationBound g D) (j : Fin 4) :
    PacketOperationBound (expressionNormalized f g t j) (8*C+8*D+972) := by
  have hr : ScalarOperationBound (expressionRadius f g j) (C+D+130) := by
    have h := expressionSqrt_bound _ (C+D+122) (fun p => expressionChartMass_bound f g C D hf hg p j)
    exact h
  have hi := expressionInv_bound _ (t+1) _ hr
  have hadj := expressionPacketInverse_bound _ _ (expressionChartTarget_bound g j D hg)
  have hc : ∀ i,ScalarOperationBound
      (expressionMul (t+2) (expressionAdd (expressionCoordinate f i)
        (expressionNeg (expressionCoordinate (expressionPacketInverse (expressionChartTarget g j)) i)))
        (expressionInv (t+1) (expressionRadius f g j))) (2*C+2*D+242) := by
    intro i
    have h := expressionMul_bound _ _ (t+2) _ _
      (expressionAdd_bound _ _ _ _ (expressionCoordinate_bound f i C hf)
        (expressionNeg_bound _ _ (expressionCoordinate_bound _ i _ hadj))) hi
    convert h using 1 <;> first | rfl | ring
  intro p
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hc i p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  change (∑ i : Fin 4,_)+4≤_
  have h' := Nat.add_le_add_right h 4
  dsimp only at h' ⊢
  omega
theorem expressionConjugator_bound (f : PacketExpressionOracle) (C t : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionConjugator f t) (468*C+20847) := by
  have hg := expressionBalancedReference_bound f C hf
  have hs := fun j => expressionChartMass_bound f _ C _ hf hg (2*t+2) j
  have hb := fun j => expressionPacketMul_bound _ (expressionFrame j) _ 1
    (expressionNormalized_bound f _ C _ t hf hg j) (fun _ => le_refl 1)
  intro p
  have h1 := Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hs j)
  have h2 := Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hb j p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h1 h2
  change (∑ j : Fin 4,_)+(∑ j : Fin 4,_)+3≤_
  dsimp only at h1 h2 ⊢
  omega
set_option maxRecDepth 3000 in
theorem expressionFactor_bounds (f : PacketExpressionOracle) (C t : ℕ) (hf : PacketOperationBound f C) :
    PacketOperationBound (expressionFactorX f t) (50000*(C+1)) ∧
    PacketOperationBound (expressionFactorY f t) (50000*(C+1)) := by
  have hp := expressionConjugator_bound f C t hf
  have one : ∀ g,PacketOperationBound g (3*C+75) →
      PacketOperationBound (expressionConjugate (expressionConjugator f t) g) (50000*(C+1)) := by
    intro g hg p
    have h := expressionPacketMul_bound _ _ _ _
      (expressionPacketMul_bound _ _ _ _ hp hg) (expressionPacketInverse_bound _ _ hp) p
    exact h.trans (by omega)
  exact ⟨one _ (expressionReferenceX_bound f C hf),one _ (expressionReferenceY_bound f C hf)⟩

end CircuitRecursion
