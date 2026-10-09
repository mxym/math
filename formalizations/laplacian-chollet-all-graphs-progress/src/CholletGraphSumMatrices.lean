import CholletDiagonalExtension
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! Exact direct-sum and one-point-sum Laplacian identities. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
noncomputable section

def optionLeftEmbedding : Option α ↪ Option (α ⊕ β) where
  toFun := Option.map Sum.inl
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

def optionRightEmbedding : Option β ↪ Option (α ⊕ β) where
  toFun := Option.map Sum.inr
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

@[simp] theorem optionLeftEmbedding_none : optionLeftEmbedding (α := α) (β := β) none = none := rfl
@[simp] theorem optionLeftEmbedding_some (a : α) :
    optionLeftEmbedding (α := α) (β := β) (some a) = some (.inl a) := rfl
@[simp] theorem optionRightEmbedding_none : optionRightEmbedding (α := α) (β := β) none = none := rfl
@[simp] theorem optionRightEmbedding_some (b : β) :
    optionRightEmbedding (α := α) (β := β) (some b) = some (.inr b) := rfl

theorem laplacian_directSum_identity (H : SimpleGraph (α ⊕ β)) [DecidableRel H.Adj]
    (hcross : ∀ a b,¬H.Adj (.inl a) (.inr b)) :
    H.lapMatrix ℝ = directSumMatrix
      ((H.comap Sum.inl).lapMatrix ℝ) ((H.comap Sum.inr).lapMatrix ℝ) := by
  have hc : ∀ b a,¬H.Adj (.inr b) (.inl a) := fun b a h => hcross a b h.symm
  have hdleft (a : α) : (H.degree (.inl a) : ℝ)=(H.comap Sum.inl).degree a := by
    rw [H.degree_eq_sum_if_adj (R := ℝ),Fintype.sum_sum_type,
      (H.comap Sum.inl).degree_eq_sum_if_adj (R := ℝ)]
    simp [hcross]
  have hdright (b : β) : (H.degree (.inr b) : ℝ)=(H.comap Sum.inr).degree b := by
    rw [H.degree_eq_sum_if_adj (R := ℝ),Fintype.sum_sum_type,
      (H.comap Sum.inr).degree_eq_sum_if_adj (R := ℝ)]
    simp [hc]
  ext i j
  cases i <;> cases j <;>
    simp [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply,directSumMatrix,hcross,hc,hdleft,hdright]

theorem laplacian_onePointSum_identity (H : SimpleGraph (Option (α ⊕ β)))
    [DecidableRel H.Adj]
    (hcross : ∀ a b,¬H.Adj (some (.inl a)) (some (.inr b))) :
    H.lapMatrix ℝ = onePointSumMatrix
      ((H.comap (optionLeftEmbedding (α := α) (β := β))).lapMatrix ℝ)
      ((H.comap (optionRightEmbedding (α := α) (β := β))).lapMatrix ℝ) := by
  let HL := H.comap (optionLeftEmbedding (α := α) (β := β))
  let HR := H.comap (optionRightEmbedding (α := α) (β := β))
  have hc : ∀ b a,¬H.Adj (some (.inr b)) (some (.inl a)) :=
    fun b a h => hcross a b h.symm
  have hdroot : (H.degree none : ℝ)=(HL.degree none : ℝ)+HR.degree none := by
    rw [H.degree_eq_sum_if_adj (R := ℝ),HL.degree_eq_sum_if_adj (R := ℝ),
      HR.degree_eq_sum_if_adj (R := ℝ)]
    simp only [Fintype.sum_option,Fintype.sum_sum_type,HL,HR,SimpleGraph.comap_adj,
      optionLeftEmbedding_none,optionLeftEmbedding_some,optionRightEmbedding_none,
      optionRightEmbedding_some,H.irrefl,ite_false,zero_add,add_zero]
    rfl
  have hdleft (a : α) : (H.degree (some (.inl a)) : ℝ)=HL.degree (some a) := by
    rw [H.degree_eq_sum_if_adj (R := ℝ),HL.degree_eq_sum_if_adj (R := ℝ)]
    simp only [Fintype.sum_option,Fintype.sum_sum_type,HL,SimpleGraph.comap_adj,
      optionLeftEmbedding_none,optionLeftEmbedding_some,hcross,ite_false,
      Finset.sum_const_zero,add_zero]
    rfl
  have hdright (b : β) : (H.degree (some (.inr b)) : ℝ)=HR.degree (some b) := by
    rw [H.degree_eq_sum_if_adj (R := ℝ),HR.degree_eq_sum_if_adj (R := ℝ)]
    simp only [Fintype.sum_option,Fintype.sum_sum_type,HR,SimpleGraph.comap_adj,
      optionRightEmbedding_none,optionRightEmbedding_some,hc,ite_false,
      Finset.sum_const_zero,zero_add]
    rfl
  ext i j
  cases i with
  | none =>
    cases j with
    | none => simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,hdroot,HL,HR]
    | some j => cases j <;> simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply]
  | some i =>
    cases i with
    | inl a =>
      cases j with
      | none => simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix_apply]
      | some j => cases j <;> simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix_apply,Matrix.diagonal_apply,hdleft,HL,hcross]
    | inr b =>
      cases j with
      | none => simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix_apply]
      | some j => cases j <;> simp [onePointSumMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix_apply,Matrix.diagonal_apply,hdright,HR,hc]

end
end Chollet
