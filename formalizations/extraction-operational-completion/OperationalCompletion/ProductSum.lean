import OperationalCompletion.SumChannels

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace OperationalCompletion
noncomputable section

variable {α β α' β' ο κ τ κ' τ' : Type*}
  [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [Fintype ο]
  [Fintype κ] [Fintype τ] [Fintype κ'] [Fintype τ']
  [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β'] [DecidableEq ο]

def bipartiteLeft : Matrix ((α⊕α')×(β⊕β')) (α×β) ℂ :=
  sumLeft ⊗ₖ sumLeft

def bipartiteRight : Matrix ((α⊕α')×(β⊕β')) (α'×β') ℂ :=
  sumRight ⊗ₖ sumRight

theorem bipartiteLeft_isometry :
    (bipartiteLeft (α:=α) (β:=β) (α':=α') (β':=β'))ᴴ*
      bipartiteLeft (α:=α) (β:=β) (α':=α') (β':=β')=1 :=
  Extraction.kronecker_isometry _ _ sumLeft_isometry sumLeft_isometry

theorem bipartiteRight_isometry :
    (bipartiteRight (α:=α) (β:=β) (α':=α') (β':=β'))ᴴ*
      bipartiteRight (α:=α) (β:=β) (α':=α') (β':=β')=1 :=
  Extraction.kronecker_isometry _ _ sumRight_isometry sumRight_isometry

theorem bipartiteLeft_right_cross :
    (bipartiteLeft (α:=α) (β:=β) (α':=α') (β':=β'))ᴴ*
      bipartiteRight (α:=α) (β:=β) (α':=α') (β':=β')=0 := by
  unfold bipartiteLeft bipartiteRight
  rw [Matrix.conjTranspose_kronecker,←Matrix.mul_kronecker_mul,
    sumLeft_right_cross,sumLeft_right_cross,Matrix.zero_kronecker]

theorem bipartiteRight_left_cross :
    (bipartiteRight (α:=α) (β:=β) (α':=α') (β':=β'))ᴴ*
      bipartiteLeft (α:=α) (β:=β) (α':=α') (β':=β')=0 := by
  unfold bipartiteLeft bipartiteRight
  rw [Matrix.conjTranspose_kronecker,←Matrix.mul_kronecker_mul,
    sumRight_left_cross,sumRight_left_cross,Matrix.zero_kronecker]

theorem productJoinedKraus_left (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ)
    (C : κ' → Matrix ο α' ℂ) (D : τ' → Matrix ο β' ℂ) (X : Matrix (α×β) (α×β) ℂ) :
    Extraction.krausApply (Extraction.productKraus (joinedKraus A C) (joinedKraus B D))
      (bipartiteLeft*X*bipartiteLeftᴴ)=Extraction.krausApply (Extraction.productKraus A B) X := by
  rw [krausApply_encoded_rect]
  unfold Extraction.productKraus bipartiteLeft
  simp_rw [←Matrix.mul_kronecker_mul,joinedKraus_mul_left]
  simp [Fintype.sum_prod_type,Fintype.sum_sum_type,Extraction.krausApply,Extraction.productKraus]

theorem productJoinedKraus_right (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ)
    (C : κ' → Matrix ο α' ℂ) (D : τ' → Matrix ο β' ℂ) (X : Matrix (α'×β') (α'×β') ℂ) :
    Extraction.krausApply (Extraction.productKraus (joinedKraus A C) (joinedKraus B D))
      (bipartiteRight*X*bipartiteRightᴴ)=Extraction.krausApply (Extraction.productKraus C D) X := by
  rw [krausApply_encoded_rect]
  unfold Extraction.productKraus bipartiteRight
  simp_rw [←Matrix.mul_kronecker_mul,joinedKraus_mul_right]
  simp [Fintype.sum_prod_type,Fintype.sum_sum_type,Extraction.krausApply,Extraction.productKraus]

theorem productJoinedKraus_left_right (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ)
    (C : κ' → Matrix ο α' ℂ) (D : τ' → Matrix ο β' ℂ) (X : Matrix (α×β) (α'×β') ℂ) :
    Extraction.krausApply (Extraction.productKraus (joinedKraus A C) (joinedKraus B D))
      (bipartiteLeft*X*bipartiteRightᴴ)=0 := by
  rw [krausApply_encoded_rect]
  unfold Extraction.productKraus bipartiteLeft bipartiteRight
  simp_rw [←Matrix.mul_kronecker_mul,joinedKraus_mul_left,joinedKraus_mul_right]
  simp [Fintype.sum_prod_type,Fintype.sum_sum_type]

theorem productJoinedKraus_right_left (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ)
    (C : κ' → Matrix ο α' ℂ) (D : τ' → Matrix ο β' ℂ) (X : Matrix (α'×β') (α×β) ℂ) :
    Extraction.krausApply (Extraction.productKraus (joinedKraus A C) (joinedKraus B D))
      (bipartiteRight*X*bipartiteLeftᴴ)=0 := by
  rw [krausApply_encoded_rect]
  unfold Extraction.productKraus bipartiteLeft bipartiteRight
  simp_rw [←Matrix.mul_kronecker_mul,joinedKraus_mul_left,joinedKraus_mul_right]
  simp [Fintype.sum_prod_type,Fintype.sum_sum_type]

end
end OperationalCompletion
