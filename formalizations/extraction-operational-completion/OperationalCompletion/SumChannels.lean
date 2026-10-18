import SpectralProtocol.WeightedBlocks

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace OperationalCompletion
noncomputable section

variable {α β ο κ τ : Type*}
  [Fintype α] [Fintype β] [Fintype ο] [Fintype κ] [Fintype τ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ο]

def sumLeft : Matrix (α⊕β) α ℂ :=
  Extraction.coordinateIsometry ⟨Sum.inl,Sum.inl_injective⟩

def sumRight : Matrix (α⊕β) β ℂ :=
  Extraction.coordinateIsometry ⟨Sum.inr,Sum.inr_injective⟩

def joinedKraus (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ) :
    κ⊕τ → Matrix ο (α⊕β) ℂ
  | Sum.inl t => fun o x => x.elim (A t o) (fun _ => 0)
  | Sum.inr t => fun o x => x.elim (fun _ => 0) (B t o)

theorem joinedKraus_complete (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ)
    (hA : ∑ t,(A t)ᴴ*A t=1) (hB : ∑ t,(B t)ᴴ*B t=1) :
    ∑ t,(joinedKraus A B t)ᴴ*joinedKraus A B t=1 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · have h := congrArg (fun M : Matrix α α ℂ => M x y) hA
    simpa [joinedKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,Matrix.one_apply] using h
  · simp [joinedKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,Matrix.one_apply]
  · simp [joinedKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,Matrix.one_apply]
  · have h := congrArg (fun M : Matrix β β ℂ => M x y) hB
    simpa [joinedKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,Matrix.one_apply] using h

theorem joinedKraus_mul_left (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ) (t : κ⊕τ) :
    joinedKraus A B t*sumLeft= t.elim A (fun _ => 0) := by
  ext o x
  change (∑ y,joinedKraus A B t o y*(if y=Sum.inl x then (1:ℂ) else 0))=_
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  cases t <;> rfl

theorem joinedKraus_mul_right (A : κ → Matrix ο α ℂ) (B : τ → Matrix ο β ℂ) (t : κ⊕τ) :
    joinedKraus A B t*sumRight= t.elim (fun _ => 0) B := by
  ext o x
  change (∑ y,joinedKraus A B t o y*(if y=Sum.inr x then (1:ℂ) else 0))=_
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  cases t <;> rfl

theorem sumLeft_isometry : (sumLeft (α:=α) (β:=β))ᴴ*sumLeft (α:=α) (β:=β)=1 :=
  Extraction.coordinateIsometry_isometry _

theorem sumRight_isometry : (sumRight (α:=α) (β:=β))ᴴ*sumRight (α:=α) (β:=β)=1 :=
  Extraction.coordinateIsometry_isometry _

theorem sumLeft_right_cross : (sumLeft (α:=α) (β:=β))ᴴ*sumRight (α:=α) (β:=β)=0 := by
  ext x y
  simp [sumLeft,sumRight,Extraction.coordinateIsometry,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_sum_type]

theorem sumRight_left_cross : (sumRight (α:=α) (β:=β))ᴴ*sumLeft (α:=α) (β:=β)=0 := by
  have h := congrArg Matrix.conjTranspose (sumLeft_right_cross (α:=α) (β:=β))
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using h

variable {ι η ζ ξ : Type*} [Fintype ι] [Fintype η] [Fintype ζ] [Fintype ξ]
  [DecidableEq ι] [DecidableEq η] [DecidableEq ζ]

theorem krausApply_encoded_rect (C : ξ → Matrix ο ι ℂ) (E : Matrix ι η ℂ)
    (F : Matrix ι ζ ℂ) (X : Matrix η ζ ℂ) :
    Extraction.krausApply C (E*X*Fᴴ)=∑ t,(C t*E)*X*(C t*F)ᴴ := by
  simp only [Extraction.krausApply,Matrix.conjTranspose_mul,Matrix.mul_assoc]

end
end OperationalCompletion
