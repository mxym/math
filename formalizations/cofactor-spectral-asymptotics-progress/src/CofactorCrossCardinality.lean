import CofactorTensorArrays

/-! Conservation of cross-block slots and decomposition of block-preserving permutations. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
noncomputable section

def leftSubtypeEquiv : {x : S ⊕ T // x.isLeft} ≃ S where
  toFun x := x.val.getLeft x.property
  invFun s := ⟨Sum.inl s, rfl⟩
  left_inv x := by rcases x with ⟨s|t,h⟩ <;> simp_all
  right_inv _ := rfl

def rightSubtypeEquiv : {x : S ⊕ T // x.isRight} ≃ T where
  toFun x := x.val.getRight x.property
  invFun t := ⟨Sum.inr t, rfl⟩
  left_inv x := by rcases x with ⟨s|t,h⟩ <;> simp_all
  right_inv _ := rfl

abbrev crossLeft (σ : Equiv.Perm (S ⊕ T)) (s : S) : Prop := (σ (Sum.inl s)).isRight
abbrev crossRight (σ : Equiv.Perm (S ⊕ T)) (t : T) : Prop := (σ (Sum.inr t)).isLeft

theorem inl_getLeft (x : S ⊕ T) (h : x.isLeft) : Sum.inl (x.getLeft h) = x := by
  cases x <;> simp_all

theorem inr_getRight (x : S ⊕ T) (h : x.isRight) : Sum.inr (x.getRight h) = x := by
  cases x <;> simp_all

theorem cross_card_eq (σ : Equiv.Perm (S ⊕ T)) :
    Fintype.card {s : S // crossLeft σ s} = Fintype.card {t : T // crossRight σ t} := by
  let P : S ⊕ T → Prop := fun x => (σ x).isLeft
  let e : {x : S ⊕ T // P x} ≃ {x : S ⊕ T // x.isLeft} :=
    σ.subtypeEquiv (fun _ => Iff.rfl)
  have h1 := Fintype.card_congr (e.trans leftSubtypeEquiv)
  have h2 := Fintype.card_congr (Equiv.subtypeSum (p := P))
  rw [Fintype.card_sum] at h2
  have h3 := Fintype.card_congr (Equiv.sumCompl (fun s : S => P (Sum.inl s)))
  rw [Fintype.card_sum] at h3
  let ec : {s : S // crossLeft σ s} ≃ {s : S // ¬ P (Sum.inl s)} :=
    Equiv.subtypeEquivRight (fun s => by
      unfold crossLeft P
      cases σ (Sum.inl s) <;> simp)
  have h4 := Fintype.card_congr ec
  change Fintype.card {s : S // crossLeft σ s} =
    Fintype.card {t : T // P (Sum.inr t)}
  omega

theorem block_preserving_decomposition (σ : Equiv.Perm (S ⊕ T))
    (hσ : ∀ x, (σ x).isLeft = x.isLeft) :
    ∃ a : Equiv.Perm S, ∃ b : Equiv.Perm T, σ = a.sumCongr b := by
  have hr : ∀ x, (σ x).isRight = x.isRight := by
    intro x
    have h := hσ x
    rcases x with s|t
    · cases he : σ (Sum.inl s) <;> simp_all
    · cases he : σ (Sum.inr t) <;> simp_all
  let el : {x : S ⊕ T // x.isLeft} ≃ {x : S ⊕ T // x.isLeft} :=
    σ.subtypeEquiv (fun x => by rw [hσ x])
  let er : {x : S ⊕ T // x.isRight} ≃ {x : S ⊕ T // x.isRight} :=
    σ.subtypeEquiv (fun x => by rw [hr x])
  let a : Equiv.Perm S := leftSubtypeEquiv.symm.trans (el.trans leftSubtypeEquiv)
  let b : Equiv.Perm T := rightSubtypeEquiv.symm.trans (er.trans rightSubtypeEquiv)
  refine ⟨a,b,?_⟩
  ext x
  rcases x with s|t
  · change σ (Sum.inl s) = Sum.inl ((σ (Sum.inl s)).getLeft _)
    exact (inl_getLeft _ _).symm
  · change σ (Sum.inr t) = Sum.inr ((σ (Sum.inr t)).getRight _)
    exact (inr_getRight _ _).symm

end
end CofactorSpectral
