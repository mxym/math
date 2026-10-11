import APPTReview.SortedWitness
import Mathlib.Data.Finset.Sort

open scoped BigOperators
open Matrix
namespace APPTReview

abbrev UpperPair (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}
abbrev SquareSlot (m : ℕ) := Fin m ⊕ (UpperPair m ⊕ UpperPair m)

def squareSlotCoord {m : ℕ} : SquareSlot m → Fin m × Fin m
  | .inl i => (i,i)
  | .inr (.inl p) => p.val
  | .inr (.inr p) => p.val.swap

theorem squareSlotCoord_injective {m : ℕ} :
    Function.Injective (squareSlotCoord (m:=m)) := by
  intro x y hxy
  rcases x with i | ⟨⟨i,j⟩,hij⟩ | ⟨⟨i,j⟩,hij⟩ <;>
    rcases y with k | ⟨⟨k,l⟩,hkl⟩ | ⟨⟨k,l⟩,hkl⟩ <;>
    dsimp only [squareSlotCoord, Prod.swap] at hxy <;>
    simp only [Prod.mk.injEq] at hxy <;>
    rcases hxy with ⟨h1,h2⟩ <;> subst_vars <;> simp_all <;> (dsimp at *; omega)

theorem squareSlotCoord_surjective {m : ℕ} :
    Function.Surjective (squareSlotCoord (m:=m)) := by
  intro ⟨i,j⟩
  rcases lt_trichotomy i j with h | h | h
  · exact ⟨.inr (.inl ⟨(i,j),h⟩),rfl⟩
  · subst j; exact ⟨.inl i,rfl⟩
  · exact ⟨.inr (.inr ⟨(j,i),h⟩),rfl⟩

noncomputable def squareSlotEquiv (m : ℕ) : SquareSlot m ≃ Fin m × Fin m :=
  Equiv.ofBijective squareSlotCoord ⟨squareSlotCoord_injective,squareSlotCoord_surjective⟩

theorem upperPair_card (m : ℕ) : 2*Fintype.card (UpperPair m)+m=m*m := by
  have h := Fintype.card_congr (squareSlotEquiv m)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at h
  omega

def squareSlotLabel {m D : ℕ}
    (hD : 2*Fintype.card (UpperPair m)+m ≤ D)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m))) : SquareSlot m → Fin D
  | .inl i => ⟨D-1-Fintype.card (UpperPair m)-i.val, by have hi := i.isLt; omega⟩
  | .inr (.inl e) => ⟨D-1-(r e).val, by have he := (r e).isLt; omega⟩
  | .inr (.inr e) => ⟨(r e).val, by have he := (r e).isLt; omega⟩

theorem squareSlotLabel_injective {m D : ℕ}
    (hD : 2*Fintype.card (UpperPair m)+m ≤ D)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m))) :
    Function.Injective (squareSlotLabel hD r) := by
  intro x y hxy
  have hv := congrArg Fin.val hxy
  rcases x with i | e | e <;> rcases y with j | f | f
  all_goals simp only [squareSlotLabel] at hv
  · congr 1; apply Fin.ext; omega
  · have hj := (r f).isLt; omega
  · have hj := (r f).isLt; omega
  · have hi := (r e).isLt; omega
  · congr 2; apply r.injective; apply Fin.ext; have hi := (r e).isLt; have hj := (r f).isLt; omega
  · have hi := (r e).isLt; have hj := (r f).isLt; omega
  · have hi := (r e).isLt; omega
  · have hi := (r e).isLt; have hj := (r f).isLt; omega
  · congr 2; apply r.injective; exact Fin.ext hv

end APPTReview
