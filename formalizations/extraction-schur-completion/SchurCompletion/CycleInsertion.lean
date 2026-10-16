import SchurCompletion.JointCycleSpectrum
import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

abbrev FixedWords (t k : ℕ) (σ : Equiv.Perm (Fin k)) :=
  {w : Word t k // ∀ j, w (σ j) = w j}

def fixedWordsEquivFixedPoints (t k : ℕ) (σ : Equiv.Perm (Fin k)) :
    FixedWords t k σ ≃ Function.fixedPoints (positionWordEquiv t k σ) where
  toFun w := ⟨w.val,funext w.property⟩
  invFun w := ⟨w.val,fun j => congrFun w.property j⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixedWords_card (t k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Fintype.card (FixedWords t k σ) = t^positionCycleCount k σ := by
  rw [Fintype.card_congr (fixedWordsEquivFixedPoints t k σ),Set.fintypeCard_eq_ncard]
  exact fixedWordCard_eq_pow_cycleCount t k σ

def fixedWords_insert_zero (t k : ℕ) (σ : Equiv.Perm (Fin k)) :
    FixedWords t (k+1) (Equiv.Perm.decomposeFin.symm (0,σ)) ≃ Fin t × FixedWords t k σ where
  toFun w := (w.val 0,⟨fun j => w.val j.succ,by
    intro j
    have h := w.property j.succ
    simpa only [Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,Equiv.refl_apply] using h⟩)
  invFun u := ⟨Fin.cases u.1 u.2.val,by
    intro j
    induction j using Fin.cases with
    | zero => simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
    | succ j =>
      simpa only [Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,Equiv.refl_apply,
        Fin.cases_succ] using u.2.property j⟩
  left_inv w := by
    apply Subtype.ext
    apply funext
    intro j
    induction j using Fin.cases <;> rfl
  right_inv u := by rfl

def fixedWords_insert_succ (t k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    FixedWords t (k+1) (Equiv.Perm.decomposeFin.symm (i.succ,σ)) ≃ FixedWords t k σ where
  toFun w := ⟨fun j => w.val j.succ,by
    intro j
    have h0 := w.property 0
    rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
    have hj := w.property j.succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ] at hj
    by_cases hσ : σ j = i
    · simp only [hσ,Equiv.swap_apply_right] at hj
      exact (congrArg w.val (congrArg Fin.succ hσ)).trans (h0.trans hj)
    · have hn : (σ j).succ ≠ i.succ := fun h => hσ (Fin.succ_injective _ h)
      simpa only [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hn] using hj⟩
  invFun w := ⟨Fin.cases (w.val i) w.val,by
    intro j
    induction j using Fin.cases with
    | zero => simp only [Equiv.Perm.decomposeFin_symm_apply_zero,Fin.cases_succ,Fin.cases_zero]
    | succ j =>
      rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      by_cases hσ : σ j = i
      · simpa only [hσ,Equiv.swap_apply_right,Fin.cases_zero,Fin.cases_succ] using w.property j
      · have hn : (σ j).succ ≠ i.succ := fun h => hσ (Fin.succ_injective _ h)
        simpa only [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hn,Fin.cases_succ]
          using w.property j⟩
  left_inv w := by
    apply Subtype.ext
    apply funext
    intro j
    induction j using Fin.cases with
    | zero =>
      have h := w.property 0
      simpa only [Equiv.Perm.decomposeFin_symm_apply_zero,Fin.cases_zero] using h
    | succ j => rfl
  right_inv _ := rfl

/-- Adjoining a fixed position creates one free letter. This character recursion
 is derived by an actual fixed-word equivalence, including t=0 and k=0. -/
theorem cycleCharacter_insert_zero (t k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (t : ℂ)^positionCycleCount (k+1) (Equiv.Perm.decomposeFin.symm (0,σ)) =
      (t : ℂ)*(t : ℂ)^positionCycleCount k σ := by
  have h := Fintype.card_congr (fixedWords_insert_zero t k σ)
  rw [fixedWords_card,Fintype.card_prod,Fintype.card_fin,fixedWords_card] at h
  exact_mod_cast h

/-- Inserting a new position into an existing cycle leaves the character
 power unchanged. No statement about abstract cycle counts is assumed. -/
theorem cycleCharacter_insert_succ (t k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (t : ℂ)^positionCycleCount (k+1) (Equiv.Perm.decomposeFin.symm (i.succ,σ)) =
      (t : ℂ)^positionCycleCount k σ := by
  have h := Fintype.card_congr (fixedWords_insert_succ t k σ i)
  rw [fixedWords_card,fixedWords_card] at h
  exact_mod_cast h

end
end ExtractionSchur
