import CofactorGramPSD
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-! Finite coordinate arrays for the two-block symmetrization argument.
These are actual finite functions; their pairings are finite sums. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {V C S T : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
noncomputable section

def assignmentPerm (σ : Equiv.Perm V) : Equiv.Perm (V → C) where
  toFun f := f ∘ σ
  invFun f := f ∘ σ.symm
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

def arrayPair (p q : (V → C) → ℂ) : ℂ := ∑ f, p f * star (q f)

def arrayCoefficient (p : (V → C) → ℂ) (σ : Equiv.Perm V) : ℂ :=
  arrayPair p (fun f => p (f ∘ σ.symm))

def rowTensor (v : V → C → ℂ) (f : V → C) : ℂ := ∏ i, v i (f i)

theorem arrayPair_reindex (p q : (V → C) → ℂ) (σ : Equiv.Perm V) :
    arrayPair (fun f => p (f ∘ σ)) (fun f => q (f ∘ σ)) = arrayPair p q := by
  unfold arrayPair
  apply Fintype.sum_equiv (assignmentPerm (C := C) σ)
  intro f
  rfl

theorem rowTensor_permuted (v : V → C → ℂ) (f : V → C) (σ : Equiv.Perm V) :
    rowTensor v (f ∘ σ.symm) = ∏ i, v (σ i) (f i) := by
  unfold rowTensor
  symm
  apply Fintype.prod_equiv σ
  intro i
  simp

theorem arrayCoefficient_rowTensor (v : V → C → ℂ) (σ : Equiv.Perm V) :
    arrayCoefficient (rowTensor v) σ = ∏ i, complexGram v i (σ i) := by
  unfold arrayCoefficient arrayPair
  simp_rw [rowTensor_permuted, star_prod]
  unfold rowTensor complexGram
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i c => v i c * star (v (σ i) c))).symm

def symmetrizeArray (p : (V → C) → ℂ) (f : V → C) : ℂ :=
  (Fintype.card (Equiv.Perm V) : ℂ)⁻¹ * ∑ σ : Equiv.Perm V, p (f ∘ σ)

theorem symmetrizeArray_invariant (p : (V → C) → ℂ) (σ : Equiv.Perm V) (f : V → C) :
    symmetrizeArray p (f ∘ σ) = symmetrizeArray p f := by
  unfold symmetrizeArray
  congr 1
  let e : Equiv.Perm (Equiv.Perm V) := Equiv.mulLeft σ
  apply Fintype.sum_equiv e
  intro τ
  rfl

def blockArray (u : (S → C) → ℂ) (v : (T → C) → ℂ) (f : S ⊕ T → C) : ℂ :=
  u (f ∘ Sum.inl) * v (f ∘ Sum.inr)

theorem blockArray_invariant (u : (S → C) → ℂ) (v : (T → C) → ℂ)
    (σ : Equiv.Perm S) (τ : Equiv.Perm T) (f : S ⊕ T → C) :
    blockArray (symmetrizeArray u) (symmetrizeArray v) (f ∘ σ.sumCongr τ) =
      blockArray (symmetrizeArray u) (symmetrizeArray v) f := by
  unfold blockArray
  change symmetrizeArray u ((f ∘ Sum.inl) ∘ σ) *
    symmetrizeArray v ((f ∘ Sum.inr) ∘ τ) = _
  rw [symmetrizeArray_invariant, symmetrizeArray_invariant]

theorem blockArray_sum_symmetrized (u : (S → C) → ℂ) (v : (T → C) → ℂ)
    (f : S ⊕ T → C) :
    blockArray (symmetrizeArray u) (symmetrizeArray v) f =
      ((Fintype.card (Equiv.Perm S) * Fintype.card (Equiv.Perm T) : ℕ) : ℂ)⁻¹ *
        ∑ h : Equiv.Perm S × Equiv.Perm T, blockArray u v (f ∘ h.1.sumCongr h.2) := by
  unfold blockArray symmetrizeArray
  rw [Fintype.sum_prod_type]
  simp only [Nat.cast_mul, mul_inv_rev] at *
  simp only [Function.comp_def, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

end
end CofactorSpectral
