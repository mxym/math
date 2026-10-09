import CofactorCrossCardinality
import CofactorContractionSquare

/-! Every two-block permutation can be corrected by a block-preserving
permutation to a partial swap. Its coefficient on a block-symmetric product
is therefore nonnegative. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {S T C V W : Type*} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype C] [DecidableEq C]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
noncomputable section

def crossSlotsEquiv (σ : Equiv.Perm (S ⊕ T)) :
    {s : S // crossLeft σ s} ≃ {t : T // crossRight σ t} :=
  Fintype.equivOfCardEq (cross_card_eq σ)

def leftSlotsEquiv (σ : Equiv.Perm (S ⊕ T)) :
    ({s : S // ¬crossLeft σ s} ⊕ {s : S // crossLeft σ s}) ≃ S :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl (crossLeft σ))

def rightSlotsEquiv (σ : Equiv.Perm (S ⊕ T)) :
    ({t : T // ¬crossRight σ t} ⊕ {s : S // crossLeft σ s}) ≃ T :=
  ((Equiv.refl _).sumCongr (crossSlotsEquiv σ)).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl (crossRight σ)))

def allSlotsEquiv (σ : Equiv.Perm (S ⊕ T)) :
    (({s : S // ¬crossLeft σ s} ⊕ {s : S // crossLeft σ s}) ⊕
      ({t : T // ¬crossRight σ t} ⊕ {s : S // crossLeft σ s})) ≃ (S ⊕ T) :=
  (leftSlotsEquiv σ).sumCongr (rightSlotsEquiv σ)

def crossSwap (σ : Equiv.Perm (S ⊕ T)) : Equiv.Perm (S ⊕ T) :=
  (allSlotsEquiv σ).symm.trans (partialSwap.trans (allSlotsEquiv σ))

theorem crossSwap_same_block (σ : Equiv.Perm (S ⊕ T)) (x : S ⊕ T) :
    (crossSwap σ x).isLeft = (σ x).isLeft := by
  obtain ⟨y,rfl⟩ := (allSlotsEquiv σ).surjective x
  change ((allSlotsEquiv σ) (partialSwap ((allSlotsEquiv σ).symm (allSlotsEquiv σ y)))).isLeft = _
  rw [Equiv.symm_apply_apply]
  rcases y with (a|j)|(b|j)
  · have h := a.property
    simp only [allSlotsEquiv, leftSlotsEquiv, rightSlotsEquiv, partialSwap,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.trans_apply,
      Equiv.sumComm_apply, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    cases hx : σ (Sum.inl a.val) <;> simp_all [crossLeft]
  · have h := j.property
    simp only [allSlotsEquiv, leftSlotsEquiv, rightSlotsEquiv, partialSwap,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.trans_apply,
      Equiv.sumComm_apply, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    cases hx : σ (Sum.inl j.val) <;> simp_all [crossLeft]
  · have h := b.property
    simp only [allSlotsEquiv, leftSlotsEquiv, rightSlotsEquiv, partialSwap,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.trans_apply,
      Equiv.sumComm_apply, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    cases hx : σ (Sum.inr b.val) <;> simp_all [crossRight]
  · have h := (crossSlotsEquiv σ j).property
    simp only [allSlotsEquiv, leftSlotsEquiv, rightSlotsEquiv, partialSwap,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.trans_apply,
      Equiv.sumComm_apply, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    cases hx : σ (Sum.inr (crossSlotsEquiv σ j).val) <;> simp_all [crossRight]

theorem arrayCoefficient_transport (p : (W → C) → ℂ) (e : V ≃ W) (σ : Equiv.Perm V) :
    arrayCoefficient p (e.symm.trans (σ.trans e)) =
      arrayCoefficient (fun f => p (f ∘ e.symm)) σ := by
  unfold arrayCoefficient arrayPair
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl C))
  intro f
  congr 1
  · congr 1
    funext i
    simp

theorem arrayCoefficient_postcompose (p : (V → C) → ℂ) (σ τ : Equiv.Perm V)
    (h : ∀ f, p (f ∘ τ.symm) = p f) :
    arrayCoefficient p (σ.trans τ) = arrayCoefficient p σ := by
  unfold arrayCoefficient arrayPair
  apply Finset.sum_congr rfl
  intro f _
  change p f * star (p ((f ∘ σ.symm) ∘ τ.symm)) = _
  rw [h]

theorem crossSwap_coefficient_nonneg (u : (S → C) → ℂ) (v : (T → C) → ℂ)
    (σ : Equiv.Perm (S ⊕ T)) : 0 ≤ arrayCoefficient (blockArray u v) (crossSwap σ) := by
  unfold crossSwap
  rw [arrayCoefficient_transport]
  have hp : (fun f => blockArray u v (f ∘ (allSlotsEquiv σ).symm)) =
      blockArray (fun f => u (f ∘ (leftSlotsEquiv σ).symm))
        (fun f => v (f ∘ (rightSlotsEquiv σ).symm)) := by
    funext f
    rfl
  rw [hp]
  exact partialSwap_coefficient_nonneg _ _

theorem symmetricBlock_coefficient_nonneg (u : (S → C) → ℂ) (v : (T → C) → ℂ)
    (σ : Equiv.Perm (S ⊕ T)) :
    0 ≤ arrayCoefficient (blockArray (symmetrizeArray u) (symmetrizeArray v)) σ := by
  let τ := σ.symm.trans (crossSwap σ)
  have hτ : ∀ x, (τ x).isLeft = x.isLeft := by
    intro x
    change (crossSwap σ (σ.symm x)).isLeft = x.isLeft
    rw [crossSwap_same_block, Equiv.apply_symm_apply]
  obtain ⟨a,b,hab⟩ := block_preserving_decomposition τ hτ
  have hc : σ.trans τ = crossSwap σ := by ext x; simp [τ]
  have hp : ∀ f, blockArray (symmetrizeArray u) (symmetrizeArray v) (f ∘ τ.symm) =
      blockArray (symmetrizeArray u) (symmetrizeArray v) f := by
    intro f
    rw [hab]
    exact blockArray_invariant u v a.symm b.symm f
  have he := arrayCoefficient_postcompose
    (blockArray (symmetrizeArray u) (symmetrizeArray v)) σ τ hp
  rw [hc] at he
  rw [← he]
  exact crossSwap_coefficient_nonneg _ _ σ

end
end CofactorSpectral
