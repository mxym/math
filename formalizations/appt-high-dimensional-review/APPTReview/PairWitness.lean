import APPTReview.PairSlots
import APPTReview.GraphBounds

open scoped BigOperators
open Matrix
namespace APPTReview

theorem pairPlacementBound {m n : ℕ} (hmn : m ≤ n) :
    2*Fintype.card (UpperPair m)+m ≤ Fintype.card (Fin m × Fin n) := by
  rw [upperPair_card]
  simpa using Nat.mul_le_mul_left m hmn

noncomputable def placedSpectrum {m n : ℕ} (hmn : m ≤ n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) : Fin m × Fin m → ℝ :=
  fun p => lam (squareSlotLabel (pairPlacementBound hmn) r ((squareSlotEquiv m).symm p))

@[simp] theorem placedSpectrum_slot {m n : ℕ} (hmn : m ≤ n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (s : SquareSlot m) :
    placedSpectrum hmn r lam (squareSlotCoord s) =
      lam (squareSlotLabel (pairPlacementBound hmn) r s) := by
  change lam (squareSlotLabel _ r ((squareSlotEquiv m).symm ((squareSlotEquiv m) s))) = _
  rw [Equiv.symm_apply_apply]

/-- Every edge arrangement is obtained by one actual global unitary. -/
theorem appt_all_ordered_pair_witnesses {m n : ℕ} (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A.IsHermitian) (happt : APPT.Quantum.AbsolutelyPPT A)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m))) :
    (witnessMatrix (placedSpectrum hmn r hA.eigenvalues₀)).PosSemidef := by
  classical
  let e : Fin m → Fin n := Fin.castLE hmn
  have he : Function.Injective e := by intro a b h; exact Fin.ext (congrArg (fun z : Fin n => z.val) h)
  let emb : Fin m × Fin m → Fin m × Fin n := fun p => (p.1,e p.2)
  have hemb : Function.Injective emb := by
    intro a b h
    exact Prod.ext (congrArg (fun z : Fin m × Fin n => z.1) h) (he (congrArg (fun z : Fin m × Fin n => z.2) h))
  let f : SquareSlot m → Fin m × Fin n := fun s => emb (squareSlotCoord s)
  let g : SquareSlot m → Fin m × Fin n :=
    fun s => spectralLabel _ (squareSlotLabel (pairPlacementBound hmn) r s)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g
    (hemb.comp squareSlotCoord_injective)
    ((spectralLabel _).injective.comp (squareSlotLabel_injective _ r))
  have hd : (fun p : Fin m × Fin m => hA.eigenvalues (σ (emb p))) =
      placedSpectrum hmn r hA.eigenvalues₀ := by
    funext p
    obtain ⟨s,rfl⟩ := squareSlotCoord_surjective p
    change hA.eigenvalues (σ (f s)) = _
    rw [hσ, placedSpectrum_slot]
    exact eigenvalues_spectralLabel hA _
  have hp := appt_eigenvalue_witness_posSemidef hA happt σ e he
  change (witnessMatrix (fun p : Fin m × Fin m => hA.eigenvalues (σ (emb p)))).PosSemidef at hp
  rwa [hd] at hp

end APPTReview
