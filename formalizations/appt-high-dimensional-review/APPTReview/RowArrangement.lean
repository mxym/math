import APPTReview.TriangleRows
namespace APPTReview

def upperPairCode {m : ℕ} (p : UpperPair m) : ℕ := p.val.1.val*m+p.val.2.val

theorem upperPairCode_injective {m : ℕ} : Function.Injective (upperPairCode (m:=m)) := by
  intro p q hpq
  have hmod := congrArg (fun x : ℕ => x % m) hpq
  have hp := p.val.2.isLt
  have hq := q.val.2.isLt
  simp only [upperPairCode, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
    Nat.zero_mod, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at hmod
  have hmul : p.val.1.val*m=q.val.1.val*m := by dsimp [upperPairCode] at hpq; omega
  have hm : 0<m := lt_of_le_of_lt (Nat.zero_le _) hp
  have he := Nat.eq_of_mul_eq_mul_right hm hmul
  apply Subtype.ext
  exact Prod.ext (Fin.ext he) (Fin.ext hmod)

structure RowPair (m : ℕ) where
  edge : UpperPair m

def rowPairEquiv (m : ℕ) : RowPair m ≃ UpperPair m where
  toFun := RowPair.edge
  invFun := RowPair.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance rowPairFintype (m : ℕ) : Fintype (RowPair m) :=
  Fintype.ofEquiv (UpperPair m) (rowPairEquiv m).symm

instance rowPairOrder (m : ℕ) : LinearOrder (RowPair m) :=
  LinearOrder.lift' (fun p => upperPairCode p.edge)
    (by intro p q h; apply (rowPairEquiv m).injective; exact upperPairCode_injective h)

noncomputable def rowRank (m : ℕ) : UpperPair m ≃ Fin (Fintype.card (UpperPair m)) :=
  (rowPairEquiv m).symm.trans
    (Fintype.orderIsoFinOfCardEq (RowPair m) (Fintype.card_congr (rowPairEquiv m))).symm.toEquiv

theorem rowRank_monotone {m : ℕ} (p q : UpperPair m)
    (hpq : upperPairCode p ≤ upperPairCode q) : rowRank m p ≤ rowRank m q := by
  have h : (RowPair.mk p : RowPair m) ≤ RowPair.mk q := hpq
  exact (Fintype.orderIsoFinOfCardEq (RowPair m) (Fintype.card_congr (rowPairEquiv m))).symm.monotone h

theorem placed_gap_pair {m n : ℕ} (hmn : m≤n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (p : UpperPair m) :
    gapMatrix (placedSpectrum hmn r lam) p.val.1 p.val.2 =
      lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inr p))) -
      lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inl p))) := by
  rw [gapMatrix_upper _ _ _ p.property]
  change placedSpectrum hmn r lam (squareSlotCoord (.inr (.inr p))) -
    placedSpectrum hmn r lam (squareSlotCoord (.inr (.inl p))) = _
  rw [placedSpectrum_slot, placedSpectrum_slot]

theorem placed_gap_antitone_rank {m n : ℕ} (hmn : m≤n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (hf : Antitone lam)
    (p q : UpperPair m) (hr : r p≤r q) :
    gapMatrix (placedSpectrum hmn r lam) q.val.1 q.val.2 ≤
      gapMatrix (placedSpectrum hmn r lam) p.val.1 p.val.2 := by
  rw [placed_gap_pair, placed_gap_pair]
  have ht : lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inr q))) ≤
      lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inr p))) := by
    apply hf
    exact hr
  have hb : lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inl p))) ≤
      lam (squareSlotLabel (pairPlacementBound hmn) r (.inr (.inl q))) := by
    apply hf
    change Fintype.card (Fin m × Fin n)-1-(r q).val ≤ Fintype.card (Fin m × Fin n)-1-(r p).val
    have hr' : (r p).val≤(r q).val := hr
    omega
  linarith

theorem placed_gap_rowMajor {m n : ℕ} (hmn : m≤n)
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (hf : Antitone lam) :
    RowMajorAntitone (gapMatrix (placedSpectrum hmn (rowRank m) lam)) := by
  intro i j k l hij hkl hc
  exact placed_gap_antitone_rank hmn (rowRank m) lam hf
    ⟨(i,j),hij⟩ ⟨(k,l),hkl⟩ (rowRank_monotone _ _ hc)

end APPTReview
