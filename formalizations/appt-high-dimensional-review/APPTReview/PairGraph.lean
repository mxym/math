import APPTReview.PairWitness
open scoped BigOperators
open Matrix
namespace APPTReview
variable {m : ℕ}

def gapMatrix (d : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => 2*d (i,i))-witnessMatrix d

@[simp] theorem gapMatrix_diag (d : Fin m × Fin m → ℝ) (i : Fin m) :
    gapMatrix d i i = 0 := by simp [gapMatrix, witnessMatrix]

theorem gapMatrix_upper (d : Fin m × Fin m → ℝ) (i j : Fin m) (h : i<j) :
    gapMatrix d i j = d (j,i)-d (i,j) := by
  simp [gapMatrix, witnessMatrix, ne_of_lt h, h]

theorem gapMatrix_nonneg (d : Fin m × Fin m → ℝ)
    (ho : ∀ i j, i<j → d (i,j) ≤ d (j,i)) : ∀ i j, 0 ≤ gapMatrix d i j := by
  intro i j
  by_cases hij : i=j
  · subst j; simp
  · by_cases hi : i<j
    · rw [gapMatrix_upper d i j hi]; exact sub_nonneg.mpr (ho i j hi)
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hij)
      simpa [gapMatrix, witnessMatrix, hij, hi] using sub_nonneg.mpr (ho j i hj)

theorem gapMatrix_hermitian (d : Fin m × Fin m → ℝ)
    (hM : (witnessMatrix d).PosSemidef) : (gapMatrix d).IsHermitian :=
  (Matrix.isHermitian_diagonal _).sub hM.isHermitian

theorem witness_gap_psd_bound (d : Fin m × Fin m → ℝ) (b : ℝ)
    (hM : (witnessMatrix d).PosSemidef) (hd : ∀ i, d (i,i) ≤ b) :
    ((2*b) • (1 : Matrix (Fin m) (Fin m) ℝ)-gapMatrix d).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => 2*(b-d (i,i)))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by have hi := hd i; dsimp; linarith)
  convert hM.add hp using 1
  ext i j
  by_cases hij : i=j <;> simp [gapMatrix, Matrix.diagonal_apply, Matrix.one_apply, hij] <;> ring

def pairedPivot {m n : ℕ} (hm : 0<m) (hmn : m≤n) :
    Fin (Fintype.card (Fin m × Fin n)) :=
  ⟨Fintype.card (Fin m × Fin n)-Fintype.card (UpperPair m)-m,
    by have hd := pairPlacementBound hmn; omega⟩

theorem placedSpectrum_diagonal_le {m n : ℕ} (hm : 0<m) (hmn : m≤n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (hanti : Antitone lam)
    (i : Fin m) : placedSpectrum hmn r lam (i,i) ≤ lam (pairedPivot hm hmn) := by
  change placedSpectrum hmn r lam (squareSlotCoord (.inl i)) ≤ _
  rw [placedSpectrum_slot]
  apply hanti
  change Fintype.card (Fin m × Fin n)-Fintype.card (UpperPair m)-m ≤
    Fintype.card (Fin m × Fin n)-1-Fintype.card (UpperPair m)-i.val
  have hd := pairPlacementBound hmn
  omega

theorem placedSpectrum_order {m n : ℕ} (hmn : m≤n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (hanti : Antitone lam)
    (i j : Fin m) (hij : i<j) :
    placedSpectrum hmn r lam (i,j) ≤ placedSpectrum hmn r lam (j,i) := by
  let e : UpperPair m := ⟨(i,j),hij⟩
  change placedSpectrum hmn r lam (squareSlotCoord (.inr (.inl e))) ≤
    placedSpectrum hmn r lam (squareSlotCoord (.inr (.inr e)))
  rw [placedSpectrum_slot, placedSpectrum_slot]
  apply hanti
  change (r e).val ≤ Fintype.card (Fin m × Fin n)-1-(r e).val
  have hd := pairPlacementBound hmn
  have he := (r e).isLt
  omega

/-- All graph rearrangements of an actual sorted APPT spectrum obey the squared bound. -/
theorem appt_ordered_gap_square_bound {m n : ℕ} (hm : 0<m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A.IsHermitian) (happt : APPT.Quantum.AbsolutelyPPT A)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m))) (x : Fin m → ℝ) :
    (∑ i, (gapMatrix (placedSpectrum hmn r hA.eigenvalues₀) *ᵥ x) i ^ 2) ≤
      4*(hA.eigenvalues₀ (pairedPivot hm hmn))^2 * ∑ i, x i ^ 2 := by
  have hw := appt_all_ordered_pair_witnesses hmn hA happt r
  have hn := gapMatrix_nonneg _ (placedSpectrum_order hmn r _ hA.eigenvalues₀_antitone)
  have hb := witness_gap_psd_bound _ (hA.eigenvalues₀ (pairedPivot hm hmn)) hw
    (placedSpectrum_diagonal_le hm hmn r _ hA.eigenvalues₀_antitone)
  have hs := nonnegative_matrix_square_bound _ _ (gapMatrix_hermitian _ hw) hn hb x
  nlinarith

end APPTReview
