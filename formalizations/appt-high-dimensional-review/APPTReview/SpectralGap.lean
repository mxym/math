import APPTReview.GraphEnergy
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

theorem row_energy_eq_pair_sum {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) :
    (∑ i, rowEnergy G i) = ∑ p : UpperPair m, (G p.val.1 p.val.2)^2 := by
  simp_rw [rowEnergy_eq_sum]
  change (∑ i : Fin m, ∑ j : Fin m, if i<j then (G i j)^2 else 0) = _
  rw [← Fintype.sum_prod_type (fun p : Fin m × Fin m => if p.1<p.2 then (G p.1 p.2)^2 else 0)]
  let s := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1<p.2)
  calc
    _ = ∑ p ∈ s, (G p.1 p.2)^2 := by simp only [s, Finset.sum_filter]
    _ = _ := Finset.sum_subtype s (by intro p; simp [s]) _

theorem gapPrefixBound {m n : ℕ} (hmn : m≤n) :
    Fintype.card (UpperPair m) ≤ Fintype.card (Fin m × Fin n) := by
  have h := pairPlacementBound hmn
  omega

def sortedGap {D R : ℕ} (hR : R≤D) (lam : Fin D → ℝ) (i : Fin R) : ℝ :=
  lam (Fin.castLE hR i)-lam (Fin.rev (Fin.castLE hR i))

theorem placed_gap_eq_sortedGap {m n : ℕ} (hmn : m≤n)
    (r : UpperPair m ≃ Fin (Fintype.card (UpperPair m)))
    (lam : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (p : UpperPair m) :
    gapMatrix (placedSpectrum hmn r lam) p.val.1 p.val.2 =
      sortedGap (gapPrefixBound hmn) lam (r p) := by
  rw [placed_gap_pair]
  unfold sortedGap
  have ht : squareSlotLabel (pairPlacementBound hmn) r (.inr (.inr p)) =
      Fin.castLE (gapPrefixBound hmn) (r p) := by apply Fin.ext; rfl
  have hb : squareSlotLabel (pairPlacementBound hmn) r (.inr (.inl p)) =
      Fin.rev (Fin.castLE (gapPrefixBound hmn) (r p)) := by
    apply Fin.ext
    dsimp only [squareSlotLabel, Fin.rev, Fin.castLE]
    omega
  rw [ht,hb]

theorem upperPair_card_formula (m : ℕ) :
    Fintype.card (UpperPair m) = m*(m-1)/2 := by
  cases m with
  | zero => have h := upperPair_card 0; omega
  | succ k =>
    have h := upperPair_card (k+1)
    have he : 2*Fintype.card (UpperPair (k+1))=(k+1)*k := by nlinarith
    change Fintype.card (UpperPair (k+1))=(k+1)*k/2
    omega

theorem pairedPivot_paper_index {m n : ℕ} (hm : 0<m) (hmn : m≤n) :
    (pairedPivot hm hmn).val = Fintype.card (Fin m × Fin n)-m*(m+1)/2 := by
  have hc := upperPair_card m
  have he : 2*(Fintype.card (UpperPair m)+m)=m*(m+1) := by nlinarith
  have hdiv : m*(m+1)/2=Fintype.card (UpperPair m)+m := by omega
  simp only [pairedPivot, hdiv, Nat.sub_sub]

theorem density_pairedPivot_positive {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    0 < hρ.1.isHermitian.eigenvalues₀ (pairedPivot (by omega) hmn) := by
  have hfour : 4≤Fintype.card (Fin (h+1) × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
  have hr : 3≤Fintype.card (UpperPair (h+1))+(h+1) := by
    have hc := upperPair_card (h+1)
    nlinarith
  exact ordered_pivot_positive hfour hρ.1.isHermitian.eigenvalues₀
    hρ.1.isHermitian.eigenvalues₀_antitone
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear (by omega) hmn hρ.1.isHermitian happt hfour)
    (pairedPivot (by omega) hmn) (by dsimp [pairedPivot]; omega)

/-- A dimension-uniform square budget for the actual paired APPT eigenvalues. -/
theorem density_appt_pair_gap_square_sum {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    (∑ i : Fin (Fintype.card (UpperPair (h+1))),
      (sortedGap (gapPrefixBound hmn) hρ.1.isHermitian.eigenvalues₀ i)^2) ≤
      8*(hρ.1.isHermitian.eigenvalues₀ (pairedPivot (by omega) hmn))^2 := by
  let lam := hρ.1.isHermitian.eigenvalues₀
  let b := lam (pairedPivot (by omega) hmn)
  let d := placedSpectrum hmn (rowRank (h+1)) lam
  have hanti : Antitone lam := hρ.1.isHermitian.eigenvalues₀_antitone
  have hb : 0<b := density_pairedPivot_positive hh hmn hρ happt
  have hw := appt_all_ordered_pair_witnesses hmn hρ.1.isHermitian happt (rowRank (h+1))
  have hn := gapMatrix_nonneg d (placedSpectrum_order hmn (rowRank (h+1)) lam hanti)
  have hp := witness_gap_psd_bound d b hw
    (placedSpectrum_diagonal_le (by omega) hmn (rowRank (h+1)) lam hanti)
  have hg := ordered_graph_energy_bound (gapMatrix d) (2*b) (by positivity)
    (gapMatrix_hermitian d hw) hn (gapMatrix_diag d)
    (placed_gap_rowMajor hmn lam hanti) hp
  rw [row_energy_eq_pair_sum] at hg
  dsimp only [d] at hg
  simp_rw [placed_gap_eq_sortedGap] at hg
  rw [(rowRank (h+1)).sum_comp (fun i => (sortedGap (gapPrefixBound hmn) lam i)^2)] at hg
  change (∑ i, (sortedGap (gapPrefixBound hmn) lam i)^2) ≤ 8*b^2
  nlinarith

end APPTReview
