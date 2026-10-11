import APPTReview.ResidualGraph
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

theorem sortedGap_antitone {D R : ℕ} (hRD : R≤D)
    (f : Fin D → ℝ) (hf : Antitone f) : Antitone (sortedGap hRD f) := by
  intro i j hij
  have ht := hf (show Fin.castLE hRD i ≤ Fin.castLE hRD j from hij)
  have hb := hf (show (Fin.castLE hRD j).rev ≤ (Fin.castLE hRD i).rev by
    change D-(j.val+1)≤D-(i.val+1)
    have he : i.val≤j.val := hij
    omega)
  exact sub_le_sub ht hb

theorem sortedGap_nonneg {D R : ℕ} (h2R : 2*R≤D)
    (f : Fin D → ℝ) (hf : Antitone f) (i : Fin R) :
    0≤sortedGap (show R≤D by omega) f i := by
  apply sub_nonneg.mpr
  apply hf
  change i.val≤D-(i.val+1)
  have hi := i.isLt
  omega

theorem upperPair_card_pos {h : ℕ} (hh : 1≤h) :
    0<Fintype.card (UpperPair (h+1)) := by
  have hc := upperPair_card (h+1)
  nlinarith

/-- The residual edge sums are exactly sums over the actual sorted paired gaps. -/
theorem residual_pair_sum {m n : ℕ} (hmn : m≤n)
    (f : Fin (Fintype.card (Fin m × Fin n)) → ℝ) (w : ℝ) (F : ℝ → ℝ) :
    (∑ p : UpperPair m,
      F ((gapMatrix (placedSpectrum hmn (rowRank m) f)-w • completeAdjacency :
        Matrix (Fin m) (Fin m) ℝ) p.val.1 p.val.2)) =
      ∑ i, F (sortedGap (gapPrefixBound hmn) f i-w) := by
  have he (p : UpperPair m) :
      (gapMatrix (placedSpectrum hmn (rowRank m) f)-w • completeAdjacency :
        Matrix (Fin m) (Fin m) ℝ) p.val.1 p.val.2 =
      sortedGap (gapPrefixBound hmn) f (rowRank m p)-w := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, completeAdjacency,
      if_neg (ne_of_lt p.property), smul_eq_mul, mul_one, placed_gap_eq_sortedGap]
  simp_rw [he]
  exact (rowRank m).sum_comp (fun i => F (sortedGap (gapPrefixBound hmn) f i-w))

/-- The graph and centering arguments are now connected for the actual APPT spectrum. -/
theorem density_appt_ordered_variance_bound {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    (∑ i, (hρ.1.isHermitian.eigenvalues₀ i)^2)-
      1/(Fintype.card (Fin (h+1) × Fin n) : ℝ) ≤
      max 8 (4+(Fintype.card (Fin (h+1) × Fin n) : ℝ)/(h : ℝ)^2)*
        (hρ.1.isHermitian.eigenvalues₀ (pairedPivot (by omega) hmn))^2 := by
  classical
  let D := Fintype.card (Fin (h+1) × Fin n)
  let R := Fintype.card (UpperPair (h+1))
  have hR : 0<R := upperPair_card_pos hh
  have h2R : 2*R≤D := by have he := pairPlacementBound hmn; dsimp [R,D]; omega
  let f := hρ.1.isHermitian.eigenvalues₀
  have hf : Antitone f := hρ.1.isHermitian.eigenvalues₀_antitone
  let b := f (pairedPivot (by omega) hmn)
  have hb : 0<b := density_pairedPivot_positive hh hmn hρ happt
  let gaps : Fin R → ℝ := sortedGap (gapPrefixBound hmn) f
  let last : Fin R := ⟨R-1,by omega⟩
  let w := gaps last
  have hw : 0≤w := sortedGap_nonneg h2R f hf last
  have hmin (i : Fin R) : w≤gaps i := sortedGap_antitone _ f hf (by
    change i.val≤R-1; omega)
  let B := gapMatrix (placedSpectrum hmn (rowRank (h+1)) f)
  have hW := appt_all_ordered_pair_witnesses hmn hρ.1.isHermitian happt (rowRank (h+1))
  have hB : B.IsHermitian := gapMatrix_hermitian _ hW
  have hsym (i j : Fin (h+1)) : B i j=B j i := by
    have he := congrArg (fun M => M j i) hB.eq
    simpa [Matrix.conjTranspose_apply] using he
  have hlo (i j : Fin (h+1)) (hij : i≠j) : w≤B i j := by
    by_cases hi : i<j
    · calc
        w ≤ gaps (rowRank (h+1) ⟨(i,j),hi⟩) := hmin _
        _ = B i j := (placed_gap_eq_sortedGap hmn (rowRank (h+1)) f ⟨(i,j),hi⟩).symm
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hij)
      rw [hsym]
      calc
        w ≤ gaps (rowRank (h+1) ⟨(j,i),hj⟩) := hmin _
        _ = B j i := (placed_gap_eq_sortedGap hmn (rowRank (h+1)) f ⟨(j,i),hj⟩).symm
  let G : Matrix (Fin (h+1)) (Fin (h+1)) ℝ := B-w • completeAdjacency
  obtain ⟨hG,hdiag,hn,hord⟩ := residual_graph_properties B w hB
    (gapMatrix_diag _) hlo (placed_gap_rowMajor hmn f hf)
  have hrestore : G+w • completeAdjacency=B := by dsimp [G]; abel
  have hp : ((2*b) • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-
      (G+w • completeAdjacency)).PosSemidef := by
    rw [hrestore]
    exact witness_gap_psd_bound _ b hW
      (placedSpectrum_diagonal_le (by omega) hmn (rowRank (h+1)) f hf)
  have hcap : (h : ℝ)*w≤2*b := baseline_all_ones_bound G w (2*b) hn hp
  have hg := baseline_graph_refined_budget G w (2*b) hw (by positivity) hn hG hdiag hord hp
  rw [row_energy_eq_pair_sum] at hg
  have hsum (F : ℝ → ℝ) :
      (∑ p : UpperPair (h+1), F (G p.val.1 p.val.2)) = ∑ i, F (gaps i-w) :=
    residual_pair_sum hmn f w F
  rw [hsum (fun x => x^2), hsum (fun x => x)] at hg
  have hvar := sorted_centered_variance hR h2R f hf
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
  change (∑ i, (f i)^2)-1/(D:ℝ) ≤
    (∑ i, (gaps i)^2)-w*(∑ i, gaps i)+(D:ℝ)/4*w^2 at hvar
  have he : (∑ i, (gaps i)^2)-w*(∑ i, gaps i) =
      (∑ i, (gaps i-w)^2)+w*(∑ i, (gaps i-w)) := by
    simp [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [he] at hvar
  have hT : 0≤∑ i, (gaps i-w) := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hmin i))
  exact scalar_baseline_variance_bound ((h+1 : ℕ) : ℝ) (h:ℝ) (D:ℝ) b w
    (∑ i, (gaps i-w)) (∑ i, (gaps i-w)^2) ((∑ i, (f i)^2)-1/(D:ℝ))
    (by positivity) (by exact_mod_cast hh) (by norm_num) hb.le hw hT hcap
    (by nlinarith [hg]) hvar

end APPTReview
