import APPTReview.HeadRowOrder
import APPTReview.FinitePurity

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Actual APPT variance with its full exceptional-head contribution retained.
Only physical density/APPT and dimensions are assumed. -/
theorem density_appt_head_retained_variance {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    (∑ i,(hρ.1.isHermitian.eigenvalues₀ i)^2)-1/(Fintype.card (Fin (h+1) × Fin n):ℝ) ≤
      (∑ i : Fin h,(sortedGap (show h≤Fintype.card (Fin (h+1) × Fin n) by
        have hp:=pairPlacementBound hmn;have hc:=upperPair_card (h+1);nlinarith)
        hρ.1.isHermitian.eigenvalues₀ i)^2)+
      max 4 ((Fintype.card (Fin (h+1) × Fin n):ℝ)/(h:ℝ)^2)*
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
  have hg := baseline_graph_head_budget G w (2*b) hw hG hn hdiag hord hp
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
  have hret := scalar_head_variance_bound ((h+1 : ℕ) : ℝ) (h:ℝ) (D:ℝ) b w
    (∑ i, (gaps i-w)) (∑ i, (gaps i-w)^2) (rowEnergy G 0) ((∑ i, (f i)^2)-1/(D:ℝ))
    (by positivity) (by exact_mod_cast hh) (by norm_num) hb.le hw hT hcap
    (by nlinarith [hg]) hvar
  have hhead := residual_first_row_le_head hh hmn f hf w hw hn
  exact hret.trans (add_le_add hhead le_rfl)

end APPTReview
