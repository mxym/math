import APPTReview.EntropyMeanUniform
import APPTReview.EntropyNormalizerLimit
import APPTReview.FixedLocalRatio

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The exact APPT cut controls the total paired mass and the last gap. -/
theorem density_appt_gap_mass_last {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let R := Fintype.card (UpperPair (k+2))
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    let g := sortedGap (gapPrefixBound hmn) f
    (∑ i,g i)≤((k+2:ℕ):ℝ)*b ∧
    ((k+1:ℕ):ℝ)*g ⟨R-1,by have hr : 0<R := upperPair_card_pos (h:=k+1) (by omega);omega⟩≤2*b := by
  dsimp only
  let D := Fintype.card (Fin (k+2) × Fin n)
  let R := Fintype.card (UpperPair (k+2))
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  let g := sortedGap (gapPrefixBound hmn) f
  have hc : 2*R+(k+2)=(k+2)*(k+2) := upperPair_card (k+2)
  have hplace : 2*R+(k+2)≤D := pairPlacementBound hmn
  have hR : 0<R := by nlinarith
  let G := gapMatrix (placedSpectrum hmn (rowRank (k+2)) f)
  have hw:=appt_all_ordered_pair_witnesses hmn hρ.1.isHermitian hP (rowRank (k+2))
  have hG:=gapMatrix_hermitian _ hw
  have hsym (i j : Fin (k+2)) : G i j=G j i := by
    have he:=congrArg (fun M => M j i) hG.eq
    simpa [Matrix.conjTranspose_apply] using he
  have hdiag : ∀ i,placedSpectrum hmn (rowRank (k+2)) f (i,i)≤b := by
    have hh:=placedSpectrum_diagonal_le (by omega : 0<k+2) hmn (rowRank (k+2)) f hρ.1.isHermitian.eigenvalues₀_antitone
    simpa only [pairedPivot_eq_paperPivot hmn] using hh
  have hcap:=gap_mass_cap G (2*b) hsym (gapMatrix_diag _)
    (witness_gap_psd_bound _ b hw hdiag)
  have hsum : (∑ p : UpperPair (k+2),G p.val.1 p.val.2)=∑ i,g i := by
    dsimp only [G]
    simp_rw [placed_gap_eq_sortedGap]
    exact (rowRank (k+2)).sum_comp _
  rw [hsum] at hcap
  have hmass : (∑ i,g i)≤((k+2:ℕ):ℝ)*b := by nlinarith
  refine ⟨hmass,?_⟩
  let last : Fin R := ⟨R-1,by omega⟩
  have hmin (i : Fin R) : g last≤g i := sortedGap_antitone _ f
    hρ.1.isHermitian.eigenvalues₀_antitone (by change i.val≤R-1;omega)
  have hlast:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hmin i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlast
  have he : ((k+2:ℕ):ℝ)*((k+1:ℕ):ℝ)=2*(R:ℝ) := by
    have hr : 2*(R:ℝ)+((k+2:ℕ):ℝ)=((k+2:ℕ):ℝ)*((k+2:ℕ):ℝ) := by exact_mod_cast hc
    push_cast at hr ⊢;nlinarith
  have H : ((k+2:ℕ):ℝ)*(((k+1:ℕ):ℝ)*g last)≤((k+2:ℕ):ℝ)*(2*b) := by
    rw [← mul_assoc,he]
    nlinarith [hlast.trans hmass]
  exact (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<((k+2:ℕ):ℝ))).mp H

/-- The paper pivot has a uniform, aspect-ratio-independent normalization
error. A slightly relaxed constant three avoids an unnecessary exact expansion. -/
theorem density_appt_uniform_mean_radius {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    |paperNormalization hmn hρ-1|≤3/((k+1:ℕ):ℝ) := by
  let D := Fintype.card (Fin (k+2) × Fin n)
  let R := Fintype.card (UpperPair (k+2))
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  let g := sortedGap (gapPrefixBound hmn) f
  have hc : 2*R+(k+2)=(k+2)*(k+2) := upperPair_card (k+2)
  have hplace : 2*R+(k+2)≤D := pairPlacementBound hmn
  have hR : 0<R := by nlinarith
  have hpval : (paperPivot hmn).val=D-R-(k+2) := by
    exact (congrArg Fin.val (pairedPivot_eq_paperPivot hmn)).symm
  have hp:=paired_pivot_trace_deviation hR (show 2*R≤D by omega) f
    hρ.1.isHermitian.eigenvalues₀_antitone (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (paperPivot hmn) (by rw [hpval];omega) (by rw [hpval];omega)
  obtain ⟨hmass,hlast⟩:=density_appt_gap_mass_last hmn hρ hP
  let w := g ⟨R-1,by omega⟩
  change |1-(D:ℝ)*b|≤(∑ i,g i)+(D:ℝ)*w at hp
  change (∑ i,g i)≤((k+2:ℕ):ℝ)*b at hmass
  change ((k+1:ℕ):ℝ)*w≤2*b at hlast
  have hb : 0<b := paper_head_pivot_positive hmn hρ hP
  have hDP : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hhP : (0:ℝ)<((k+1:ℕ):ℝ) := by positivity
  have hDb : 0<(D:ℝ)*b := mul_pos hDP hb
  have hd : ((k+2:ℕ):ℝ)*((k+1:ℕ):ℝ)≤(D:ℝ) := by
    have hr : (k+2)*(k+1)≤D := by nlinarith
    exact_mod_cast hr
  have H1:=mul_le_mul_of_nonneg_left hp hhP.le
  have H2:=mul_le_mul_of_nonneg_left hmass hhP.le
  have H3:=mul_le_mul_of_nonneg_left hlast hDP.le
  have H4:=mul_le_mul_of_nonneg_right hd hb.le
  have hbound : |1-(D:ℝ)*b| *((k+1:ℕ):ℝ)≤3*((D:ℝ)*b) := by nlinarith
  have hid : paperNormalization hmn hρ-1=(1-(D:ℝ)*b)/((D:ℝ)*b) := by
    unfold paperNormalization
    change 1/((D:ℝ)*b)-1=_
    field_simp
  rw [hid,abs_div,abs_of_pos hDb]
  exact (div_le_div_iff₀ hDb hhP).2 hbound

end APPTReview
