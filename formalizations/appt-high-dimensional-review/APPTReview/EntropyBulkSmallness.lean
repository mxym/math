import APPTReview.EntropyQuantile

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

theorem antitone_nonnegative_prefix_square {R : ℕ} (g : Fin R → ℝ)
    (hg : Antitone g) (hn : ∀ i,0≤g i) (p : Fin R) :
    ((p.val+1:ℕ):ℝ)*(g p)^2≤∑ i,(g i)^2 := by
  calc
    _ = ∑ _i∈Finset.Iic p,(g p)^2 := by simp
    _ ≤ ∑ i∈Finset.Iic p,(g i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (hn p) (hg (Finset.mem_Iic.mp hi)) 2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)

/-- Isolate every potentially large positive or negative deviation in the
exceptional head. This follows from the actual ordered paired-gap budget. -/
theorem sorted_bulk_deviation_square {D R h : ℕ} (hh : 1≤h) (hhR : h≤R) (hRD : 2*R≤D)
    (f : Fin D → ℝ) (hf : Antitone f) (p : Fin D) (hb : 0<f p)
    (hpl : h-1≤p.val) (hpr : p.val≤D-h)
    (hbudget : (∑ i : Fin R,(sortedGap (show R≤D by omega) f i)^2)≤8*(f p)^2) :
    ∀ i∈entropyBulkIndices D h,(f i/f p-1)^2≤8/(h:ℝ) := by
  let j : Fin R := ⟨h-1,by omega⟩
  let l := Fin.castLE (show R≤D by omega) j
  let r := l.rev
  let q := sortedGap (show R≤D by omega) f j
  have hq : 0≤q := sortedGap_nonneg hRD f hf j
  have hhead := antitone_nonnegative_prefix_square (sortedGap (show R≤D by omega) f)
    (sortedGap_antitone _ f hf) (sortedGap_nonneg hRD f hf) j
  have hidx : j.val+1=h := by dsimp [j];omega
  rw [hidx] at hhead
  have hsq : (h:ℝ)*q^2≤8*(f p)^2 := hhead.trans hbudget
  have hpr' : p≤r := by change p.val≤D-(h-1+1);omega
  have hpl' : l≤p := hpl
  have hblo := hf hpr'
  have hbhi := hf hpl'
  have hhP : (0:ℝ)<h := by exact_mod_cast (by omega : 0<h)
  intro i hi
  have hi' : h≤ i.val ∧ i.val<D-(h+1) := by simpa [entropyBulkIndices] using hi
  have hil : l ≤ i := by change h-1≤ i.val;omega
  have hir : i≤r := by change i.val≤D-(h-1+1);omega
  have hfil := hf hil
  have hfir := hf hir
  have hl : -q≤f i-f p := by dsimp [q,sortedGap,l,r] at *;linarith
  have hu : f i-f p≤q := by dsimp [q,sortedGap,l,r] at *;linarith
  have hs : (f i-f p)^2≤q^2 := by
    have ht := mul_nonneg (show 0≤q-(f i-f p) by linarith) (show 0≤q+(f i-f p) by linarith)
    nlinarith
  have hs' := (mul_le_mul_of_nonneg_left hs hhP.le).trans hsq
  have he : (f i/f p-1)^2=(f i-f p)^2/(f p)^2 := by field_simp <;> ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hb) hhP).2 (by nlinarith)

noncomputable def entropyBulkRadius (k : ℕ) : ℝ := Real.sqrt (8/((k+1:ℕ):ℝ))

/-- Every true nonexceptional eigenvalue has dimension-controlled contrast. -/
theorem density_appt_entropy_bulk_smallness {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ∀ i∈entropyBulkIndices (Fintype.card (Fin (k+2) × Fin n)) (k+1),
      |hρ.1.isHermitian.eigenvalues₀ i/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)-1|≤entropyBulkRadius k := by
  let D := Fintype.card (Fin (k+2) × Fin n)
  let R := Fintype.card (UpperPair (k+2))
  have hcard : 2*R+(k+2)=(k+2)*(k+2) := upperPair_card (k+2)
  have hplace : 2*R+(k+2)≤D := pairPlacementBound hmn
  have hhR : k+1≤R := by nlinarith
  have hp := paper_pivot_rank_bounds hmn
  have hbudget := density_appt_pair_gap_square_sum (h:=k+1) (by omega) hmn hρ hP
  rw [pairedPivot_eq_paperPivot hmn] at hbudget
  have hlow : k+1-1≤(paperPivot hmn).val := by
    have ht := hp.1
    simpa [paperPivot] using (show k+1-1≤(k+2)*n-(k+2)*(k+3)/2 by omega)
  have hhigh : (paperPivot hmn).val≤D-(k+1) := by
    have ht := hp.2.1
    dsimp [paperPivot,D]
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hb := sorted_bulk_deviation_square (h:=k+1) (by omega) hhR (by omega : 2*R≤D)
    hρ.1.isHermitian.eigenvalues₀ hρ.1.isHermitian.eigenvalues₀_antitone (paperPivot hmn)
    (paper_head_pivot_positive hmn hρ hP) hlow hhigh hbudget
  intro i hi
  have hh := hb i hi
  have hs := Real.sq_sqrt (show (0:ℝ)≤8/((k+1:ℕ):ℝ) by positivity)
  have hn := Real.sqrt_nonneg (8/((k+1:ℕ):ℝ))
  have ha := sq_abs (hρ.1.isHermitian.eigenvalues₀ i/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)-1)
  unfold entropyBulkRadius
  nlinarith [abs_nonneg (hρ.1.isHermitian.eigenvalues₀ i/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)-1)]

end APPTReview
