import APPTReview.FixedLocalRatio
import APPTReview.IntervalMoment

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Uniform over all states, with an explicit error for a fixed first dimension. -/
theorem density_appt_fixed_local_upper {m n : ℕ} (hm : 2≤m) (hn : 2*m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    ((m:ℝ)*n)*APPT.Quantum.purity A ≤
      (m:ℝ)^2/((m:ℝ)^2-1)+13*(m:ℝ)/n := by
  classical
  have hmn : m≤n := by omega
  let D := Fintype.card (Fin m × Fin n)
  let R := Fintype.card (UpperPair m)
  have hcR := upperPair_card m
  have hR : 0<R := by dsimp [R]; nlinarith
  have hplace := pairPlacementBound hmn
  have hD2 : 2*m*m≤D := by
    dsimp [D]
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  let f := hρ.1.isHermitian.eigenvalues₀
  let t := finalTop hR (gapPrefixBound hmn)
  let p := pairedPivot (by omega : 0<m) hmn
  let s := Finset.Icc t p
  let b := f p
  let r : ℝ := ((m:ℝ)+1)/((m:ℝ)-1)
  let C : ℝ := (m:ℝ)^2/((m:ℝ)^2-1)
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hmp : (0:ℝ)<(m:ℝ)-1 := by linarith
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hDP : (0:ℝ)<D := by dsimp [D]; simp; positivity
  have hr : 0<r := div_pos (by linarith) hmp
  have hsCard : s.card+m*m=D+2 := by
    dsimp [s]
    rw [Fin.card_Icc]
    change (D-R-m+1-(R-1))+m*m=D+2
    have h0 : 2*R+m=m*m := hcR
    have hd : 2*R+m≤D := hplace
    omega
  have hLD : s.card≤D := by
    have h := Finset.card_le_card (Finset.subset_univ s)
    simpa [D] using h
  have hDL : D≤2*s.card := by nlinarith
  have hsP : 0<s.card := by nlinarith
  have hf : Antitone f := hρ.1.isHermitian.eigenvalues₀_antitone
  have hnonneg (i : Fin D) : 0≤f i := by
    have h := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using h
  have htrace : (∑ i, f i)=1 := ordered_eigenvalues_sum hρ.1.isHermitian hρ.2
  have hrank := density_appt_bulk_ratio hm hmn hρ happt hR
  have htop : f t≤r*b := by
    have he : r*b=(((m:ℝ)+1)*b)/((m:ℝ)-1) := by dsimp [r]; ring
    rw [he]
    apply (le_div_iff₀ hmp).2
    simpa only [mul_comm] using hrank
  have hl (i : Fin D) (hi : i∈s) : b≤f i := hf (Finset.mem_Icc.mp hi).2
  have hu (i : Fin D) (hi : i∈s) : f i≤r*b :=
    (hf (Finset.mem_Icc.mp hi).1).trans htop
  have hfour : 4≤D := by nlinarith
  have hmax0 := appt_largest_eigenvalue_bound hm hmn hρ happt hfour
  have hmax (i : Fin D) : f i≤3/(D:ℝ) := by
    have hh : f (rankTwoLabels hfour (1,0))≤3/((D:ℝ)+2) := by simpa [D] using hmax0
    have ht : f i≤f (rankTwoLabels hfour (1,0)) := by
      apply hf
      change (0:ℕ) ≤ i.val
      exact Nat.zero_le _
    exact ht.trans (hh.trans (div_le_div_of_nonneg_left (by norm_num) hDP (by linarith)))
  have hmoment := bulk_exception_moment s f b r (3/(D:ℝ))
    (hnonneg p) hr (by positivity) hsP hnonneg htrace hmax hl hu
  have hpC : 0<(m:ℝ)^2-1 := by nlinarith
  have hC0 : 0≤C := div_nonneg (sq_nonneg _) hpC.le
  have hC2 : C≤2 := (div_le_iff₀ hpC).2 (by nlinarith)
  have hid : (r+1)^2/(4*r)=C := by
    dsimp [r,C]
    field_simp <;> ring
  have hid2 : (r+1)^2/(4*r*(s.card:ℝ))=C/(s.card:ℝ) := by
    rw [← div_div, hid]
  rw [hid2] at hmoment
  have hb : (∑ i, (f i)^2)≤C/(s.card:ℝ)+9*((D:ℝ)-(s.card:ℝ))/(D:ℝ)^2 := by
    convert hmoment using 1 <;> ring
  have he := bulk_rescale_bound (D:ℝ) (s.card:ℝ) C ((m:ℝ)^2)
    (∑ i, (f i)^2) hDP (by exact_mod_cast hsP) hC0 hC2
    (by exact_mod_cast hLD) (by exact_mod_cast hDL)
    (by have hc : (s.card:ℝ)+(m:ℝ)^2=(D:ℝ)+2 := by simpa only [pow_two] using (show (s.card:ℝ)+(m:ℝ)*(m:ℝ)=(D:ℝ)+2 by exact_mod_cast hsCard)
        nlinarith) hb
  have herr : 13*(m:ℝ)^2/(D:ℝ)=13*(m:ℝ)/n := by
    simp only [D,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    field_simp <;> ring
  rw [herr] at he
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  simpa [D,C] using he

end APPTReview
