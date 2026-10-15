import APPTReview.PhysicalHeadVariance

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

theorem pairedPivot_eq_paperPivot {k n : ℕ} (hmn : k+2≤n) :
    pairedPivot (by omega : 0<k+2) hmn=paperPivot hmn := by
  apply Fin.ext
  rw [pairedPivot_paper_index]
  rfl

/-- The exact normalized retained-head budget at the paper's actual pivot. -/
theorem density_appt_normalized_head_variance {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let hD : 3*(k+1)+1≤Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    (APPT.Quantum.purity A-1/(Fintype.card (Fin (k+2) × Fin n):ℝ))/b^2 ≤
      (∑ i : Fin (k+1),(sortedHeadA hD f b i+sortedHeadBeta hD f b i.castSucc)^2)+
      max 4 ((Fintype.card (Fin (k+2) × Fin n):ℝ)/((k+1:ℕ):ℝ)^2) := by
  dsimp only
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  have hD : 3*(k+1)+1≤D := by dsimp [D];simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
  have hp : 0<b := by
    have hh := density_pairedPivot_positive (h:=k+1) (by omega) hmn hρ hP
    rwa [pairedPivot_eq_paperPivot hmn] at hh
  have hbound := density_appt_head_retained_variance (h:=k+1) (by omega) hmn hρ hP
  rw [pairedPivot_eq_paperPivot hmn,← purity_eq_ordered_eigenvalues hρ.1.isHermitian] at hbound
  have he (i : Fin (k+1)) :
      b*(sortedHeadA hD f b i+sortedHeadBeta hD f b i.castSucc)=
      sortedGap (show k+1≤D by omega) f i := by
    dsimp only [sortedHeadA,sortedHeadBeta,starSlotLabel,sortedGap]
    have hb : b≠0 := ne_of_gt hp
    have hi : (⟨D-(1+i.castSucc.val),by omega⟩:Fin D)=(Fin.castLE (show k+1≤D by omega) i).rev := by
      apply Fin.ext
      simp only [Fin.val_castSucc,Fin.val_rev,Fin.val_castLE,Nat.add_comm]
    rw [hi]
    field_simp
    simp only [Fin.castLE]
    ring
  have hsum : b^2*(∑ i : Fin (k+1),(sortedHeadA hD f b i+sortedHeadBeta hD f b i.castSucc)^2)=
      ∑ i : Fin (k+1),(sortedGap (show k+1≤D by omega) f i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_pow,he]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).2
  rw [add_mul,mul_comm (∑ i : Fin (k+1),_),hsum]
  exact hbound

/-- Correcting the retained second moment by the entire exceptional entropy
head leaves only the tail coefficient; the last negative square is favorable. -/
theorem entropy_head_corrected_variance {k : ℕ}
    (a : Fin (k+1) → ℝ) (β : Fin (k+2) → ℝ) (V C : ℝ)
    (hV : V≤(∑ i,(a i+β i.castSucc)^2)+C) :
    V/2+(∑ i : Fin (k+1),(entropyKernel (a i)-(a i)^2/2))+
      (∑ i : Fin (k+2),(entropyKernel (-β i)-(β i)^2/2))≤C/2+entropyHead a β := by
  have he : (∑ i : Fin (k+1),(a i+β i.castSucc)^2)=
      (∑ i,(a i)^2)+2*(∑ i : Fin (k+1),a i*β i.castSucc)+(∑ i : Fin (k+1),(β i.castSucc)^2) := by
    have hid (i : Fin (k+1)) : (a i+β i.castSucc)^2=(a i)^2+2*(a i*β i.castSucc)+(β i.castSucc)^2 := by ring
    simp_rw [hid]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have ht := Fin.sum_univ_castSucc (fun i : Fin (k+2) => (β i)^2)
  rw [he] at hV
  simp only [entropyHead,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div]
  nlinarith [sq_nonneg (β (Fin.last (k+1)))]

/-- The physical form of E24: all quantities are computed from the actual
ordered eigenvalues and original trace-square purity, with no supplied budget. -/
theorem density_appt_entropy_corrected_variance {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let hD : 3*(k+1)+1≤Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    let a := sortedHeadA hD f b
    let β := sortedHeadBeta hD f b
    (APPT.Quantum.purity A-1/(Fintype.card (Fin (k+2) × Fin n):ℝ))/b^2/2+
      (∑ i : Fin (k+1),(entropyKernel (a i)-(a i)^2/2))+
      (∑ i : Fin (k+2),(entropyKernel (-β i)-(β i)^2/2))≤
      max 4 ((Fintype.card (Fin (k+2) × Fin n):ℝ)/((k+1:ℕ):ℝ)^2)/2+entropyHead a β :=
  entropy_head_corrected_variance _ _ _ _ (density_appt_normalized_head_variance hmn hρ hP)

end APPTReview
