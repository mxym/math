import APPTReview.EntropyBulkPartition
import APPTReview.PhysicalHeadLimit

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def vonNeumannDeficit {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : ℝ :=
  Real.log (Fintype.card (Fin m × Fin n):ℝ)-spectralVonNeumannEntropy hρ.1.isHermitian

noncomputable def paperEntropyRest {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : ℝ :=
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  (∑ i∈entropyBulkIndices D (k+1),entropyRemainder (f i/b-1))-
    (D:ℝ)*entropyRemainder (1/((D:ℝ)*b)-1)

/-- Full von Neumann entropy, with the exact exceptional head deficit retained.
The remaining term consists only of nonexceptional logarithmic remainders and
the necessary trace-centering remainder, all evaluated on the actual spectrum. -/
theorem density_appt_full_entropy_rest_bound {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let D := Fintype.card (Fin (k+2) × Fin n)
    let b := hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)
    vonNeumannDeficit hρ/b ≤
      max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2-paperHeadDeficit hmn hρ+paperEntropyRest hmn hρ := by
  dsimp only
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  have hD : 3*(k+1)+1≤D := by dsimp [D];simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
  have hp : 0<b := paper_head_pivot_positive hmn hρ hP
  have hn (i) : 0≤f i := by
    have ht := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using ht
  have hi := spectrum_entropy_remainder_identity (by omega : 0<D) f hn
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) b hp
  have hpart := entropy_remainder_partition hD f b
  have hret := density_appt_entropy_corrected_variance hmn hρ hP
  dsimp only at hret
  have hpur : (∑ i,(f i)^2)=APPT.Quantum.purity A :=
    (purity_eq_ordered_eigenvalues hρ.1.isHermitian).symm
  rw [hpur] at hi
  have he : vonNeumannDeficit hρ=Real.log (D:ℝ)+(∑ i,f i*Real.log (f i)) := by
    unfold vonNeumannDeficit spectralVonNeumannEntropy
    ring
  rw [← he] at hi
  simp only [entropyRemainder,neg_sq] at hpart
  simp only [Finset.sum_sub_distrib,← Finset.sum_div] at hpart hret
  change vonNeumannDeficit hρ/b ≤max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2-
    (2-entropyHead (sortedHeadA hD f b) (sortedHeadBeta hD f b))+
    ((∑ i∈entropyBulkIndices D (k+1),entropyRemainder (f i/b-1))-
      (D:ℝ)*entropyRemainder (1/((D:ℝ)*b)-1))
  have hparts : (∑ i,entropyRemainder (f i/b-1))=
      (∑ i : Fin (k+1),(entropyKernel (sortedHeadA hD f b i)-(sortedHeadA hD f b i)^2/2))+
      (∑ i∈entropyBulkIndices D (k+1),entropyRemainder (f i/b-1))+
      (∑ i : Fin (k+2),(entropyKernel (-sortedHeadBeta hD f b i)-(sortedHeadBeta hD f b i)^2/2)) := by
    simpa only [entropyRemainder,neg_sq] using entropy_remainder_partition hD f b
  rw [hparts] at hi
  simp only [Finset.sum_sub_distrib,← Finset.sum_div] at hi
  linarith

/-- Quantitative control of the exact remainder on a specified nonexceptional
set. Smallness is only used on this set and on the scalar normalization. -/
theorem entropy_rest_taylor_bound {D : ℕ} (f : Fin D → ℝ) (b δ ν : ℝ)
    (S : Finset (Fin D)) (hδ : 0≤δ) (hδ1 : δ<1) (hν : 0≤ν) (hν1 : ν<1)
    (htail : ∀ i∈S,|f i/b-1|≤δ)
    (hmean : |1/((D:ℝ)*b)-1|≤ν) :
    (∑ i∈S,entropyRemainder (f i/b-1))-(D:ℝ)*entropyRemainder (1/((D:ℝ)*b)-1)≤
      (δ/(2*(1-δ)))*(∑ i,(f i/b-1)^2)+
      (ν/(2*(1+ν)))*(D:ℝ)*(1/((D:ℝ)*b)-1)^2 := by
  have hc : 0≤δ/(2*(1-δ)) := by positivity
  have hs := Finset.sum_le_sum (fun i hi => (entropyRemainder_bounds δ (f i/b-1) hδ hδ1 (htail i hi)).2)
  rw [← Finset.mul_sum] at hs
  have hsubset : (∑ i∈S,(f i/b-1)^2)≤∑ i,(f i/b-1)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => sq_nonneg _)
  have htail' := hs.trans (mul_le_mul_of_nonneg_left hsubset hc)
  have hm := mul_le_mul_of_nonneg_left
    (entropyRemainder_bounds ν (1/((D:ℝ)*b)-1) hν hν1 hmean).1 (Nat.cast_nonneg D)
  nlinarith

/-- Finite full-entropy bound with an explicit Taylor error; no exceptional
coordinate is subjected to a small-deviation assumption. -/
theorem density_appt_full_entropy_taylor_bound {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (δ ν : ℝ) (hδ : 0≤δ) (hδ1 : δ<1) (hν : 0≤ν) (hν1 : ν<1)
    (htail : ∀ i∈entropyBulkIndices (Fintype.card (Fin (k+2) × Fin n)) (k+1),
      |hρ.1.isHermitian.eigenvalues₀ i/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)-1|≤δ)
    (hmean : |1/((Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))-1|≤ν) :
    let D := Fintype.card (Fin (k+2) × Fin n)
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    vonNeumannDeficit hρ/b≤max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2-paperHeadDeficit hmn hρ+
      (δ/(2*(1-δ)))*(∑ i,(f i/b-1)^2)+
      (ν/(2*(1+ν)))*(D:ℝ)*(1/((D:ℝ)*b)-1)^2 := by
  dsimp only
  have hbase := density_appt_full_entropy_rest_bound hmn hρ hP
  have hrest := entropy_rest_taylor_bound hρ.1.isHermitian.eigenvalues₀
    (hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)) δ ν
    (entropyBulkIndices (Fintype.card (Fin (k+2) × Fin n)) (k+1)) hδ hδ1 hν hν1 htail hmean
  dsimp only [paperEntropyRest] at hbase
  linarith

end APPTReview
