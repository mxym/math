import Spectrum.Tilt

open scoped BigOperators Topology
open Filter ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def wordMass (p : ι → ℝ) (k : ℕ) (A : Finset (Fin k → ι)) : ℝ :=
  ∑ w ∈ A, iidLaw p k w

theorem wordMass_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (A : Finset (Fin k → ι)) : 0 ≤ wordMass p k A :=
  Finset.sum_nonneg (fun w _ => iidLaw_nonneg p hp k w)

theorem wordMass_le_one (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (k : ℕ) (A : Finset (Fin k → ι)) : wordMass p k A ≤ 1 := by
  calc
    _ ≤ ∑ w : Fin k → ι, iidLaw p k w :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun w _ _ => iidLaw_nonneg p hp k w)
    _ = 1 := iidLaw_sum p hs k

theorem wordMass_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    {A B : Finset (Fin k → ι)} (hAB : A ⊆ B) : wordMass p k A ≤ wordMass p k B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun w _ _ => iidLaw_nonneg p hp k w)

theorem wordMass_inter_lower (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (k : ℕ) (A B : Finset (Fin k → ι)) :
    wordMass p k A+wordMass p k B-1 ≤ wordMass p k (A ∩ B) := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := iidLaw p k)
  have hu := wordMass_le_one p hp hs k (A ∪ B)
  change wordMass p k (A ∪ B)+wordMass p k (A ∩ B) = wordMass p k A+wordMass p k B at h
  linarith

/-- A genuine joint typical set for both log likelihoods under the iid law `q`. -/
def jointTypical (p q : ι → ℝ) (k : ℕ) (δ : ℝ) : Finset (Fin k → ι) :=
  finiteTypicalBand q (selfInformation q) k δ ∩
    finiteTypicalBand q (selfInformation p) k δ

theorem jointTypical_qpos (p q : ι → ℝ) (k : ℕ) (δ : ℝ) (w : Fin k → ι)
    (hw : w ∈ jointTypical p q k δ) : 0 < iidLaw q k w :=
  (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2.1

theorem jointTypical_q_likelihood_upper (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (k : ℕ) (δ : ℝ) (w : Fin k → ι) (hw : w ∈ jointTypical p q k δ) :
    iidLaw q k w ≤ Real.exp (-(k:ℝ)*(entropy q-δ)) := by
  have hband := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
  rw [iidLaw_eq_exp_sum_of_pos q w (iidLaw_letters_pos q hq w hband.1)]
  apply Real.exp_le_exp.mpr
  simpa only [entropy, neg_mul] using (neg_le_neg (le_of_lt hband.2.1))

theorem jointTypical_change_of_measure (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hSupport : ∀ i, 0 < q i → 0 < p i) (k : ℕ) (δ : ℝ) (w : Fin k → ι)
    (hw : w ∈ jointTypical p q k δ) :
    iidLaw q k w * Real.exp (-(k:ℝ)*(divergence q p+2*δ)) ≤ iidLaw p k w := by
  have hbandq := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
  have hbandp := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2
  have hqpos := iidLaw_letters_pos q hq w hbandq.1
  rw [iidLaw_eq_exp_sum_of_pos q w hqpos,
    iidLaw_eq_exp_sum_of_pos p w (fun j => hSupport _ (hqpos j)), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcross := cross_entropy_eq_entropy_add_divergence q p
  change finiteMean q (selfInformation p) = entropy q+divergence q p at hcross
  have hqlo := hbandq.2.1
  change (k:ℝ)*(entropy q-δ) < ∑ j, selfInformation q (w j) at hqlo
  have hphi := hbandp.2.2
  nlinarith

theorem jointTypical_mass_tendsto_one (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k => wordMass q k (jointTypical p q k δ)) atTop (𝓝 1) := by
  have hA := finiteBandMass_self_tendsto_one q hq hs (selfInformation q) δ hδ
  have hB := finiteBandMass_self_tendsto_one q hq hs (selfInformation p) δ hδ
  have hsum := ((tendsto_const_nhds (x := (1:ℝ))).sub hA).add
    ((tendsto_const_nhds (x := (1:ℝ))).sub hB)
  simp only [sub_self, zero_add] at hsum
  have hgap : Tendsto (fun k => 1-wordMass q k (jointTypical p q k δ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun k =>
      sub_nonneg.mpr (wordMass_le_one q hq hs k _))) _ hsum
    apply Filter.Eventually.of_forall
    intro k
    have h := wordMass_inter_lower q hq hs k
      (finiteTypicalBand q (selfInformation q) k δ)
      (finiteTypicalBand q (selfInformation p) k δ)
    change wordMass q k (finiteTypicalBand q (selfInformation q) k δ)+
      wordMass q k (finiteTypicalBand q (selfInformation p) k δ)-1 ≤
        wordMass q k (jointTypical p q k δ) at h
    change 1-wordMass q k (jointTypical p q k δ) ≤
      (1-wordMass q k (finiteTypicalBand q (selfInformation q) k δ))+
      (1-wordMass q k (finiteTypicalBand q (selfInformation p) k δ))
    linarith
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub hgap
  simpa only [sub_sub_cancel, sub_zero] using h

end
end ExtractionDeviation
