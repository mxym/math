import Deviation.JointTypical

open scoped BigOperators Topology
open Filter ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem jointTypical_captured_qmass_le (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (k : ℕ) (δ : ℝ) (B : Finset (Fin k → ι)) :
    wordMass q k (jointTypical p q k δ ∩ B) ≤
      (B.card:ℝ)*Real.exp (-(k:ℝ)*(entropy q-δ)) := by
  calc
    _ ≤ ∑ _w ∈ jointTypical p q k δ ∩ B, Real.exp (-(k:ℝ)*(entropy q-δ)) :=
      Finset.sum_le_sum (fun w hw => jointTypical_q_likelihood_upper p q hq k δ w
        (Finset.mem_inter.mp hw).1)
    _ = ((jointTypical p q k δ ∩ B).card:ℝ)*Real.exp (-(k:ℝ)*(entropy q-δ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
        jointTypical p q k δ ∩ B ⊆ B)) (Real.exp_pos _).le

/-- A set with exponentially fewer than `exp(k H(q))` words misses asymptotically
full `q` mass inside the joint typical set, uniformly over the selected set. -/
theorem jointTypical_remaining_qmass_lower (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (c δ : ℝ) (hδ : 0 < δ) (hgap : c+δ < entropy q) :
    ∀ᶠ k : ℕ in atTop, ∀ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c) →
      (1:ℝ)/2 ≤ wordMass q k (jointTypical p q k δ \ B) := by
  have hmass := jointTypical_mass_tendsto_one p q hq hs δ hδ
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ)*(entropy q-c-δ))) atTop (𝓝 0) := by
    have hlin := tendsto_natCast_atTop_atTop.atTop_mul_const (show 0 < entropy q-c-δ by linarith)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext k
    congr 1
    ring
  filter_upwards [hmass.eventually (Ioi_mem_nhds (by norm_num : (3:ℝ)/4 < 1)),
    hexp.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4))] with k hmassk hexpk
  intro B hB
  have hcap := jointTypical_captured_qmass_le p q hq k δ B
  have hmul := mul_le_mul_of_nonneg_right hB (Real.exp_pos (-(k:ℝ)*(entropy q-δ))).le
  have heq : Real.exp ((k:ℝ)*c)*Real.exp (-(k:ℝ)*(entropy q-δ)) =
      Real.exp (-(k:ℝ)*(entropy q-c-δ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  have hsplit := Finset.sum_inter_add_sum_sdiff (jointTypical p q k δ) B (iidLaw q k)
  change wordMass q k (jointTypical p q k δ ∩ B)+
    wordMass q k (jointTypical p q k δ \ B) = wordMass q k (jointTypical p q k δ) at hsplit
  linarith

theorem jointTypical_remaining_pmass_lower (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hps : ∑ i, p i = 1) (hq : ∀ i, 0 ≤ q i)
    (hSupport : ∀ i, 0 < q i → 0 < p i) (k : ℕ) (δ : ℝ)
    (B : Finset (Fin k → ι)) :
    wordMass q k (jointTypical p q k δ \ B)*Real.exp (-(k:ℝ)*(divergence q p+2*δ)) ≤
      1-wordMass p k B := by
  have hchange : wordMass q k (jointTypical p q k δ \ B)*
      Real.exp (-(k:ℝ)*(divergence q p+2*δ)) ≤
      wordMass p k (jointTypical p q k δ \ B) := by
    unfold wordMass
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun w hw => jointTypical_change_of_measure p q hq hSupport k δ w
      (Finset.mem_sdiff.mp hw).1)
  have hsub : jointTypical p q k δ \ B ⊆ Finset.univ \ B := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w,(Finset.mem_sdiff.mp hw).2⟩
  have hmono := wordMass_mono p hp k hsub
  have htotal := Finset.sum_sdiff (Finset.subset_univ B) (f := iidLaw p k)
  rw [iidLaw_sum p hps k] at htotal
  change wordMass p k (Finset.univ \ B)+wordMass p k B = 1 at htotal
  linarith

/-- Uniform lower bound on the missed iid mass of every exponentially bounded
subset. The likelihood comparison and both LLNs are internally proved from
the actual finite laws; no large-deviation or type-cardinality premise is used. -/
theorem iid_subset_tail_eventual_lower (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hps : ∑ i, p i = 1) (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hSupport : ∀ i, 0 < q i → 0 < p i) (c : ℝ) (hc : c < entropy q)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c) →
      Real.exp (-(k:ℝ)*(divergence q p+ε)) ≤ 1-wordMass p k B := by
  let δ := min ((entropy q-c)/2) (ε/4)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hg : c+δ < entropy q := by
    have h := min_le_left ((entropy q-c)/2) (ε/4)
    change δ ≤ (entropy q-c)/2 at h
    linarith
  have hη : 0 < ε-2*δ := by
    have h := min_le_right ((entropy q-c)/2) (ε/4)
    change δ ≤ ε/4 at h
    linarith
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ)*(ε-2*δ))) atTop (𝓝 0) := by
    have hlin := tendsto_natCast_atTop_atTop.atTop_mul_const hη
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext k
    congr 1
    ring
  filter_upwards [jointTypical_remaining_qmass_lower p q hq hqs c δ hδ hg,
    hexp.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with k hk he
  intro B hB
  have hqmass := hk B hB
  have hchange := jointTypical_remaining_pmass_lower p q hp hps hq hSupport k δ B
  calc
    _ = Real.exp (-(k:ℝ)*(divergence q p+2*δ))*Real.exp (-(k:ℝ)*(ε-2*δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k:ℝ)*(divergence q p+2*δ))*((1:ℝ)/2) :=
      mul_le_mul_of_nonneg_left he.le (Real.exp_pos _).le
    _ ≤ wordMass q k (jointTypical p q k δ \ B)*Real.exp (-(k:ℝ)*(divergence q p+2*δ)) := by
      rw [mul_comm _ ((1:ℝ)/2)]
      exact mul_le_mul_of_nonneg_right hqmass (Real.exp_pos _).le
    _ ≤ _ := hchange

end
end ExtractionDeviation
