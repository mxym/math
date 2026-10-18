import OperationalCompletion.GridCoverage
import Deviation.JointTypical

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem jointTypical_subset_lowEntropyWords (p q : ι → ℝ) (hq : ∀ i,0≤q i)
    (hqs : ∑ i,q i=1) (k : ℕ) (hk : 0<k) (δ : ℝ) :
    jointTypical p q k δ ⊆ lowEntropyWords k (entropy q+δ) := by
  intro w hw
  have hpos := jointTypical_qpos p q k δ w hw
  have hH := empirical_entropy_le_information hk q hq hqs w hpos
  have hband := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2.2.2
  change (∑ j,selfInformation q (w j))≤(k:ℝ)*(entropy q+δ) at hband
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  change entropy (empiricalLaw w)≤entropy q+δ
  change (k:ℝ)*entropy (empiricalLaw w)≤∑ j,selfInformation q (w j) at hH
  nlinarith

/-- A genuine lower large-deviation estimate for the fixed entropy-selected
sets, obtained by a joint iid typical set and change of measure. -/
theorem lowEntropyMass_eventual_lower (p q : ι → ℝ) (hp : ∀ i,0≤p i)
    (hq : ∀ i,0≤q i) (hqs : ∑ i,q i=1) (hSupport : ∀ i,0<q i → 0<p i)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (nhds c₀)) (hH : entropy q<c₀)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,Real.exp (-(k:ℝ)*(divergence q p+ε))≤empiricalEntropyMass p k (c k) := by
  let δ := min ((c₀-entropy q)/2) (ε/4)
  have hδ : 0<δ := lt_min (by linarith) (by linarith)
  have hgap : entropy q+δ<c₀ := by
    have h := min_le_left ((c₀-entropy q)/2) (ε/4)
    change δ≤(c₀-entropy q)/2 at h
    linarith
  have hη : 0<ε-2*δ := by
    have h := min_le_right ((c₀-entropy q)/2) (ε/4)
    change δ≤ε/4 at h
    linarith
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ)*(ε-2*δ))) atTop (nhds 0) := by
    have hlin := tendsto_natCast_atTop_atTop.atTop_mul_const hη
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext k
    congr 1
    ring
  filter_upwards [jointTypical_mass_tendsto_one p q hq hqs δ hδ |>.eventually_const_lt
      (by norm_num : (1:ℝ)/2<1),
    hc.eventually_const_lt hgap,
    hexp.eventually_lt_const (by norm_num : (0:ℝ)<1/2),eventually_gt_atTop 0]
      with k hmass hcut hsmall hk
  have hchange : wordMass q k (jointTypical p q k δ)*Real.exp (-(k:ℝ)*(divergence q p+2*δ))≤
      wordMass p k (jointTypical p q k δ) := by
    unfold wordMass
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun w hw => jointTypical_change_of_measure p q hq hSupport k δ w hw)
  have hsub : jointTypical p q k δ ⊆ lowEntropyWords k (c k) := by
    intro w hw
    have h := jointTypical_subset_lowEntropyWords p q hq hqs k hk δ hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2.trans hcut.le⟩
  calc
    _ = Real.exp (-(k:ℝ)*(ε-2*δ))*Real.exp (-(k:ℝ)*(divergence q p+2*δ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ (1/2)*Real.exp (-(k:ℝ)*(divergence q p+2*δ)) :=
      mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos _).le
    _ ≤ wordMass q k (jointTypical p q k δ)*Real.exp (-(k:ℝ)*(divergence q p+2*δ)) :=
      mul_le_mul_of_nonneg_right hmass.le (Real.exp_pos _).le
    _ ≤ wordMass p k (jointTypical p q k δ) := hchange
    _ ≤ _ := wordMass_mono p hp k hsub

end
end OperationalCompletion
