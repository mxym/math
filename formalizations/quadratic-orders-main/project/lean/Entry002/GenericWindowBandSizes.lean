import Entry002.GenericWindowEntropy

/-! Positivity and capacity of the actual middle and bottom window batches.
The numerical guards are discharged by actual dyadic density before all walks.
-/
set_option autoImplicit false
namespace Entry002
open Module Filter
open OAI.GaussianMoat
open scoped Classical
variable {L : Type*} [AddCommGroup L]

private lemma window_band_size_positive {μ g U X : ℝ} {l : ℕ}
    (hμ : 0<μ) (hμup : μ≤2*X) (hg : 0≤g) (hg1 : g≤1)
    (hlarge : 1280*X≤g^5*bandScale g U l) : 0<bandSize μ g U l := by
  have hX : 0<X := by linarith only [hμ,hμup]
  have hV : 0<bandScale g U l := by
    nlinarith only [hlarge,hX,pow_nonneg hg 5]
  have hpow : g^5≤1 := pow_le_one₀ hg hg1
  have hp := mul_le_mul_of_nonneg_right hpow hV.le
  have hlow : μ≤bandScale g U l := by nlinarith only [hlarge,hμup,hp,hX]
  apply Nat.floor_pos.mpr
  exact (le_div_iff₀ hμ).mpr (by simpa only [one_mul] using hlow)

theorem eventually_window_band_sizes (data : SignedResidueData L)
    {δ : ℝ} (hδ : 0<δ) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀i<W,∀j∈J i,(100:ℝ)^i*Real.exp m≤(j:ℝ)*Real.log 2 ∧
        (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card) →
      ∀j∈J w,
      let S := dyadicPrimeBatch data.primes j
      let μ := FreshEntropy.batchMeanLog S
      let qmid := bandSize μ (accurateGrid m)
        (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m)
      let qbot := bandSize μ (accurateGrid m)
        (Real.exp ((1/20)*Real.exp m)) (accurateIterations m)
      0<qmid ∧ qmid≤S.card ∧ 0<qbot ∧ qbot≤S.card := by
  have hp : (0:ℝ)<100^w := by positivity
  have hmid := eventually_accurate_actual_batch_guards
    (A := (100:ℝ)^w) (B := 2*(100:ℝ)^w) (a := (100:ℝ)^w/4)
    hp (by positivity) (by positivity) (by linarith only [hp]) hδ 0
  have hbot := eventually_accurate_actual_batch_guards
    (A := 1) (B := 2*(100:ℝ)^w) (a := 1/20)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) hδ 0
  filter_upwards [hmid,hbot] with m hmid hbot
  intro J hJ j hj
  have hdata := hJ w hw j hj
  let S := dyadicPrimeBatch data.primes j
  have hne : S.Nonempty := dyadicPrimeBatch_nonempty_of_dense data.primes j hδ hdata.2.2
  have hpT : ∀p∈S,(2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j := by
    intro p hp
    exact ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩
  have hdense : δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤S.card := by
    simpa only [pow_succ,mul_comm] using hdata.2.2
  have hT : Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m := by
    rw [Real.log_pow]
    nlinarith only [hdata.2.1,show 0≤(100:ℝ)^w*Real.exp m by positivity]
  obtain ⟨_,hm,hmu,hgm⟩ := hmid S ((2:ℝ)^j) hne hpT hdense hT hThi
  obtain ⟨_,hb,hbu,hgb⟩ := hbot S ((2:ℝ)^j) hne hpT hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [window_power_one w,Real.exp_pos (m:ℝ)] :
      1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT) hThi
  let X := (2*(100:ℝ)^w+1)*Real.exp m
  have hposmid := window_band_size_positive (by linarith only [hm]) hmu
    (accurateGrid_pos m).le (accurateGrid_le_one m)
    (hgm (accurateIterations m) le_rfl).2.1
  have hposbot := window_band_size_positive (by linarith only [hb]) hbu
    (accurateGrid_pos m).le (accurateGrid_le_one m)
    (hgb (accurateIterations m) le_rfl).2.1
  exact ⟨hposmid,(hgm (accurateIterations m) le_rfl).2.2,
    hposbot,(hgb (accurateIterations m) le_rfl).2.2⟩

end Entry002
