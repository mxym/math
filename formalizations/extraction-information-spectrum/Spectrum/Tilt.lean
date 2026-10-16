import Spectrum.Direct

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteSumEvent (q f : ι → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ w : Fin k → ι, if (∑ j, f (w j)) ≤ x then iidLaw q k w else 0

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finiteSumEvent_eq_measure (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (f : ι → ℝ) (k : ℕ) (x : ℝ) :
    finiteSumEvent q f k x = (iidMeasure q hq hs).real
      {w | (∑ j ∈ Finset.range k, f (w j)) ≤ x} := by
  have h := (iid_window_hasLaw q hq hs k).measureReal_eq
    (p := fun w : Fin k → ι => (∑ j, f (w j)) ≤ x) (Set.toFinite _).measurableSet
  rw [finiteMeasure_pi, finiteMeasure_real_event] at h
  change (iidMeasure q hq hs).real {w | (∑ j : Fin k, f (w j)) ≤ x} =
    finiteSumEvent q f k x at h
  have he : {w : ℕ → ι | (∑ j : Fin k, f (w j)) ≤ x} =
      {w | (∑ j ∈ Finset.range k, f (w j)) ≤ x} := by
    ext w
    change (∑ j : Fin k, f (w j)) ≤ x ↔ _
    rw [Fin.sum_univ_eq_sum_range (fun j => f (w j)) k]
    rfl
  rw [he] at h
  exact h.symm

theorem finiteSumEvent_law_of_large_numbers (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (f : ι → ℝ) (c : ℝ) (hc : c ≠ finiteMean q f) :
    Tendsto (fun k : ℕ => finiteSumEvent q f k ((k : ℝ) * c)) atTop
      (𝓝 (if finiteMean q f < c then 1 else 0)) := by
  have he (k : ℕ) (hk : 0 < k) : finiteSumEvent q f k ((k : ℝ) * c) =
      (iidMeasure q hq hs).real
        {w | (∑ j ∈ Finset.range k, f (w j)) / k ≤ c} := by
    rw [finiteSumEvent_eq_measure q hq hs]
    congr 2
    ext w
    change (∑ j ∈ Finset.range k, f (w j)) ≤ (k : ℝ) * c ↔ _
    rw [div_le_iff₀ (Nat.cast_pos.mpr hk)]
    constructor <;> intro h <;> nlinarith
  by_cases hgt : finiteMean q f < c
  · simp only [hgt, ite_true]
    apply (finite_iid_average_upper_tail q hq hs f c hgt).congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (he k hk).symm
  · have hlt : c < finiteMean q f := lt_of_le_of_ne (le_of_not_gt hgt) hc
    simp only [hgt, ite_false]
    apply (finite_iid_average_lower_tail q hq hs f c hlt).congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (he k hk).symm

def finiteTypicalBand (q f : ι → ℝ) (k : ℕ) (δ : ℝ) : Finset (Fin k → ι) :=
  Finset.univ.filter (fun w => 0 < iidLaw q k w ∧
    (k : ℝ) * (finiteMean q f - δ) < (∑ j, f (w j)) ∧
      (∑ j, f (w j)) ≤ (k : ℝ) * (finiteMean q f + δ))

def finiteBandMass (p q f : ι → ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  ∑ w ∈ finiteTypicalBand q f k δ, iidLaw p k w

theorem finiteBandMass_self_eq_difference (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (f : ι → ℝ) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    finiteBandMass q q f k δ =
      finiteSumEvent q f k ((k : ℝ) * (finiteMean q f + δ)) -
        finiteSumEvent q f k ((k : ℝ) * (finiteMean q f - δ)) := by
  unfold finiteBandMass finiteTypicalBand finiteSumEvent
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have hnn := iidLaw_nonneg q hq k w
  have hcut : (k : ℝ) * (finiteMean q f - δ) ≤ (k : ℝ) * (finiteMean q f + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
  by_cases hw : 0 < iidLaw q k w
  · by_cases hl : (∑ j, f (w j)) ≤ (k : ℝ) * (finiteMean q f - δ)
    · have hu := hl.trans hcut
      simp only [hw, true_and, hu, hl, not_lt_of_ge hl, false_and,
        ite_false, ite_true, sub_self]
    · have hlow := lt_of_not_ge hl
      by_cases hu : (∑ j, f (w j)) ≤ (k : ℝ) * (finiteMean q f + δ) <;>
        simp only [hw, true_and, hu, hl, hlow, true_and, ite_false, ite_true, sub_zero]
  · have hz := le_antisymm (le_of_not_gt hw) hnn
    simp only [hz, ite_self, sub_self]

/-- The typical band has asymptotically full mass under its actual finite
iid sampling law. The finite word event and the strong law are connected. -/
theorem finiteBandMass_self_tendsto_one (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (f : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k => finiteBandMass q q f k δ) atTop (𝓝 1) := by
  have hl := finiteSumEvent_law_of_large_numbers q hq hs f (finiteMean q f - δ)
    (by linarith)
  have hu := finiteSumEvent_law_of_large_numbers q hq hs f (finiteMean q f + δ)
    (by linarith)
  simp only [show ¬finiteMean q f < finiteMean q f - δ by linarith, ite_false] at hl
  simp only [show finiteMean q f < finiteMean q f + δ by linarith, ite_true] at hu
  have h := hu.sub hl
  simpa only [sub_zero, ← finiteBandMass_self_eq_difference q hq f _ δ hδ.le] using h

theorem escort_nonneg_of_normalized (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (i : ι) : 0 ≤ escort p α i :=
  div_nonneg (Real.rpow_nonneg (hp i) α) (partition_pos_of_normalized p hp hs α).le

/-- Entropy and cross entropy are related by the actual escort density,
including all zero coordinates of the original law. -/
theorem escort_entropy_information_identity (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α) :
    entropy (escort p α) = α * finiteMean (escort p α) (selfInformation p) +
      Real.log (partition p α) := by
  have hZ := partition_pos_of_normalized p hp hs α
  have he (i : ι) : escort p α i * (-Real.log (escort p α i)) =
      α * (escort p α i * (-Real.log (p i))) + escort p α i * Real.log (partition p α) := by
    by_cases hi : p i = 0
    · have hz : escort p α i = 0 := by
        simp only [escort, hi, Real.zero_rpow (ne_of_gt hα), zero_div]
      simp only [hz, zero_mul, mul_zero, add_zero]
    · have hpi := lt_of_le_of_ne (hp i) (Ne.symm hi)
      have hl : Real.log (escort p α i) = α * Real.log (p i) - Real.log (partition p α) := by
        rw [escort, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hpi α))
          (ne_of_gt hZ), Real.log_rpow hpi]
      rw [hl]
      ring
  simp only [entropy, finiteMean, selfInformation, he, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, escort_sum_of_normalized p hp hs α, one_mul]

theorem escort_word_letters_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    {k : ℕ} (w : Fin k → ι) (hw : 0 < iidLaw (escort p α) k w) (j : Fin k) :
    0 < p (w j) := by
  have hq := iidLaw_letters_pos (escort p α) (escort_nonneg_of_normalized p hp hs α) w hw j
  apply lt_of_le_of_ne (hp _) (Ne.symm _)
  intro hz
  have he : escort p α (w j) = 0 := by
    simp only [escort, hz, Real.zero_rpow (ne_of_gt hα), zero_div]
  rw [he] at hq
  exact (lt_irrefl 0) hq

theorem iidLaw_eq_exp_sum_of_pos (p : ι → ℝ) {k : ℕ} (w : Fin k → ι)
    (hp : ∀ j, 0 < p (w j)) :
    iidLaw p k w = Real.exp (-(∑ j, selfInformation p (w j))) := by
  simp only [selfInformation, Finset.sum_neg_distrib, neg_neg, Real.exp_sum, iidLaw]
  apply Finset.prod_congr rfl
  intro j _
  exact (Real.exp_log (hp j)).symm

/-- Exact change of density at every positive-mass escort word. The iid
likelihood ratio is derived from the original normalized finite law. -/
theorem escort_word_likelihood_exp (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    {k : ℕ} (w : Fin k → ι) (hw : 0 < iidLaw (escort p α) k w) :
    iidLaw (escort p α) k w = Real.exp
      (-α * (∑ j, selfInformation p (w j)) - (k : ℝ) * Real.log (partition p α)) := by
  have hZ := partition_pos_of_normalized p hp hs α
  have hj (j : Fin k) : escort p α (w j) =
      Real.exp (-α * selfInformation p (w j) - Real.log (partition p α)) := by
    have hpi := escort_word_letters_pos p hp hs α hα w hw j
    rw [escort, Real.rpow_def_of_pos hpi, ← Real.exp_log hZ, ← Real.exp_sub]
    congr 1
    simp only [Real.log_exp]
    unfold selfInformation
    ring
  unfold iidLaw
  simp_rw [hj]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem escort_word_likelihood_ratio (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    {k : ℕ} (w : Fin k → ι) (hw : 0 < iidLaw (escort p α) k w) :
    iidLaw p k w = iidLaw (escort p α) k w * Real.exp
      ((α - 1) * (∑ j, selfInformation p (w j)) + (k : ℝ) * Real.log (partition p α)) := by
  rw [iidLaw_eq_exp_sum_of_pos p w (escort_word_letters_pos p hp hs α hα w hw),
    escort_word_likelihood_exp p hp hs α hα w hw, ← Real.exp_add]
  congr 1
  ring

/-- Every word in the escort typical band has the required pointwise
likelihood lower bound under the escort itself. -/
theorem escort_band_word_likelihood_lower (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    (k : ℕ) (δ : ℝ) (w : Fin k → ι)
    (hw : w ∈ finiteTypicalBand (escort p α) (selfInformation p) k δ) :
    Real.exp (-(k : ℝ) * (entropy (escort p α) + α * δ)) ≤
      iidLaw (escort p α) k w := by
  have hband := (Finset.mem_filter.mp hw).2
  rw [escort_word_likelihood_exp p hp hs α hα w hband.1]
  apply Real.exp_le_exp.mpr
  rw [escort_entropy_information_identity p hp hs α hα]
  have h := mul_le_mul_of_nonneg_left hband.2.2 hα.le
  nlinarith

/-- Exact change of density and the band deviation bound give a likelihood
ratio lower bound. Absolute value handles both direct and converse tilts. -/
theorem escort_band_word_change_of_measure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    (k : ℕ) (δ : ℝ) (w : Fin k → ι)
    (hw : w ∈ finiteTypicalBand (escort p α) (selfInformation p) k δ) :
    iidLaw (escort p α) k w * Real.exp (-(k : ℝ) *
      (divergence (escort p α) p + |α - 1| * δ)) ≤ iidLaw p k w := by
  have hband := (Finset.mem_filter.mp hw).2
  rw [escort_word_likelihood_ratio p hp hs α hα w hband.1]
  apply mul_le_mul_of_nonneg_left _ hband.1.le
  apply Real.exp_le_exp.mpr
  let M := finiteMean (escort p α) (selfInformation p)
  let S := ∑ j, selfInformation p (w j)
  have hdev : |S - (k : ℝ) * M| ≤ (k : ℝ) * δ := by
    apply abs_le.mpr
    dsimp [S, M]
    constructor <;> nlinarith [hband.2.1, hband.2.2]
  have hmul := mul_le_mul_of_nonneg_left hdev (abs_nonneg (α - 1))
  rw [← abs_mul] at hmul
  have hneg := neg_abs_le ((α - 1) * (S - (k : ℝ) * M))
  have hcross := cross_entropy_eq_entropy_add_divergence (escort p α) p
  change M = entropy (escort p α) + divergence (escort p α) p at hcross
  rw [escort_entropy_information_identity p hp hs α hα] at hcross
  have hD : divergence (escort p α) p = (1 - α) * M - Real.log (partition p α) := by
    change M = α * M + Real.log (partition p α) + divergence (escort p α) p at hcross
    linarith
  rw [hD]
  change -(k : ℝ) * ((1 - α) * M - Real.log (partition p α) + |α - 1| * δ) ≤
    (α - 1) * S + (k : ℝ) * Real.log (partition p α)
  nlinarith

/-- The actual escort typical band has at most exp(k(H(q)+alpha*delta)) words.
Its cardinal estimate is derived from positive pointwise likelihoods and
total probability one, retaining zero coordinates of p. -/
theorem escort_typicalBand_card_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α) (k : ℕ) (δ : ℝ) :
    ((finiteTypicalBand (escort p α) (selfInformation p) k δ).card : ℝ) ≤
      Real.exp ((k : ℝ) * (entropy (escort p α) + α * δ)) := by
  let A := finiteTypicalBand (escort p α) (selfInformation p) k δ
  have hmass : ∑ w ∈ A, iidLaw (escort p α) k w ≤ 1 := by
    calc
      _ ≤ ∑ w : Fin k → ι, iidLaw (escort p α) k w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => iidLaw_nonneg _ (escort_nonneg_of_normalized p hp hs α) k w)
      _ = 1 := iidLaw_sum _ (escort_sum_of_normalized p hp hs α) k
  have hlower : ((A.card : ℕ) : ℝ) *
      Real.exp (-(k : ℝ) * (entropy (escort p α) + α * δ)) ≤ 1 := by
    calc
      _ = ∑ _w ∈ A, Real.exp (-(k : ℝ) * (entropy (escort p α) + α * δ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ A, iidLaw (escort p α) k w :=
        Finset.sum_le_sum fun w hw => escort_band_word_likelihood_lower p hp hs α hα k δ w hw
      _ ≤ 1 := hmass
  have h := mul_le_mul_of_nonneg_right hlower
    (Real.exp_pos ((k : ℝ) * (entropy (escort p α) + α * δ))).le
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel,
    Real.exp_zero, mul_one, one_mul] using h

/-- The escort typical band has the required mass in the original law;
the finite likelihood comparison is summed without a large-deviation premise. -/
theorem escort_typicalBand_mass_lower (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α) (k : ℕ) (δ : ℝ) :
    finiteBandMass (escort p α) (escort p α) (selfInformation p) k δ *
      Real.exp (-(k : ℝ) * (divergence (escort p α) p + |α - 1| * δ)) ≤
        finiteBandMass p (escort p α) (selfInformation p) k δ := by
  unfold finiteBandMass
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun w hw => escort_band_word_change_of_measure p hp hs α hα k δ w hw

/-- The lower bound's prefactor is asymptotically one under the internally
constructed iid escort law. -/
theorem escort_typicalBand_escort_mass_tendsto_one (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k => finiteBandMass (escort p α) (escort p α) (selfInformation p) k δ)
      atTop (𝓝 1) := by
  exact finiteBandMass_self_tendsto_one (escort p α) (escort_nonneg_of_normalized p hp hs α)
    (escort_sum_of_normalized p hp hs α) (selfInformation p) δ hδ

/-- The full-mass prefactor can be absorbed into an arbitrarily small
exponential loss, without taking logarithms of a zero probability. -/
theorem escort_typicalBand_mass_eventual_lower (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α)
    (δ : ℝ) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (-(k : ℝ) * (divergence (escort p α) p + |α - 1| * δ + η)) ≤
        finiteBandMass p (escort p α) (selfInformation p) k δ := by
  have hq := escort_typicalBand_escort_mass_tendsto_one p hp hs α hα δ hδ
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ) * η)) atTop (𝓝 0) := by
    have hlin := tendsto_natCast_atTop_atTop.atTop_mul_const hη
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext k
    congr 1
    ring
  filter_upwards [hq.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hexp.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)] with k hk he
  calc
    _ = Real.exp (-(k : ℝ) * η) *
        Real.exp (-(k : ℝ) * (divergence (escort p α) p + |α - 1| * δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ finiteBandMass (escort p α) (escort p α) (selfInformation p) k δ *
        Real.exp (-(k : ℝ) * (divergence (escort p α) p + |α - 1| * δ)) :=
      mul_le_mul_of_nonneg_right (he.trans hk).le (Real.exp_pos _).le
    _ ≤ _ := escort_typicalBand_mass_lower p hp hs α hα k δ

/-- Actual finite subsets realizing the escort entropy/divergence tradeoff.
The subsets and their limiting probability behavior are constructed, not
provided as an asymptotic hypothesis. Zero coordinates of p remain allowed. -/
theorem escort_typical_subsets (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : (k : ℕ) → Finset (Fin k → ι),
      (∀ k, ((A k).card : ℝ) ≤ Real.exp ((k : ℝ) * (entropy (escort p α) + ε))) ∧
      (∀ᶠ k : ℕ in atTop,
        Real.exp (-(k : ℝ) * (divergence (escort p α) p + ε)) ≤
          ∑ w ∈ A k, iidLaw p k w) := by
  let δ := ε / (2 * (α + |α - 1| + 1))
  have hden : 0 < 2 * (α + |α - 1| + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * (2 * (α + |α - 1| + 1)) = ε := by
    dsimp [δ]
    field_simp
  have ha : α * δ ≤ ε := by
    have hpos := mul_nonneg (abs_nonneg (α - 1)) hδ.le
    nlinarith
  have hb : |α - 1| * δ + ε / 2 ≤ ε := by
    have hpos := mul_nonneg hα.le hδ.le
    nlinarith
  refine ⟨fun k => finiteTypicalBand (escort p α) (selfInformation p) k δ, ?_, ?_⟩
  · intro k
    exact (escort_typicalBand_card_le p hp hs α hα k δ).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith :
        entropy (escort p α) + α * δ ≤ entropy (escort p α) + ε) (Nat.cast_nonneg k)))
  · filter_upwards [escort_typicalBand_mass_eventual_lower p hp hs α hα δ hδ
      (ε / 2) (by positivity)] with k hk
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (by linarith : divergence (escort p α) p + |α - 1| * δ + ε / 2 ≤
        divergence (escort p α) p + ε) (neg_nonpos.mpr (Nat.cast_nonneg k)))).trans hk

/-- The attaining trial vector in escort weak duality can be chosen to be
the escort at the very same parameter, including endpoint parameters. -/
theorem escort_parameter_primal_dual_attainment [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (c : ℝ) :
    ∃ α ∈ Set.Icc (1 : ℝ) 2,
      primalObjective p c (escort p α) = dualObjective p c α := by
  by_cases hpc : entropy p ≤ c
  · refine ⟨1, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [escort_one p hs, dualObjective_one p hs]
    simp only [primalObjective, divergence_self, max_eq_left (sub_nonpos.mpr hpc),
      zero_div, add_zero]
  · by_cases h2 : c ≤ entropy (escort p 2)
    · exact ⟨2, ⟨by norm_num, le_rfl⟩, escort_primal_dual_at_two p hp c h2⟩
    · have hI : c ∈ Set.Icc (entropy (escort p 2)) (entropy (escort p 1)) := by
        rw [escort_one p hs]
        exact ⟨(lt_of_not_ge h2).le, (lt_of_not_ge hpc).le⟩
      obtain ⟨α, hα, hH⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2)
        (escort_entropy_continuous p hp).continuousOn hI
      exact ⟨α, hα, escort_primal_dual_of_entropy_eq p hp c α
        (lt_of_lt_of_le zero_lt_one hα.1) hH⟩

theorem escort_restrict_positive_support [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (α : ℝ) (hα : 0 < α) :
    (fun i : PositiveSupport p => escort p α i.1) = escort (supportLaw p) α := by
  have hpart : partition (supportLaw p) α = partition p α :=
    positiveSupport_sum p hp (fun x => x ^ α) (Real.zero_rpow (ne_of_gt hα))
  ext i
  simp only [escort, supportLaw, hpart]

theorem escort_support_entropy [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (α : ℝ) (hα : 0 < α) :
    entropy (escort (supportLaw p) α) = entropy (escort p α) := by
  rw [← escort_restrict_positive_support p hp α hα]
  unfold entropy finiteMean selfInformation
  exact positiveSupport_sum p hp
    (fun x => (x ^ α / partition p α) * (-Real.log (x ^ α / partition p α)))
    (by simp only [Real.zero_rpow (ne_of_gt hα), zero_div, zero_mul])

theorem escort_support_divergence [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (α : ℝ) (hα : 0 < α) :
    divergence (escort (supportLaw p) α) (supportLaw p) = divergence (escort p α) p := by
  rw [← escort_restrict_positive_support p hp α hα]
  unfold divergence
  exact positiveSupport_sum p hp
    (fun x => (x ^ α / partition p α) * (Real.log (x ^ α / partition p α) - Real.log x))
    (by simp only [Real.zero_rpow (ne_of_gt hα), zero_div, zero_mul])

/-- A full-law escort attains the exact positive-support variational value.
This bridges the scalar optimization and the original finite iid likelihoods. -/
theorem nonnegative_escort_primal_attainment [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ) :
    ∃ α ∈ Set.Icc (1 : ℝ) 2,
      (⨅ q : ProbabilityVector (PositiveSupport p), primalObjective (supportLaw p) c q.1) =
        primalObjective p c (escort p α) := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  obtain ⟨α, hα, he⟩ := escort_parameter_primal_dual_attainment (supportLaw p)
    (fun i => i.2) (supportLaw_sum p hp hs) c
  let q0 : ProbabilityVector (PositiveSupport p) :=
    ⟨escort (supportLaw p) α, (fun i => (escort_pos (supportLaw p) (fun i => i.2) α i).le),
      escort_sum (supportLaw p) (fun i => i.2) α⟩
  letI : Nonempty (ProbabilityVector (PositiveSupport p)) := ⟨q0⟩
  have hlower (q : ProbabilityVector (PositiveSupport p)) :
      primalObjective (supportLaw p) c (escort (supportLaw p) α) ≤
        primalObjective (supportLaw p) c q.1 := by
    rw [he]
    exact escort_variational_lower (supportLaw p) q.1 (fun i => i.2) q.2.1 q.2.2 c α hα
  have hB : BddBelow (Set.range (fun q : ProbabilityVector (PositiveSupport p) =>
      primalObjective (supportLaw p) c q.1)) := by
    refine ⟨primalObjective (supportLaw p) c (escort (supportLaw p) α), ?_⟩
    rintro v ⟨q, rfl⟩
    exact hlower q
  have hInf : (⨅ q : ProbabilityVector (PositiveSupport p),
      primalObjective (supportLaw p) c q.1) =
        primalObjective (supportLaw p) c (escort (supportLaw p) α) :=
    le_antisymm (ciInf_le hB q0) (le_ciInf hlower)
  refine ⟨α, hα, ?_⟩
  rw [hInf]
  unfold primalObjective
  rw [escort_support_entropy p hp α (lt_of_lt_of_le zero_lt_one hα.1),
    escort_support_divergence p hp α (lt_of_lt_of_le zero_lt_one hα.1)]

/-- Optimized typical subsets give all classical input needed for the
matching fidelity-exponent lower bound. The parameter, subsets, exact
variational value, integer cardinality bound, and mass exponent are proved. -/
theorem optimized_escort_typical_subsets [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (c ε : ℝ) (hε : 0 < ε) :
    ∃ α ∈ Set.Icc (1 : ℝ) 2, ∃ A : (k : ℕ) → Finset (Fin k → ι),
      ((⨅ q : ProbabilityVector (PositiveSupport p), primalObjective (supportLaw p) c q.1) =
        primalObjective p c (escort p α)) ∧
      (∀ k, ((A k).card : ℝ) ≤ Real.exp ((k : ℝ) * (entropy (escort p α) + ε))) ∧
      (∀ᶠ k : ℕ in atTop,
        Real.exp (-(k : ℝ) * (divergence (escort p α) p + ε)) ≤
          ∑ w ∈ A k, iidLaw p k w) := by
  obtain ⟨α, hα, hopt⟩ := nonnegative_escort_primal_attainment p hp hs c
  obtain ⟨A, hcard, hmass⟩ := escort_typical_subsets p hp hs α
    (lt_of_lt_of_le zero_lt_one hα.1) ε hε
  exact ⟨α, hα, A, hopt, hcard, hmass⟩

end
end ExtractionSpectrum
