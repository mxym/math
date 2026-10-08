import ContinuumRemainder.DistinctMisses
import ContinuumGeometric.CountableExhaustion

/-!
The prescribed countable configuration family is fixed before the open set.
Only compact ranges and bounds are enumerated: l,N,j,k,q,h.  Each individual
blocker handles all real exponents in its compact interval, all translations,
and every permitted error family.  The existence statements are explicitly
conditional on `RobustCompactBlockerSpec`.
-/
namespace ContinuumRemainder

open Set MeasureTheory Filter Topology ContinuumGeometric
open scoped ENNReal

abbrev RobustBlockerIndex (ι : Type*) :=
  ι × {N : ℕ // 2 ≤ N} × {j : ℕ // 0 < j} × ℤ ×
    {q : ℕ // 0 < q} × {h : ℕ // 0 < h}

/-- Natural tails approach zero; arbitrarily late positive indices are available. -/
theorem exists_dyadic_tail (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ h : ℕ, 0 < h ∧ dyadic h < ρ := by
  have ht : Tendsto dyadic atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev := ht.eventually (gt_mem_nhds hρ)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  exact ⟨K + 1, by omega, hK _ (by omega)⟩

/-- Countable budgets cover all compact real-power ranges, remainder orders,
coefficient scales, error bounds and tails, with both coefficient signs. -/
theorem robustCompactBlockerSpec_open_exhaustion
    (hblock : RobustCompactBlockerSpec)
    {ι : Type*} [Countable ι] (A : ι → Set ℝ)
    (hA : ∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l))
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ OnePeriodic U ∧ unitDensity U < ENNReal.ofReal ε ∧
      ∀ l : ι, ∀ (s α y c M : ℝ) (f : ℝ → ℝ),
        0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
        PowerRemainderOn (A l) f y c s α M →
        ∀ ρ : ℝ, 0 < ρ → ∃ a ∈ A l, 0 < a ∧ a < ρ ∧ f a ∈ U := by
  classical
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ε := ENNReal.ofReal ε) (by positivity) (RobustBlockerIndex ι)
  have hδ₁ (i : RobustBlockerIndex ι) : (δ i : ℝ) < 1 := by
    have hi : (δ i : ENNReal) < 1 :=
      (ENNReal.le_tsum i).trans_lt (hδsum.trans (ENNReal.ofReal_lt_one.2 hε₁))
    exact_mod_cast ENNReal.coe_lt_coe.1 hi
  have hex (i : RobustBlockerIndex ι) :
      ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
        unitDensity H ≤ ENNReal.ofReal (6 * ((δ i : ℝ) / 12)) ∧
        RobustCompactHits H (A i.1) (1 / (i.2.1.1 : ℝ)) (i.2.1.1 : ℝ)
          (1 / (i.2.2.1.1 : ℝ)) i.2.2.2.1 i.2.2.2.2.1.1 i.2.2.2.2.2.1 := by
    have hN : (0 : ℝ) < i.2.1.1 := by exact_mod_cast (by have := i.2.1.2; omega : 0 < i.2.1.1)
    have hj : (0 : ℝ) < i.2.2.1.1 := by exact_mod_cast i.2.2.1.2
    apply hblock (A i.1) (hA i.1).1 (hA i.1).2
      (1 / (i.2.1.1 : ℝ)) (i.2.1.1 : ℝ) (1 / (i.2.2.1.1 : ℝ))
      (by positivity) ?_ (by positivity) i.2.2.2.1
      i.2.2.2.2.1.1 i.2.2.2.2.2.1 i.2.2.2.2.1.2 i.2.2.2.2.2.2
      ((δ i : ℝ) / 12) (by exact div_pos (hδpos i) (by norm_num))
      ((div_lt_div_iff_of_pos_right (by norm_num)).2 (hδ₁ i))
    have hN₂ : (2 : ℝ) ≤ i.2.1.1 := by exact_mod_cast i.2.1.2
    apply (div_lt_iff₀ hN).2
    nlinarith
  choose H hopen hperiod hsmall hhits using hex
  let S := fun i : RobustBlockerIndex ι => H i ∪ reflectedSet (H i)
  let U := ⋃ i, S i
  have hUo : IsOpen U := isOpen_iUnion fun i =>
    (hopen i).union ((hopen i).preimage continuous_neg)
  have hUp : OnePeriodic U := by
    intro x
    simp only [U, mem_iUnion]
    exact exists_congr fun i =>
      onePeriodic_union (hperiod i) (onePeriodic_reflectedSet (hperiod i)) x
  have hUμ : unitDensity U < ENNReal.ofReal ε := by
    calc
      unitDensity U ≤ ∑' i, unitDensity (S i) := unitDensity_iUnion_le S
      _ ≤ ∑' i, (δ i : ENNReal) := by
        apply ENNReal.tsum_le_tsum
        intro i
        calc
          unitDensity (S i) ≤ unitDensity (H i) + unitDensity (reflectedSet (H i)) :=
            unitDensity_union_le _ _
          _ = unitDensity (H i) + unitDensity (H i) := by
            rw [unitDensity_reflectedSet _ (hperiod i)]
          _ ≤ ENNReal.ofReal (6 * ((δ i : ℝ) / 12)) +
              ENNReal.ofReal (6 * ((δ i : ℝ) / 12)) := add_le_add (hsmall i) (hsmall i)
          _ = (δ i : ENNReal) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            have heq : 6 * ((δ i : ℝ) / 12) + 6 * ((δ i : ℝ) / 12) = δ i := by ring
            rw [heq, ENNReal.ofReal_coe_nnreal]
      _ < ENNReal.ofReal ε := hδsum
  refine ⟨U, hUo, hUp, hUμ, ?_⟩
  intro l s α y c M f hs hα hc hM hf ρ hρ
  obtain ⟨N, hN, hsN⟩ := exists_compact_exponent_range s hs
  obtain ⟨j, hj₂, hαj⟩ := exists_compact_exponent_range α hα
  have hj : 0 < j := by omega
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt M
  let q := q₀ + 1
  have hq : 0 < q := by simp [q]
  have hMq : M ≤ (q : ℝ) := by dsimp [q]; push_cast; linarith
  obtain ⟨σ, hσ, hrem⟩ := hf
  obtain ⟨h, hh, htail⟩ := exists_dyadic_tail (min ρ (min σ 1))
    (lt_min hρ (lt_min hσ zero_lt_one))
  have hdρ : dyadic h < ρ := htail.trans_le (min_le_left _ _)
  have hdσ : dyadic h < σ := htail.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd₁ : dyadic h < 1 := htail.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨positive, k, t, ht₀, ht₁, hceq⟩ := signed_dyadic_coefficient_cover c hc
  let i : RobustBlockerIndex ι := (l, ⟨N, hN⟩, ⟨j, hj⟩, k, ⟨q, hq⟩, ⟨h, hh⟩)
  have he : ∀ a ∈ A l, 0 < a → a < dyadic h →
      |f a - y - c * a ^ s| ≤ (q : ℝ) * a ^ (s + 1 / (j : ℝ)) := by
    intro a ha ha₀ hah
    have ha₁ : a ≤ 1 := (hah.trans hd₁).le
    have hrpow : a ^ (s + α) ≤ a ^ (s + 1 / (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ha₀ ha₁ (add_le_add le_rfl hαj.1)
    calc
      |f a - y - c * a ^ s| ≤ M * a ^ (s + α) :=
        hrem a ha ha₀ (hah.trans hdσ)
      _ ≤ (q : ℝ) * a ^ (s + 1 / (j : ℝ)) :=
        mul_le_mul hMq hrpow (Real.rpow_nonneg ha₀.le _) (by positivity)
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at hceq
    obtain ⟨a, ha, ha₀, hah, hhit⟩ := hhits i (-y) s t
      (fun a => -(f a - y - c * a ^ s)) hsN ⟨ht₀, ht₁.le⟩ (by
        intro a ha ha₀ hah
        simpa only [abs_neg] using he a ha ha₀ hah)
    have hpoint : -y + t * (2 : ℝ) ^ k * a ^ s - (f a - y - c * a ^ s) = -f a := by
      rw [hceq]; ring
    change -y + t * (2 : ℝ) ^ k * a ^ s - (f a - y - c * a ^ s) ∈ H i at hhit
    rw [hpoint] at hhit
    refine ⟨a, ha, ha₀, hah.trans hdρ, mem_iUnion.2 ⟨i, Or.inr ?_⟩⟩
    exact hhit
  · simp only [↓reduceIte, one_mul] at hceq
    obtain ⟨a, ha, ha₀, hah, hhit⟩ := hhits i y s t
      (fun a => f a - y - c * a ^ s) hsN ⟨ht₀, ht₁.le⟩ he
    have hpoint : y + t * (2 : ℝ) ^ k * a ^ s + (f a - y - c * a ^ s) = f a := by
      rw [hceq]; ring
    rw [hpoint] at hhit
    exact ⟨a, ha, ha₀, hah.trans hdρ, mem_iUnion.2 ⟨i, Or.inl hhit⟩⟩

end ContinuumRemainder
