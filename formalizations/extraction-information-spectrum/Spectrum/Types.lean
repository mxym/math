import Spectrum.Variational
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators Classical Topology
open Filter

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordCount {k : ℕ} (w : Fin k → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun j => w j = i)).card

theorem wordCount_le {k : ℕ} (w : Fin k → ι) (i : ι) : wordCount w i ≤ k := by
  simpa only [Finset.card_univ, Fintype.card_fin, wordCount] using
    Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun j => w j = i)

def wordType {k : ℕ} (w : Fin k → ι) : ι → Fin (k + 1) :=
  fun i => ⟨wordCount w i, Nat.lt_succ_of_le (wordCount_le w i)⟩

def empiricalLaw {k : ℕ} (w : Fin k → ι) (i : ι) : ℝ :=
  wordCount w i / k

theorem wordCount_sum {k : ℕ} (w : Fin k → ι) : ∑ i, wordCount w i = k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin k))) (t := Finset.univ) (f := w) (by simp)
  simpa only [Finset.card_univ, Fintype.card_fin, wordCount] using h.symm

theorem word_sum_by_counts {k : ℕ} (w : Fin k → ι) (f : ι → ℝ) :
    ∑ j, f (w j) = ∑ i, (wordCount w i : ℝ) * f i := by
  rw [← Finset.sum_fiberwise Finset.univ w (fun j => f (w j))]
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ j ∈ Finset.univ.filter (fun j => w j = i), f (w j) =
        ∑ j ∈ Finset.univ.filter (fun j => w j = i), f i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, wordCount]

theorem empiricalLaw_nonneg {k : ℕ} (w : Fin k → ι) (i : ι) :
    0 ≤ empiricalLaw w i := by unfold empiricalLaw; positivity

theorem empiricalLaw_sum {k : ℕ} (hk : 0 < k) (w : Fin k → ι) :
    ∑ i, empiricalLaw w i = 1 := by
  simp only [empiricalLaw, ← Finset.sum_div, ← Nat.cast_sum, wordCount_sum]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr hk))

theorem empiricalLaw_eq_of_wordType_eq {k : ℕ} (v w : Fin k → ι)
    (h : wordType v = wordType w) : empiricalLaw v = empiricalLaw w := by
  ext i
  have hi := congrArg (fun t : ι → Fin (k + 1) => (t i).val) h
  change wordCount v i = wordCount w i at hi
  simp only [empiricalLaw, hi]

theorem wordCount_at_pos {k : ℕ} (w : Fin k → ι) (j : Fin k) :
    0 < wordCount w (w j) := by
  apply Finset.card_pos.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem empiricalLaw_at_pos {k : ℕ} (hk : 0 < k) (w : Fin k → ι) (j : Fin k) :
    0 < empiricalLaw w (w j) :=
  div_pos (Nat.cast_pos.mpr (wordCount_at_pos w j)) (Nat.cast_pos.mpr hk)

/-- Weighted self-information of an empirical law is exactly its word sum. -/
theorem empirical_cross_entropy {k : ℕ} (hk : 0 < k) (w : Fin k → ι) (p : ι → ℝ) :
    (k : ℝ) * (∑ i, empiricalLaw w i * (-Real.log (p i))) =
      ∑ j, -Real.log (p (w j)) := by
  rw [word_sum_by_counts w (fun i => -Real.log (p i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold empiricalLaw
  field_simp

/-- Exact word likelihood expressed by its empirical cross entropy. Positivity
is required only at the letters that actually occur in the word. -/
theorem word_likelihood_eq_exp {k : ℕ} (hk : 0 < k)
    (w : Fin k → ι) (p : ι → ℝ) (hp : ∀ j, 0 < p (w j)) :
    iidLaw p k w = Real.exp (-(k : ℝ) *
      (∑ i, empiricalLaw w i * (-Real.log (p i)))) := by
  have he := empirical_cross_entropy hk w p
  have he' : -(k : ℝ) * (∑ i, empiricalLaw w i * (-Real.log (p i))) =
      ∑ j, Real.log (p (w j)) := by
    rw [neg_mul, he, Finset.sum_neg_distrib, neg_neg]
  rw [he', Real.exp_sum]
  unfold iidLaw
  apply Finset.prod_congr rfl
  intro j _
  exact (Real.exp_log (hp j)).symm

def typeClass {k : ℕ} (w : Fin k → ι) : Finset (Fin k → ι) :=
  Finset.univ.filter (fun v => wordType v = wordType w)

/-- Every word in an empirical type has the same likelihood under that
empirical law. This retains all zero, absent letters. -/
theorem typeClass_likelihood {k : ℕ} (hk : 0 < k)
    (v w : Fin k → ι) (h : v ∈ typeClass w) :
    iidLaw (empiricalLaw w) k v = Real.exp (-(k : ℝ) * entropy (empiricalLaw w)) := by
  have hvw := empiricalLaw_eq_of_wordType_eq v w (Finset.mem_filter.mp h).2
  have hp (j : Fin k) : 0 < empiricalLaw w (v j) := by
    rw [← hvw]
    exact empiricalLaw_at_pos hk v j
  rw [word_likelihood_eq_exp hk v _ hp]
  simp only [hvw, entropy, finiteMean, selfInformation]

/-- A type contains at most exp(k H(q)) words. The proof uses the exact
likelihood and the total mass one of q's actual iid law, not Stirling bounds. -/
theorem typeClass_card_le {k : ℕ} (hk : 0 < k) (w : Fin k → ι) :
    ((typeClass w).card : ℝ) ≤ Real.exp ((k : ℝ) * entropy (empiricalLaw w)) := by
  have hmass : ∑ v ∈ typeClass w, iidLaw (empiricalLaw w) k v ≤ 1 := by
    calc
      ∑ v ∈ typeClass w, iidLaw (empiricalLaw w) k v ≤
          ∑ v : Fin k → ι, iidLaw (empiricalLaw w) k v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ => iidLaw_nonneg _ (empiricalLaw_nonneg w) k v)
      _ = 1 := iidLaw_sum _ (empiricalLaw_sum hk w) k
  have he : (∑ v ∈ typeClass w, iidLaw (empiricalLaw w) k v) =
      ((typeClass w).card : ℝ) * Real.exp (-(k : ℝ) * entropy (empiricalLaw w)) := by
    calc
      _ = ∑ _v ∈ typeClass w, Real.exp (-(k : ℝ) * entropy (empiricalLaw w)) :=
        Finset.sum_congr rfl fun v hv => typeClass_likelihood hk v w hv
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he] at hmass
  have h := mul_le_mul_of_nonneg_right hmass
    (Real.exp_pos ((k : ℝ) * entropy (empiricalLaw w))).le
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero,
    mul_one, one_mul] using h

def lowEntropyWords (k : ℕ) (c : ℝ) : Finset (Fin k → ι) :=
  Finset.univ.filter (fun w => entropy (empiricalLaw w) ≤ c)

/-- There are at most (k+1)^D possible empirical types, without a factorial
or an asymptotic estimate. -/
theorem wordType_range_card_le (k : ℕ) :
    (Finset.univ.image (wordType (ι := ι) (k := k))).card ≤
      (k + 1) ^ Fintype.card ι := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Finset.card_le_univ (Finset.univ.image (wordType (ι := ι) (k := k)))

/-- The complete low-empirical-entropy cardinal estimate used for a
state-independent compression subspace. The alphabet is arbitrary finite,
and k=0 is included. -/
theorem lowEntropyWords_card_le (k : ℕ) (c : ℝ) :
    ((lowEntropyWords (ι := ι) k c).card : ℝ) ≤
      ((k + 1 : ℝ) ^ Fintype.card ι) * Real.exp ((k : ℝ) * c) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa only [Nat.cast_zero, zero_add, one_pow, zero_mul, Real.exp_zero, mul_one,
      Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ (lowEntropyWords (ι := ι) 0 c))
  · let S := lowEntropyWords (ι := ι) k c
    have hcount : S.card = ∑ t : ι → Fin (k + 1),
        (S.filter (fun w => wordType w = t)).card :=
      Finset.card_eq_sum_card_fiberwise (by simp)
    have hfiber (t : ι → Fin (k + 1)) :
        ((S.filter (fun w => wordType w = t)).card : ℝ) ≤ Real.exp ((k : ℝ) * c) := by
      by_cases hempty : (S.filter (fun w => wordType w = t)).Nonempty
      · obtain ⟨w, hw⟩ := hempty
        have hwt := (Finset.mem_filter.mp hw).2
        have hwS := (Finset.mem_filter.mp hw).1
        have hH : entropy (empiricalLaw w) ≤ c := (Finset.mem_filter.mp hwS).2
        have hsub : S.filter (fun v => wordType v = t) ⊆ typeClass w := by
          intro v hv
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hwt.symm⟩
        exact ((Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)).trans
          ((typeClass_card_le hk w).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg k))))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simpa using (Real.exp_pos ((k : ℝ) * c)).le
    rw [hcount, Nat.cast_sum]
    calc
      _ ≤ ∑ _t : ι → Fin (k + 1), Real.exp ((k : ℝ) * c) :=
        Finset.sum_le_sum fun t _ => hfiber t
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- Gibbs nonnegativity allowing singular base laws, with the necessary
absolute-continuity condition explicitly stated. -/
theorem divergence_nonneg_of_support (q p : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (hsupport : ∀ i, 0 < q i → 0 < p i) :
    0 ≤ divergence q p := by
  have hi (i : ι) : q i - p i ≤ q i * (Real.log (q i) - Real.log (p i)) := by
    by_cases hz : q i = 0
    · simp only [hz, zero_sub, zero_mul]
      exact neg_nonpos.mpr (hp i)
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hpi := hsupport i hqi
      have hm := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hpi hqi)) hqi.le
      rw [Real.log_div (ne_of_gt hpi) hz] at hm
      have he : q i * (p i / q i - 1) = p i - q i := by field_simp
      rw [he] at hm
      nlinarith
  calc
    0 = ∑ i, (q i - p i) := by rw [Finset.sum_sub_distrib, hqs, hps]; ring
    _ ≤ divergence q p := Finset.sum_le_sum fun i _ => hi i

theorem iidLaw_letters_pos {k : ℕ} (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (w : Fin k → ι) (hw : 0 < iidLaw p k w) (j : Fin k) : 0 < p (w j) := by
  apply lt_of_le_of_ne (hp _) (Ne.symm _)
  intro hz
  have hzero : iidLaw p k w = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hz
  rw [hzero] at hw
  exact (lt_irrefl 0) hw

/-- A positive-mass word has empirical entropy bounded by its normalized
self-information, including laws with zero probabilities. -/
theorem empirical_entropy_le_information {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (w : Fin k → ι) (hw : 0 < iidLaw p k w) :
    (k : ℝ) * entropy (empiricalLaw w) ≤ ∑ j, -Real.log (p (w j)) := by
  have hsupport (i : ι) (hi : 0 < empiricalLaw w i) : 0 < p i := by
    have hc : 0 < wordCount w i := by
      by_contra hn
      have hz : wordCount w i = 0 := Nat.eq_zero_of_not_pos hn
      simp only [empiricalLaw, hz, Nat.cast_zero, zero_div] at hi
      exact (lt_irrefl 0) hi
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
    have hji := (Finset.mem_filter.mp hj).2
    rw [← hji]
    exact iidLaw_letters_pos p hp w hw j
  have hg := divergence_nonneg_of_support (empiricalLaw w) p
    (empiricalLaw_nonneg w) (empiricalLaw_sum hk w) hp hs hsupport
  have hcross : divergence (empiricalLaw w) p =
      (∑ i, empiricalLaw w i * (-Real.log (p i))) - entropy (empiricalLaw w) := by
    rw [divergence, entropy_eq_neg_sum]
    simp only [sub_neg_eq_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross] at hg
  calc
    (k : ℝ) * entropy (empiricalLaw w) ≤
        (k : ℝ) * ∑ i, empiricalLaw w i * (-Real.log (p i)) :=
      mul_le_mul_of_nonneg_left (sub_nonneg.mp hg) (Nat.cast_nonneg k)
    _ = _ := empirical_cross_entropy hk w p

theorem information_word_mem_lowEntropyWords {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (w : Fin k → ι) (hw : 0 < iidLaw p k w) (c : ℝ)
    (hcut : ∑ j, -Real.log (p (w j)) ≤ (k : ℝ) * c) :
    w ∈ lowEntropyWords k c := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact le_of_mul_le_mul_left
    ((empirical_entropy_le_information hk p hp hs w hw).trans hcut)
    (Nat.cast_pos.mpr hk)

def empiricalEntropyMass (p : ι → ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  ∑ w ∈ lowEntropyWords k c, iidLaw p k w

theorem empiricalEntropyMass_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) (c : ℝ) : 0 ≤ empiricalEntropyMass p k c :=
  Finset.sum_nonneg fun w _ => iidLaw_nonneg p hp k w

theorem empiricalEntropyMass_le_one (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) (c : ℝ) : empiricalEntropyMass p k c ≤ 1 := by
  calc
    _ ≤ ∑ w : Fin k → ι, iidLaw p k w :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun w _ _ => iidLaw_nonneg p hp k w)
    _ = 1 := iidLaw_sum p hs k

theorem empiricalEntropyMass_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) {c d : ℝ} (hcd : c ≤ d) :
    empiricalEntropyMass p k c ≤ empiricalEntropyMass p k d := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _
    (fun w _ _ => iidLaw_nonneg p hp k w)
  intro w hw
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hw).2).trans hcd⟩

/-- Information-spectrum mass is contained in the universal empirical-entropy
set. The proof explicitly discards zero-mass words before using Gibbs. -/
theorem iidInformationEvent_le_empiricalEntropyMass {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (x c : ℝ) (hxc : x ≤ (k : ℝ) * c) :
    iidInformationEvent p k x ≤ empiricalEntropyMass p k c := by
  unfold iidInformationEvent empiricalEntropyMass lowEntropyWords
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro w _
  by_cases hcut : ∑ j, -Real.log (p (w j)) ≤ x
  · rw [if_pos hcut]
    by_cases hz : iidLaw p k w = 0
    · simp only [hz, ite_self, le_refl]
    · have hw := lt_of_le_of_ne (iidLaw_nonneg p hp k w) (Ne.symm hz)
      have hmem := information_word_mem_lowEntropyWords hk p hp hs w hw c (hcut.trans hxc)
      rw [if_pos (Finset.mem_filter.mp hmem).2]
  · rw [if_neg hcut]
    split_ifs <;> first | exact iidLaw_nonneg p hp k w | exact le_rfl

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The spectrum of any normalized finite law has asymptotically full mass in
the basis-independent low-empirical-entropy collection whenever c>H(p). -/
theorem empiricalEntropyMass_tendsto_one (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℝ) (hc : entropy p < c) :
    Filter.Tendsto (fun k => empiricalEntropyMass p k c) Filter.atTop (𝓝 1) := by
  have hmass := iidInformationEvent_law_of_large_numbers p hp hs c (ne_of_gt hc)
  simp only [hc, ite_true] at hmass
  have hgap : Filter.Tendsto (fun k => 1 - iidInformationEvent p k ((k : ℝ) * c))
      Filter.atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hmass
  have hsmall : Filter.Tendsto (fun k => 1 - empiricalEntropyMass p k c)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall
      (fun k => sub_nonneg.mpr (empiricalEntropyMass_le_one p hp hs k c))) _ hgap
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    exact sub_le_sub_left (iidInformationEvent_le_empiricalEntropyMass hk p hp hs _ c le_rfl) 1
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  simpa only [sub_sub_cancel, sub_zero] using h

/-- The universal mass law also allows a convergent, dimension-dependent
empirical-entropy cutoff. -/
theorem empiricalEntropyMass_tendsto_one_moving (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) (hH : entropy p < c₀) :
    Tendsto (fun k => empiricalEntropyMass p k (c k)) atTop (𝓝 1) := by
  let d := (entropy p + c₀) / 2
  have hdlo : entropy p < d := by dsimp [d]; linarith
  have hdhi : d < c₀ := by dsimp [d]; linarith
  have hmass := empiricalEntropyMass_tendsto_one p hp hs d hdlo
  have hgap : Tendsto (fun k => 1 - empiricalEntropyMass p k d) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hmass
  have hsmall : Tendsto (fun k => 1 - empiricalEntropyMass p k (c k)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall
      (fun k => sub_nonneg.mpr (empiricalEntropyMass_le_one p hp hs k (c k)))) _ hgap
    filter_upwards [hc.eventually (Ioi_mem_nhds hdhi)] with k hk
    exact sub_le_sub_left (empiricalEntropyMass_mono p hp k hk.le) 1
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  simpa only [sub_sub_cancel, sub_zero] using h

/-- The universal empirical-entropy collection retains at least the Gaussian
information-spectrum mass at every moving threshold with the displayed
second-order limit. Independence and the CLT are proved in Spectrum.Probability. -/
theorem empiricalEntropyMass_liminf_gaussian (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p)
    (c : ℕ → ℝ) (y : ℝ)
    (hcut : Tendsto (fun k : ℕ =>
      ((k : ℝ) * c k - k * entropy p) / Real.sqrt k) atTop (𝓝 y)) :
    (ProbabilityTheory.gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y) ≤
      liminf (fun k => empiricalEntropyMass p k (c k)) atTop := by
  have hm := iidInformationEvent_gaussian_moving p hp hs hv
    (fun k => (k : ℝ) * c k) y hcut
  rw [← hm.liminf_eq]
  apply liminf_le_liminf _ hm.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop (fun k => empiricalEntropyMass_le_one p hp hs k (c k)))
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact iidInformationEvent_le_empiricalEntropyMass hk p hp hs _ (c k) le_rfl

/-- Every fixed polynomial compression overhead is negligible on the
Gaussian scale; the zero-length convention is harmless. -/
theorem log_succ_div_sqrt_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / Real.sqrt k) atTop (𝓝 0) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ) / Real.sqrt k) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hconst : Tendsto (fun k : ℕ => Real.log 2 / Real.sqrt k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (Real.log 2)
  have hupper : Tendsto (fun k : ℕ =>
      Real.log 2 / Real.sqrt k + Real.log (k : ℝ) / Real.sqrt k) atTop (𝓝 0) := by
    simpa only [add_zero] using hconst.add hlog
  apply squeeze_zero' (Eventually.of_forall fun k =>
    div_nonneg (Real.log_nonneg (by have hkNN : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))
      (Real.sqrt_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkP : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hkR
  have hl : Real.log ((k : ℝ) + 1) ≤ Real.log 2 + Real.log (k : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hkP)]
    apply Real.log_le_log (by positivity)
    linarith
  simpa only [add_div] using div_le_div_of_nonneg_right hl (Real.sqrt_nonneg _)

theorem polynomial_overhead_div_sqrt_tendsto_zero (C L : ℝ) :
    Tendsto (fun k : ℕ => (C + L * Real.log ((k : ℝ) + 1)) / Real.sqrt k)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun k : ℕ => C / Real.sqrt k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
  have hl := log_succ_div_sqrt_tendsto_zero.const_mul L
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hc.add hl

theorem polynomial_overhead_div_nat_tendsto_zero (C L : ℝ) :
    Tendsto (fun k : ℕ => (C + L * Real.log ((k : ℝ) + 1)) / k)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (polynomial_overhead_div_sqrt_tendsto_zero C L).mul hinv
  have hh : Tendsto (fun k : ℕ =>
      ((C + L * Real.log ((k : ℝ) + 1)) / Real.sqrt k) * (Real.sqrt k)⁻¹)
      atTop (𝓝 0) := by simpa only [mul_zero] using h
  apply hh.congr'
  filter_upwards with k
  change ((C + L * Real.log ((k : ℝ) + 1)) / Real.sqrt k) / Real.sqrt k = _
  rw [div_div, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg k)]

end
end ExtractionSpectrum
