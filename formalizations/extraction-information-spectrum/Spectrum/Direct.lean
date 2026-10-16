import Spectrum.Types
import Spectrum.Holder

open scoped BigOperators Classical Topology ComplexOrder
open Filter

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact occupation product, with the natural convention 0^0=1 for
absent letters. It proves equal type likelihood even for zero probabilities. -/
theorem iidLaw_eq_count_product {k : ℕ} (p : ι → ℝ) (w : Fin k → ι) :
    iidLaw p k w = ∏ i, (p i) ^ wordCount w i := by
  unfold iidLaw
  rw [← Finset.prod_fiberwise Finset.univ w (fun j => p (w j))]
  apply Finset.prod_congr rfl
  intro i _
  calc
    ∏ j ∈ Finset.univ.filter (fun j => w j = i), p (w j) =
        ∏ j ∈ Finset.univ.filter (fun j => w j = i), p i := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by simp only [Finset.prod_const, wordCount]

theorem iidLaw_eq_of_wordType_eq {k : ℕ} (p : ι → ℝ) (v w : Fin k → ι)
    (h : wordType v = wordType w) : iidLaw p k v = iidLaw p k w := by
  rw [iidLaw_eq_count_product, iidLaw_eq_count_product]
  apply Finset.prod_congr rfl
  intro i _
  have hi := congrArg (fun t : ι → Fin (k + 1) => (t i).val) h
  change wordCount v i = wordCount w i at hi
  rw [hi]

theorem empirical_support_of_iidLaw_pos {k : ℕ} (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (w : Fin k → ι) (hw : 0 < iidLaw p k w) (i : ι)
    (hi : 0 < empiricalLaw w i) : 0 < p i := by
  have hc : 0 < wordCount w i := by
    by_contra hn
    have hz : wordCount w i = 0 := Nat.eq_zero_of_not_pos hn
    simp only [empiricalLaw, hz, Nat.cast_zero, zero_div] at hi
    exact (lt_irrefl 0) hi
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
  rw [← (Finset.mem_filter.mp hj).2]
  exact iidLaw_letters_pos p hp w hw j

theorem cross_entropy_eq_entropy_add_divergence (q p : ι → ℝ) :
    (∑ i, q i * (-Real.log (p i))) = entropy q + divergence q p := by
  rw [entropy_eq_neg_sum, divergence]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem escort_sum_of_normalized (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) : ∑ i, escort p α i = 1 := by
  simp only [escort, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos_of_normalized p hp hs α))

/-- The escort change of measure remains exact for singular laws whenever
the trial law has no mass outside the base law's positive support. -/
theorem escort_divergence_identity_of_support (q p : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (hsupport : ∀ i, 0 < q i → 0 < p i) (α : ℝ) :
    divergence q (escort p α) = α * divergence q p +
      (α - 1) * entropy q + Real.log (partition p α) := by
  have he (i : ι) : q i * (Real.log (q i) - Real.log (escort p α i)) =
      α * (q i * (Real.log (q i) - Real.log (p i))) +
        (α - 1) * -(q i * Real.log (q i)) + q i * Real.log (partition p α) := by
    by_cases hz : q i = 0
    · simp only [hz, zero_mul, neg_zero, add_zero, mul_zero]
    · have hpi := hsupport i (lt_of_le_of_ne (hq i) (Ne.symm hz))
      have hl : Real.log (escort p α i) =
          α * Real.log (p i) - Real.log (partition p α) := by
        rw [escort, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hpi α))
          (ne_of_gt (partition_pos_of_normalized p hp hps α)), Real.log_rpow hpi]
      rw [hl]
      ring
  simp only [divergence, he, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_mul, hqs, one_mul, entropy_eq_neg_sum]

/-- Strict-direct weak duality on an arbitrary normalized finite law, with
absolute continuity retained instead of a full-rank assumption. -/
theorem direct_variational_lower_of_support (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hsupport : ∀ i, 0 < q i → 0 < p i)
    (c α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hc : c ≤ entropy q) :
    directDualObjective p c α ≤ divergence q p := by
  have hZ := partition_pos_of_normalized p hp hps α
  have heNN (i : ι) : 0 ≤ escort p α i :=
    div_nonneg (Real.rpow_nonneg (hp i) α) hZ.le
  have heSupport (i : ι) (hi : 0 < q i) : 0 < escort p α i :=
    div_pos (Real.rpow_pos_of_pos (hsupport i hi) α) hZ
  have hg := divergence_nonneg_of_support q (escort p α) hq hqs heNN
    (escort_sum_of_normalized p hp hps α) heSupport
  rw [escort_divergence_identity_of_support q p hq hqs hp hps hsupport α] at hg
  unfold directDualObjective
  apply (div_le_iff₀ hα.1).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hα.2.le) (sub_nonneg.mpr hc)]

def typeClassMass {k : ℕ} (p : ι → ℝ) (w : Fin k → ι) : ℝ :=
  ∑ v ∈ typeClass w, iidLaw p k v

theorem typeClassMass_eq_card {k : ℕ} (p : ι → ℝ) (w : Fin k → ι) :
    typeClassMass p w = ((typeClass w).card : ℝ) * iidLaw p k w := by
  unfold typeClassMass
  calc
    _ = ∑ _v ∈ typeClass w, iidLaw p k w :=
      Finset.sum_congr rfl fun v hv =>
        iidLaw_eq_of_wordType_eq p v w (Finset.mem_filter.mp hv).2
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The elementary upper half of the method of types, valid on positive
type likelihoods without imposing full rank on the finite base law. -/
theorem typeClassMass_le_divergence {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (w : Fin k → ι)
    (hw : 0 < iidLaw p k w) :
    typeClassMass p w ≤ Real.exp (-(k : ℝ) * divergence (empiricalLaw w) p) := by
  rw [typeClassMass_eq_card, word_likelihood_eq_exp hk w p (iidLaw_letters_pos p hp w hw)]
  have h := mul_le_mul_of_nonneg_right (typeClass_card_le hk w)
    (Real.exp_pos (-(k : ℝ) * ∑ i, empiricalLaw w i * (-Real.log (p i)))).le
  have he : Real.exp ((k : ℝ) * entropy (empiricalLaw w)) *
      Real.exp (-(k : ℝ) * ∑ i, empiricalLaw w i * (-Real.log (p i))) =
        Real.exp (-(k : ℝ) * divergence (empiricalLaw w) p) := by
    rw [← Real.exp_add, cross_entropy_eq_entropy_add_divergence]
    congr 1
    ring
  exact h.trans_eq he

/-- A high-entropy type has the strict-direct exponential mass upper bound.
Zero-likelihood types are handled separately, before any logarithmic identity. -/
theorem typeClassMass_direct_bound {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (w : Fin k → ι) (c α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ≤ entropy (empiricalLaw w)) :
    typeClassMass p w ≤ Real.exp (-(k : ℝ) * directDualObjective p c α) := by
  by_cases hz : iidLaw p k w = 0
  · rw [typeClassMass_eq_card, hz, mul_zero]
    exact (Real.exp_pos _).le
  · have hw := lt_of_le_of_ne (iidLaw_nonneg p hp k w) (Ne.symm hz)
    have hd := direct_variational_lower_of_support p (empiricalLaw w) hp hs
      (empiricalLaw_nonneg w) (empiricalLaw_sum hk w)
      (empirical_support_of_iidLaw_pos p hp w hw) c α hα hc
    exact (typeClassMass_le_divergence hk p hp w hw).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr (Nat.cast_nonneg k))))

def highEntropyWords (k : ℕ) (c : ℝ) : Finset (Fin k → ι) :=
  Finset.univ.filter (fun w => ¬entropy (empiricalLaw w) ≤ c)

def empiricalEntropyError (p : ι → ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  ∑ w ∈ highEntropyWords k c, iidLaw p k w

theorem empiricalEntropyError_eq_one_sub (p : ι → ℝ) (hs : ∑ i, p i = 1)
    (k : ℕ) (c : ℝ) :
    empiricalEntropyError p k c = 1 - empiricalEntropyMass p k c := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin k → ι => entropy (empiricalLaw w) ≤ c) (iidLaw p k)
  rw [iidLaw_sum p hs k] at h
  change empiricalEntropyMass p k c + empiricalEntropyError p k c = 1 at h
  linarith

/-- A finite direct error bound for the state-independent empirical-entropy
collection. The polynomial counts actual integer types, and the exponential
comes from supported Gibbs/escort weak duality, without Stirling asymptotics. -/
theorem empiricalEntropyError_direct_bound {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (c α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    empiricalEntropyError p k c ≤ ((k + 1 : ℝ) ^ Fintype.card ι) *
      Real.exp (-(k : ℝ) * directDualObjective p c α) := by
  let S := highEntropyWords (ι := ι) k c
  have hfiber (t : ι → Fin (k + 1)) :
      (∑ w ∈ S.filter (fun w => wordType w = t), iidLaw p k w) ≤
        Real.exp (-(k : ℝ) * directDualObjective p c α) := by
    by_cases hempty : (S.filter (fun w => wordType w = t)).Nonempty
    · obtain ⟨w, hw⟩ := hempty
      have hwt := (Finset.mem_filter.mp hw).2
      have hwS := (Finset.mem_filter.mp hw).1
      have hH : c ≤ entropy (empiricalLaw w) :=
        (lt_of_not_ge (Finset.mem_filter.mp hwS).2).le
      have hsub : S.filter (fun v => wordType v = t) ⊆ typeClass w := by
        intro v hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hwt.symm⟩
      calc
        _ ≤ typeClassMass p w := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => iidLaw_nonneg p hp k v)
        _ ≤ _ := typeClassMass_direct_bound hk p hp hs w c α hα hH
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty]
      exact (Real.exp_pos _).le
  unfold empiricalEntropyError
  rw [← Finset.sum_fiberwise S wordType (iidLaw p k)]
  calc
    _ ≤ ∑ _t : ι → Fin (k + 1), Real.exp (-(k : ℝ) * directDualObjective p c α) :=
      Finset.sum_le_sum fun t _ => hfiber t
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

theorem one_sub_empiricalEntropyMass_direct_bound {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (c α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    1 - empiricalEntropyMass p k c ≤ ((k + 1 : ℝ) ^ Fintype.card ι) *
      Real.exp (-(k : ℝ) * directDualObjective p c α) := by
  rw [← empiricalEntropyError_eq_one_sub p hs k c]
  exact empiricalEntropyError_direct_bound hk p hp hs c α hα

/-- A proved fixed-polynomial loss is negligible in the exponential rate.
The target may vanish, so no logarithm of that target is taken. -/
theorem polynomial_exponential_eventually (D : ℕ) (F E : ℕ → ℝ) (E₀ : ℝ)
    (hE : Tendsto E atTop (𝓝 E₀))
    (hF : ∀ᶠ k : ℕ in atTop, F k ≤ ((k + 1 : ℝ) ^ D) * Real.exp (-(k : ℝ) * E k))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, F k ≤ Real.exp (-(k : ℝ) * (E₀ - η)) := by
  have hpoly : Tendsto (fun k : ℕ => (D : ℝ) * Real.log ((k : ℝ) + 1) / k)
      atTop (𝓝 0) := by
    simpa only [zero_add] using polynomial_overhead_div_nat_tendsto_zero 0 (D : ℝ)
  have hlim : Tendsto (fun k : ℕ =>
      (D : ℝ) * Real.log ((k : ℝ) + 1) / k - E k) atTop (𝓝 (-E₀)) := by
    simpa only [zero_sub] using hpoly.sub hE
  filter_upwards [hF, hlim.eventually_lt_const (show -E₀ < -E₀ + η by linarith),
    eventually_gt_atTop 0] with k hk hrate hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  have he := mul_lt_mul_of_pos_left hrate hkR
  have hcancel : (k : ℝ) * ((D : ℝ) * Real.log ((k : ℝ) + 1) / k) =
      (D : ℝ) * Real.log ((k : ℝ) + 1) := by field_simp
  rw [mul_sub, hcancel] at he
  have hp : ((k + 1 : ℝ) ^ D) = Real.exp ((D : ℝ) * Real.log ((k : ℝ) + 1)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  exact hk.trans (by
    rw [hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith)

variable [Nonempty ι]

/-- The strict-direct scalar infimum is attained by an interior Renyi
parameter, on the actual positive support of a possibly singular finite law. -/
theorem nonnegative_strict_direct_dual_attainment (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card (PositiveSupport p))) :
    ∃ α ∈ Set.Ioo (0 : ℝ) 1,
      (⨅ q : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
        divergence q.1.1 (supportLaw p)) = directDualObjective p c α := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  have hlo' : entropy (supportLaw p) < c := by rw [supportLaw_entropy p hp]; exact hlo
  obtain ⟨q, α, hq, hqs, hH, hα, he, hmin, _⟩ :=
    strict_direct_variational_certificate (supportLaw p) (fun i => i.2)
      (supportLaw_sum p hp hs) c hlo' hhi
  let q0 : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} :=
    ⟨⟨q, hq, hqs⟩, hH.ge⟩
  letI : Nonempty {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} := ⟨q0⟩
  have hloB : BddBelow (Set.range (fun r :
      {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} =>
        divergence r.1.1 (supportLaw p))) := by
    refine ⟨divergence q (supportLaw p), ?_⟩
    rintro v ⟨r, rfl⟩
    exact hmin r.1.1 r.1.2.1 r.1.2.2 r.2
  have hInf : (⨅ r : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
      divergence r.1.1 (supportLaw p)) = divergence q (supportLaw p) :=
    le_antisymm (ciInf_le hloB q0)
      (le_ciInf fun r => hmin r.1.1 r.1.2.1 r.1.2.2 r.2)
  have hpart : partition (supportLaw p) α = partition p α :=
    positiveSupport_sum p hp (fun x => x ^ α) (Real.zero_rpow (ne_of_gt hα.1))
  refine ⟨α, hα, ?_⟩
  rw [hInf, he]
  unfold directDualObjective
  rw [hpart]

/-- The optimized finite strict-direct error bound. Both the integer-type
polynomial and the full relative-entropy variational exponent are retained. -/
theorem empiricalEntropyError_strict_direct_bound {k : ℕ} (hk : 0 < k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card (PositiveSupport p))) :
    1 - empiricalEntropyMass p k c ≤ ((k + 1 : ℝ) ^ Fintype.card ι) *
      Real.exp (-(k : ℝ) *
        (⨅ q : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
          divergence q.1.1 (supportLaw p))) := by
  obtain ⟨α, hα, hE⟩ := nonnegative_strict_direct_dual_attainment p hp hs c hlo hhi
  rw [hE]
  exact one_sub_empiricalEntropyMass_direct_bound hk p hp hs c α hα

/-- The empirical-entropy compression error has the full strict-direct
variational exponent as a lower bound on its decay rate. The threshold may
vary with k, including a polynomial logarithmic compression overhead. -/
theorem empiricalEntropyError_strict_direct_exponential (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀))
    (hlo : entropy p < c₀) (hhi : c₀ < Real.log (Fintype.card (PositiveSupport p)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, 1 - empiricalEntropyMass p k (c k) ≤
      Real.exp (-(k : ℝ) *
        ((⨅ q : {q : ProbabilityVector (PositiveSupport p) // c₀ ≤ entropy q.1},
          divergence q.1.1 (supportLaw p)) - η)) := by
  obtain ⟨α, hα, hE⟩ := nonnegative_strict_direct_dual_attainment p hp hs c₀ hlo hhi
  have hlim : Tendsto (fun k => directDualObjective p (c k) α) atTop
      (𝓝 (directDualObjective p c₀ α)) := by
    unfold directDualObjective
    exact ((hc.const_mul (1 - α)).sub tendsto_const_nhds).div_const α
  rw [hE]
  apply polynomial_exponential_eventually (Fintype.card ι)
    (fun k => 1 - empiricalEntropyMass p k (c k))
    (fun k => directDualObjective p (c k) α) _ hlim _ η hη
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact one_sub_empiricalEntropyMass_direct_bound hk p hp hs (c k) α hα

/-- Strict-direct finite empirical-error estimate on the actual spectrum of
a complex PSD trace-one matrix, with its actual matrix rank at the boundary. -/
theorem density_empiricalEntropyError_strict_direct_bound
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    {k : ℕ} (hk : 0 < k) (c : ℝ)
    (hlo : entropy hX.1.isHermitian.eigenvalues < c) (hhi : c < Real.log X.rank) :
    1 - empiricalEntropyMass hX.1.isHermitian.eigenvalues k c ≤
      ((k + 1 : ℝ) ^ Fintype.card ι) * Real.exp (-(k : ℝ) *
        (⨅ q : {q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues) //
            c ≤ entropy q.1}, divergence q.1.1 (supportLaw hX.1.isHermitian.eigenvalues))) := by
  have hr : Fintype.card (PositiveSupport hX.1.isHermitian.eigenvalues) = X.rank :=
    density_positiveSupport_card_eq_rank X hX.1
  exact empiricalEntropyError_strict_direct_bound hk hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) c hlo
    (by rw [hr]; exact hhi)

/-- The actual-density, rank-sensitive strict-direct empirical-error exponent.
No type or large-deviation conclusion is an assumption of this theorem. -/
theorem density_empiricalEntropyError_strict_direct_exponential
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀))
    (hlo : entropy hX.1.isHermitian.eigenvalues < c₀) (hhi : c₀ < Real.log X.rank)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, 1 - empiricalEntropyMass hX.1.isHermitian.eigenvalues k (c k) ≤
      Real.exp (-(k : ℝ) *
        ((⨅ q : {q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues) //
            c₀ ≤ entropy q.1}, divergence q.1.1 (supportLaw hX.1.isHermitian.eigenvalues)) - η)) := by
  have hr : Fintype.card (PositiveSupport hX.1.isHermitian.eigenvalues) = X.rank :=
    density_positiveSupport_card_eq_rank X hX.1
  exact empiricalEntropyError_strict_direct_exponential hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) c c₀ hc hlo
    (by rw [hr]; exact hhi) η hη

/-- Strict finite Gibbs inequality: equality of the divergence forces equality
of the entire probability vector, including coordinates where q vanishes. -/
theorem divergence_pos_of_ne (q p : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hqs : ∑ i, q i = 1) (hp : ∀ i, 0 < p i) (hps : ∑ i, p i = 1)
    (hne : q ≠ p) : 0 < divergence q p := by
  have hpoint (i : ι) (hi : q i ≠ p i) :
      q i - p i < q i * (Real.log (q i) - Real.log (p i)) := by
    by_cases hz : q i = 0
    · simp only [hz, zero_sub, zero_mul]
      exact neg_neg_of_pos (hp i)
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hneq : p i / q i ≠ 1 := by
        intro h
        exact hi ((div_eq_one_iff_eq hz).mp h).symm
      have hm := mul_lt_mul_of_pos_left
        (Real.log_lt_sub_one_of_pos (div_pos (hp i) hqi) hneq) hqi
      rw [Real.log_div (ne_of_gt (hp i)) hz] at hm
      have he : q i * (p i / q i - 1) = p i - q i := by field_simp
      rw [he] at hm
      nlinarith
  have hweak (i : ι) : q i - p i ≤ q i * (Real.log (q i) - Real.log (p i)) := by
    by_cases he : q i = p i
    · simp only [he, sub_self, mul_zero, le_refl]
    · exact (hpoint i he).le
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  calc
    0 = ∑ i, (q i - p i) := by rw [Finset.sum_sub_distrib, hqs, hps]; ring
    _ < divergence q p := Finset.sum_lt_sum (fun i _ => hweak i)
      ⟨i, Finset.mem_univ _, hpoint i hi⟩

/-- The strict-direct variational decay rate is positive in precisely the
interior regime used here. This conclusion is proved, not separately assumed. -/
theorem strict_direct_exponent_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card (PositiveSupport p))) :
    0 < (⨅ q : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
      divergence q.1.1 (supportLaw p)) := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  have hlo' : entropy (supportLaw p) < c := by rw [supportLaw_entropy p hp]; exact hlo
  obtain ⟨q, α, hq, hqs, hH, hα, he, hmin, _⟩ :=
    strict_direct_variational_certificate (supportLaw p) (fun i => i.2)
      (supportLaw_sum p hp hs) c hlo' hhi
  let q0 : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} :=
    ⟨⟨q, hq, hqs⟩, hH.ge⟩
  letI : Nonempty {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} := ⟨q0⟩
  have hloB : BddBelow (Set.range (fun r :
      {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1} =>
        divergence r.1.1 (supportLaw p))) := by
    refine ⟨divergence q (supportLaw p), ?_⟩
    rintro v ⟨r, rfl⟩
    exact hmin r.1.1 r.1.2.1 r.1.2.2 r.2
  have hInf : (⨅ r : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
      divergence r.1.1 (supportLaw p)) = divergence q (supportLaw p) :=
    le_antisymm (ciInf_le hloB q0)
      (le_ciInf fun r => hmin r.1.1 r.1.2.1 r.1.2.2 r.2)
  rw [hInf]
  apply divergence_pos_of_ne q (supportLaw p) hq hqs (fun i => i.2) (supportLaw_sum p hp hs)
  intro hqp
  rw [hqp] at hH
  linarith

end
end ExtractionSpectrum
