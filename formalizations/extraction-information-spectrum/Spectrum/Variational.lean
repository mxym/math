import Spectrum.Probability

open scoped BigOperators Topology Classical ComplexOrder

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι]

def divergence (q p : ι → ℝ) : ℝ :=
  ∑ i, q i * (Real.log (q i) - Real.log (p i))

theorem entropy_eq_neg_sum (q : ι → ℝ) :
    entropy q = -(∑ i, q i * Real.log (q i)) := by
  simp only [entropy, finiteMean, selfInformation, mul_neg, Finset.sum_neg_distrib]

theorem divergence_self (q : ι → ℝ) : divergence q q = 0 := by
  simp [divergence]

/-- Finite Gibbs nonnegativity, proved from log x <= x-1, allowing zero
probabilities in the first argument. The base law is evaluated on its support. -/
theorem divergence_nonneg (q p : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hqs : ∑ i, q i = 1) (hp : ∀ i, 0 < p i) (hps : ∑ i, p i = 1) :
    0 ≤ divergence q p := by
  have hi (i : ι) : q i - p i ≤ q i * (Real.log (q i) - Real.log (p i)) := by
    by_cases hz : q i = 0
    · simp only [hz, zero_sub, zero_mul]
      linarith [hp i]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (div_pos (hp i) hqi)
      have hm := mul_le_mul_of_nonneg_left hlog hqi.le
      rw [Real.log_div (ne_of_gt (hp i)) hz] at hm
      have he : q i * (p i / q i - 1) = p i - q i := by
        field_simp
      rw [he] at hm
      nlinarith
  calc
    0 = ∑ i, (q i - p i) := by rw [Finset.sum_sub_distrib, hqs, hps]; ring
    _ ≤ divergence q p := Finset.sum_le_sum fun i _ => hi i

def partition (p : ι → ℝ) (α : ℝ) : ℝ := ∑ i, (p i) ^ α

def escort (p : ι → ℝ) (α : ℝ) (i : ι) : ℝ := (p i) ^ α / partition p α

variable [Nonempty ι]

theorem partition_pos (p : ι → ℝ) (hp : ∀ i, 0 < p i) (α : ℝ) :
    0 < partition p α :=
  Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hp i) α) Finset.univ_nonempty

theorem escort_pos (p : ι → ℝ) (hp : ∀ i, 0 < p i) (α : ℝ) (i : ι) :
    0 < escort p α i := div_pos (Real.rpow_pos_of_pos (hp i) α) (partition_pos p hp α)

theorem escort_sum (p : ι → ℝ) (hp : ∀ i, 0 < p i) (α : ℝ) :
    ∑ i, escort p α i = 1 := by
  simp only [escort, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos p hp α))

theorem escort_one (p : ι → ℝ) (hs : ∑ i, p i = 1) : escort p 1 = p := by
  ext i
  simp only [escort, partition, Real.rpow_one, hs, div_one]

/-- The finite escort change-of-measure identity, including nonuniform or
zero-containing trial laws q. No entropy derivative or variational conclusion
is supplied as a hypothesis. -/
theorem escort_divergence_identity (q p : ι → ℝ)
    (hqs : ∑ i, q i = 1) (hp : ∀ i, 0 < p i) (α : ℝ) :
    divergence q (escort p α) = α * divergence q p +
      (α - 1) * entropy q + Real.log (partition p α) := by
  have hl (i : ι) : Real.log (escort p α i) =
      α * Real.log (p i) - Real.log (partition p α) := by
    rw [escort, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hp i) α))
      (ne_of_gt (partition_pos p hp α)), Real.log_rpow (hp i)]
  simp only [divergence, hl, entropy_eq_neg_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  have he (i : ι) : q i * (Real.log (q i) - (α * Real.log (p i) - Real.log (partition p α))) =
      α * (q i * (Real.log (q i) - Real.log (p i))) +
        (α - 1) * -(q i * Real.log (q i)) + q i * Real.log (partition p α) := by ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_mul, hqs, one_mul]

def primalObjective (p : ι → ℝ) (c : ℝ) (q : ι → ℝ) : ℝ :=
  divergence q p + max 0 (entropy q - c) / 2

/-- The Renyi maximand is written in its nonsingular log-moment form at alpha=1. -/
def dualObjective (p : ι → ℝ) (c α : ℝ) : ℝ :=
  -Real.log (partition p α) / α - (α - 1) * c / α

theorem escort_variational_lower (p q : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (c α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2) :
    dualObjective p c α ≤ primalObjective p c q := by
  have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα.1
  have hg := divergence_nonneg q (escort p α) hq hqs
    (escort_pos p hp α) (escort_sum p hp α)
  rw [escort_divergence_identity q p hqs hp α] at hg
  have hpen : (α - 1) * (entropy q - c) ≤ α * (max 0 (entropy q - c) / 2) := by
    by_cases hB : 0 ≤ entropy q - c
    · rw [max_eq_right hB]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hα.2)]
    · rw [max_eq_left (le_of_not_ge hB)]
      have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hα.1) (le_of_not_ge hB)
      simpa using hmul
  unfold dualObjective primalObjective
  rw [← sub_div]
  apply (div_le_iff₀ hαp).mpr
  nlinarith

theorem escort_continuous (p : ι → ℝ) (hp : ∀ i, 0 < p i) (i : ι) :
    Continuous (fun α : ℝ => escort p α i) := by
  have hZ : Continuous (partition p) :=
    continuous_finset_sum _ fun j _ => Real.continuous_const_rpow (ne_of_gt (hp j))
  exact (Real.continuous_const_rpow (ne_of_gt (hp i))).div hZ
    (fun α => ne_of_gt (partition_pos p hp α))

theorem escort_entropy_continuous (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    Continuous (fun α : ℝ => entropy (escort p α)) := by
  simp only [entropy_eq_neg_sum]
  apply Continuous.neg
  apply continuous_finset_sum
  intro i _
  exact (escort_continuous p hp i).mul ((escort_continuous p hp i).log
    (fun α => ne_of_gt (escort_pos p hp α i)))

theorem dualObjective_one (p : ι → ℝ) (hs : ∑ i, p i = 1) (c : ℝ) :
    dualObjective p c 1 = 0 := by
  simp [dualObjective, partition, Real.rpow_one, hs]

theorem escort_primal_dual_of_entropy_eq (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (c α : ℝ) (hα : 0 < α) (hc : entropy (escort p α) = c) :
    primalObjective p c (escort p α) = dualObjective p c α := by
  have he := escort_divergence_identity (escort p α) p (escort_sum p hp α) hp α
  rw [divergence_self, hc] at he
  unfold primalObjective dualObjective
  rw [hc, sub_self, max_self, zero_div, add_zero]
  field_simp
  nlinarith

theorem escort_primal_dual_at_two (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (c : ℝ) (hc : c ≤ entropy (escort p 2)) :
    primalObjective p c (escort p 2) = dualObjective p c 2 := by
  have he := escort_divergence_identity (escort p 2) p (escort_sum p hp 2) hp 2
  rw [divergence_self] at he
  unfold primalObjective dualObjective
  rw [max_eq_right (sub_nonneg.mpr hc)]
  nlinarith

/-- An attaining primal law and dual parameter exist. An intermediate escort
is found with the intermediate value theorem; no entropy monotonicity or
derivative sign is assumed. -/
theorem escort_variational_attainment (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ) :
    ∃ q : ι → ℝ, ∃ α : ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      α ∈ Set.Icc (1 : ℝ) 2 ∧ primalObjective p c q = dualObjective p c α := by
  by_cases hpc : entropy p ≤ c
  · refine ⟨p, 1, (fun i => (hp i).le), hs, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [dualObjective_one p hs]
    simp [primalObjective, divergence_self, max_eq_left (sub_nonpos.mpr hpc)]
  · by_cases h2 : c ≤ entropy (escort p 2)
    · exact ⟨escort p 2, 2, (fun i => (escort_pos p hp 2 i).le), escort_sum p hp 2,
        ⟨by norm_num, le_rfl⟩, escort_primal_dual_at_two p hp c h2⟩
    · have hI : c ∈ Set.Icc (entropy (escort p 2)) (entropy (escort p 1)) := by
        rw [escort_one p hs]
        exact ⟨(lt_of_not_ge h2).le, (lt_of_not_ge hpc).le⟩
      obtain ⟨α, hα, hE⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2)
        (escort_entropy_continuous p hp).continuousOn hI
      exact ⟨escort p α, α, (fun i => (escort_pos p hp α i).le), escort_sum p hp α,
        hα, escort_primal_dual_of_entropy_eq p hp c α (lt_of_lt_of_le zero_lt_one hα.1) hE⟩

/-- Complete finite escort min--max certificate: the displayed trial law is a
global primal minimizer and the displayed parameter a global dual maximizer. -/
theorem escort_variational_certificate (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ) :
    ∃ q : ι → ℝ, ∃ α : ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      α ∈ Set.Icc (1 : ℝ) 2 ∧ primalObjective p c q = dualObjective p c α ∧
      (∀ r : ι → ℝ, (∀ i, 0 ≤ r i) → (∑ i, r i = 1) →
        primalObjective p c q ≤ primalObjective p c r) ∧
      (∀ β ∈ Set.Icc (1 : ℝ) 2, dualObjective p c β ≤ dualObjective p c α) := by
  obtain ⟨q, α, hq, hqs, hα, he⟩ := escort_variational_attainment p hp hs c
  refine ⟨q, α, hq, hqs, hα, he, ?_, ?_⟩
  · intro r hr hrs
    rw [he]
    exact escort_variational_lower p r hp hr hrs c α hα
  · intro β hβ
    rw [← he]
    exact escort_variational_lower p q hp hq hqs c β hβ

def ProbabilityVector (ι : Type*) [Fintype ι] :=
  {q : ι → ℝ // (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

/-- The actual infimum--supremum identity, with both extrema attained by the
constructed certificate, for a normalized positive finite base law. -/
theorem escort_variational_identity (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ) :
    (⨅ q : ProbabilityVector ι, primalObjective p c q.1) =
      ⨆ α : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2}, dualObjective p c α.1 := by
  letI : Nonempty (ProbabilityVector ι) := ⟨⟨p, (fun i => (hp i).le), hs⟩⟩
  letI : Nonempty {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2} := ⟨⟨1, le_rfl, by norm_num⟩⟩
  obtain ⟨q, α, hq, hqs, hα, he, hmin, hmax⟩ := escort_variational_certificate p hp hs c
  let q0 : ProbabilityVector ι := ⟨q, hq, hqs⟩
  let α0 : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2} := ⟨α, hα⟩
  have hlo : BddBelow (Set.range (fun r : ProbabilityVector ι => primalObjective p c r.1)) := by
    refine ⟨primalObjective p c q, ?_⟩
    rintro v ⟨r, rfl⟩
    exact hmin r.1 r.2.1 r.2.2
  have hhi : BddAbove (Set.range (fun β : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2} =>
      dualObjective p c β.1)) := by
    refine ⟨dualObjective p c α, ?_⟩
    rintro v ⟨β, rfl⟩
    exact hmax β.1 β.2
  have hInf : (⨅ r : ProbabilityVector ι, primalObjective p c r.1) = primalObjective p c q :=
    le_antisymm (ciInf_le hlo q0) (le_ciInf fun r => hmin r.1 r.2.1 r.2.2)
  have hSup : (⨆ β : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2}, dualObjective p c β.1) =
      dualObjective p c α := le_antisymm (ciSup_le fun β => hmax β.1 β.2) (le_ciSup hhi α0)
  rw [hInf, hSup]
  exact he

def renyiEntropy (p : ι → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then entropy p else Real.log (partition p α) / (1 - α)

theorem dualObjective_eq_renyi (p : ι → ℝ) (hs : ∑ i, p i = 1)
    (c α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2) :
    dualObjective p c α = (α - 1) / α * (renyiEntropy p α - c) := by
  by_cases h1 : α = 1
  · subst α
    rw [dualObjective_one p hs]
    norm_num
  · have hα0 : α ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hα.1)
    have hden : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [renyiEntropy, h1, ite_false, dualObjective]
    field_simp
    ring

/-- The paper's exact finite entropy/relative-entropy variational identity,
including alpha=1 and endpoint maximizers. -/
theorem escort_renyi_variational_identity (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ) :
    (⨅ q : ProbabilityVector ι, divergence q.1 p + max 0 (entropy q.1 - c) / 2) =
      ⨆ α : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2},
        (α.1 - 1) / α.1 * (renyiEntropy p α.1 - c) := by
  rw [show (⨅ q : ProbabilityVector ι, divergence q.1 p + max 0 (entropy q.1 - c) / 2) =
    (⨅ q : ProbabilityVector ι, primalObjective p c q.1) from rfl,
    escort_variational_identity p hp hs c]
  congr 1
  funext α
  exact dualObjective_eq_renyi p hs c α.1 α.2

abbrev PositiveSupport (p : ι → ℝ) := {i : ι // 0 < p i}

def supportLaw (p : ι → ℝ) (i : PositiveSupport p) : ℝ := p i.1

theorem positiveSupport_sum (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : PositiveSupport p, f (p i.1)) = ∑ i, f (p i) := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < p i) (fun i => f (p i))
  have hz : (∑ i : {i : ι // ¬0 < p i}, f (p i.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have he : p i.1 = 0 := le_antisymm (le_of_not_gt i.2) (hp i.1)
    rw [he, hf]
  rw [hz, add_zero] at h
  exact h

theorem positiveSupport_nonempty (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : Nonempty (PositiveSupport p) := by
  by_contra hn
  have hall (i : ι) : p i = 0 := by
    apply le_antisymm _ (hp i)
    apply le_of_not_gt
    intro h
    exact hn ⟨⟨i, h⟩⟩
  have hz : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => hall i
  linarith

theorem supportLaw_sum (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : ∑ i, supportLaw p i = 1 := by
  exact (positiveSupport_sum p hp id rfl).trans hs

theorem supportLaw_entropy (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    entropy (supportLaw p) = entropy p := by
  rw [entropy_eq_neg_sum, entropy_eq_neg_sum]
  congr 1
  exact positiveSupport_sum p hp (fun x => x * Real.log x) (by simp)

theorem supportLaw_renyi (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (α : ℝ) (hα : 0 < α) :
    renyiEntropy (supportLaw p) α = renyiEntropy p α := by
  by_cases h1 : α = 1
  · simp only [renyiEntropy, h1, ite_true]
    exact supportLaw_entropy p hp
  · simp only [renyiEntropy, h1, ite_false]
    congr 2
    exact positiveSupport_sum p hp (fun x => x ^ α) (Real.zero_rpow (ne_of_gt hα))

/-- The exact variational identity for a nonnegative finite law. Relative
entropy is correctly evaluated on the positive support; forbidden trial mass
on zero eigenvalues is not assigned a finite totalized-log divergence. -/
theorem nonnegative_escort_renyi_variational_identity (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ) :
    (⨅ q : ProbabilityVector (PositiveSupport p),
      divergence q.1 (supportLaw p) + max 0 (entropy q.1 - c) / 2) =
      ⨆ α : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2},
        (α.1 - 1) / α.1 * (renyiEntropy p α.1 - c) := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  rw [escort_renyi_variational_identity (supportLaw p) (fun i => i.2)
    (supportLaw_sum p hp hs) c]
  congr 1
  funext α
  rw [supportLaw_renyi p hp α.1 (lt_of_lt_of_le zero_lt_one α.2.1)]

/-- The full escort variational identity for the actual eigenspectrum of a
complex PSD trace-one matrix, including singular states. -/
theorem density_escort_renyi_variational_identity
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef ∧ X.trace = 1) (c : ℝ) :
    (⨅ q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues),
      divergence q.1 (supportLaw hX.1.isHermitian.eigenvalues) +
        max 0 (entropy q.1 - c) / 2) =
      ⨆ α : {α : ℝ // α ∈ Set.Icc (1 : ℝ) 2},
        (α.1 - 1) / α.1 * (renyiEntropy hX.1.isHermitian.eigenvalues α.1 - c) := by
  exact nonnegative_escort_renyi_variational_identity hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) c

theorem escort_zero (p : ι → ℝ) :
    escort p 0 = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  ext i
  simp [escort, partition]

theorem escort_zero_entropy (p : ι → ℝ) :
    entropy (escort p 0) = Real.log (Fintype.card ι) := by
  rw [entropy_eq_neg_sum, escort_zero]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp

def directDualObjective (p : ι → ℝ) (c α : ℝ) : ℝ :=
  ((1 - α) * c - Real.log (partition p α)) / α

/-- Strict-direct weak duality on the positive support. -/
theorem direct_variational_lower (p q : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (c α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hc : c ≤ entropy q) :
    directDualObjective p c α ≤ divergence q p := by
  have hg := divergence_nonneg q (escort p α) hq hqs
    (escort_pos p hp α) (escort_sum p hp α)
  rw [escort_divergence_identity q p hqs hp α] at hg
  unfold directDualObjective
  apply (div_le_iff₀ hα.1).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hα.2.le) (sub_nonneg.mpr hc)]

theorem escort_direct_eq (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (c α : ℝ) (hα : 0 < α) (hc : entropy (escort p α) = c) :
    divergence (escort p α) p = directDualObjective p c α := by
  have he := escort_divergence_identity (escort p α) p (escort_sum p hp α) hp α
  rw [divergence_self, hc] at he
  unfold directDualObjective
  apply (eq_div_iff (ne_of_gt hα)).mpr
  nlinarith

/-- An entropy-c escort exists in the open interval (0,1) in exactly the
strict-direct regime; both endpoints are excluded by strict inequalities. -/
theorem strict_direct_escort_exists (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card ι)) :
    ∃ α ∈ Set.Ioo (0 : ℝ) 1, entropy (escort p α) = c := by
  have hc : c ∈ Set.Icc (entropy (escort p 1)) (entropy (escort p 0)) := by
    rw [escort_one p hs, escort_zero_entropy p]
    exact ⟨hlo.le, hhi.le⟩
  obtain ⟨α, hα, hE⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    (escort_entropy_continuous p hp).continuousOn hc
  change entropy (escort p α) = c at hE
  have h0 : α ≠ 0 := by
    intro h
    rw [h, escort_zero_entropy p] at hE
    linarith
  have h1 : α ≠ 1 := by
    intro h
    rw [h, escort_one p hs] at hE
    linarith
  exact ⟨α, ⟨lt_of_le_of_ne hα.1 (Ne.symm h0), lt_of_le_of_ne hα.2 h1⟩, hE⟩

/-- Complete strict-direct scalar minimizer/maximizer certificate, retaining
the strict entropy and support-rank boundaries. -/
theorem strict_direct_variational_certificate (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card ι)) :
    ∃ q : ι → ℝ, ∃ α : ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      entropy q = c ∧ α ∈ Set.Ioo (0 : ℝ) 1 ∧
      divergence q p = directDualObjective p c α ∧
      (∀ r : ι → ℝ, (∀ i, 0 ≤ r i) → (∑ i, r i = 1) → c ≤ entropy r →
        divergence q p ≤ divergence r p) ∧
      (∀ β ∈ Set.Ioo (0 : ℝ) 1, directDualObjective p c β ≤ directDualObjective p c α) := by
  obtain ⟨α, hα, hE⟩ := strict_direct_escort_exists p hp hs c hlo hhi
  have he := escort_direct_eq p hp c α hα.1 hE
  refine ⟨escort p α, α, (fun i => (escort_pos p hp α i).le), escort_sum p hp α,
    hE, hα, he, ?_, ?_⟩
  · intro r hr hrs hc
    rw [he]
    exact direct_variational_lower p r hp hr hrs c α hα hc
  · intro β hβ
    rw [← he]
    exact direct_variational_lower p (escort p α) hp (fun i => (escort_pos p hp α i).le)
      (escort_sum p hp α) c β hβ hE.ge

theorem directDualObjective_eq_renyi (p : ι → ℝ) (c α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    directDualObjective p c α = (1 - α) / α * (c - renyiEntropy p α) := by
  have h1 : α ≠ 1 := ne_of_lt hα.2
  have h0 : α ≠ 0 := ne_of_gt hα.1
  have hd : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  simp only [directDualObjective, renyiEntropy, h1, ite_false]
  field_simp

/-- The exact strict-direct relative-entropy/Renyi variational formula. -/
theorem strict_direct_renyi_variational_identity (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card ι)) :
    (⨅ q : {q : ProbabilityVector ι // c ≤ entropy q.1}, divergence q.1.1 p) =
      ⨆ α : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1},
        (1 - α.1) / α.1 * (c - renyiEntropy p α.1) := by
  obtain ⟨q, α, hq, hqs, hE, hα, he, hmin, hmax⟩ :=
    strict_direct_variational_certificate p hp hs c hlo hhi
  let q0 : {q : ProbabilityVector ι // c ≤ entropy q.1} := ⟨⟨q, hq, hqs⟩, hE.ge⟩
  let α0 : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1} := ⟨α, hα⟩
  letI : Nonempty {q : ProbabilityVector ι // c ≤ entropy q.1} := ⟨q0⟩
  letI : Nonempty {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1} := ⟨α0⟩
  have hprimal : BddBelow (Set.range (fun r : {q : ProbabilityVector ι // c ≤ entropy q.1} =>
      divergence r.1.1 p)) := by
    refine ⟨divergence q p, ?_⟩
    rintro v ⟨r, rfl⟩
    exact hmin r.1.1 r.1.2.1 r.1.2.2 r.2
  have hdual : BddAbove (Set.range (fun β : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1} =>
      directDualObjective p c β.1)) := by
    refine ⟨directDualObjective p c α, ?_⟩
    rintro v ⟨β, rfl⟩
    exact hmax β.1 β.2
  have hInf : (⨅ r : {q : ProbabilityVector ι // c ≤ entropy q.1}, divergence r.1.1 p) =
      divergence q p := le_antisymm (ciInf_le hprimal q0)
        (le_ciInf fun r => hmin r.1.1 r.1.2.1 r.1.2.2 r.2)
  have hSup : (⨆ β : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1}, directDualObjective p c β.1) =
      directDualObjective p c α := le_antisymm (ciSup_le fun β => hmax β.1 β.2) (le_ciSup hdual α0)
  calc
    _ = divergence q p := hInf
    _ = directDualObjective p c α := he
    _ = ⨆ β : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1}, directDualObjective p c β.1 := hSup.symm
    _ = _ := by congr 1; funext β; exact directDualObjective_eq_renyi p c β.1 β.2

theorem nonnegative_strict_direct_renyi_variational_identity (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ)
    (hlo : entropy p < c) (hhi : c < Real.log (Fintype.card (PositiveSupport p))) :
    (⨅ q : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
      divergence q.1.1 (supportLaw p)) =
      ⨆ α : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1},
        (1 - α.1) / α.1 * (c - renyiEntropy p α.1) := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  have hlo' : entropy (supportLaw p) < c := by rw [supportLaw_entropy p hp]; exact hlo
  rw [strict_direct_renyi_variational_identity (supportLaw p) (fun i => i.2)
    (supportLaw_sum p hp hs) c hlo' hhi]
  congr 1
  funext α
  rw [supportLaw_renyi p hp α.1 α.2.1]

theorem density_positiveSupport_card_eq_rank (X : Matrix ι ι ℂ) (hX : X.PosSemidef) :
    Fintype.card (PositiveSupport hX.isHermitian.eigenvalues) = X.rank := by
  let e : PositiveSupport hX.isHermitian.eigenvalues ≃
      {i : ι // hX.isHermitian.eigenvalues i ≠ 0} :=
    { toFun := fun i => ⟨i.1, ne_of_gt i.2⟩
      invFun := fun i => ⟨i.1, lt_of_le_of_ne (hX.eigenvalues_nonneg i.1) (Ne.symm i.2)⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [Fintype.card_congr e, hX.isHermitian.rank_eq_card_non_zero_eigs]

/-- The paper's strict-direct scalar identity on the actual positive
eigensupport, with exactly H(p) < c < log(rank X), for singular densities too. -/
theorem density_strict_direct_renyi_variational_identity (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) (c : ℝ)
    (hlo : entropy hX.1.isHermitian.eigenvalues < c)
    (hhi : c < Real.log X.rank) :
    (⨅ q : {q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues) //
        c ≤ entropy q.1}, divergence q.1.1 (supportLaw hX.1.isHermitian.eigenvalues)) =
      ⨆ α : {α : ℝ // α ∈ Set.Ioo (0 : ℝ) 1},
        (1 - α.1) / α.1 * (c - renyiEntropy hX.1.isHermitian.eigenvalues α.1) := by
  exact nonnegative_strict_direct_renyi_variational_identity hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) c hlo
    (by rw [density_positiveSupport_card_eq_rank X hX.1]; exact hhi)

end
end ExtractionSpectrum
