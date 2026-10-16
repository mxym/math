import Deviation.EntropyPerturbation

open scoped BigOperators Topology ComplexOrder
open Filter ExtractionSpectrum Matrix

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The matching strict-direct missed-mass lower bound, uniform over every
selected finite word set and valid at any moving cardinality rate. All zero
atoms are handled on the positive support inside the variational exponent. -/
theorem iid_subset_tail_strict_direct (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀))
    (hlo : entropy p < c₀) (hhi : c₀ < Real.log (Fintype.card (PositiveSupport p)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c k) →
      Real.exp (-(k:ℝ)*(strictDirectExponent p c₀+ε)) ≤ 1-wordMass p k B := by
  obtain ⟨q,hq,hqs,hSupport,hqH,hqD⟩ :=
    strictDirectExponent_approx_above p hp hs c₀ hlo hhi (ε/2) (by linarith)
  let c₁ := (c₀+entropy q)/2
  have hc1 : c₀ < c₁ := by dsimp [c₁]; linarith
  have hcq : c₁ < entropy q := by dsimp [c₁]; linarith
  filter_upwards [iid_subset_tail_eventual_lower p q hp hs hq hqs hSupport c₁ hcq
    (ε/2) (by linarith),hc.eventually (Iio_mem_nhds hc1)] with k hk hck
  intro B hB
  have hB' : (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c₁) := hB.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hck.le (Nat.cast_nonneg k)))
  have htail := hk B hB'
  apply (Real.exp_le_exp.mpr _).trans htail
  exact mul_le_mul_of_nonpos_left (by linarith : divergence q p+ε/2 ≤ strictDirectExponent p c₀+ε)
    (neg_nonpos.mpr (Nat.cast_nonneg k))

/-- The same statement for the actual spectral law of a complex density
matrix; the upper endpoint is its true matrix rank. -/
theorem density_subset_tail_strict_direct (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀))
    (hlo : entropy hX.1.isHermitian.eigenvalues < c₀) (hhi : c₀ < Real.log X.rank)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c k) →
      Real.exp (-(k:ℝ)*(strictDirectExponent hX.1.isHermitian.eigenvalues c₀+ε)) ≤
        1-wordMass hX.1.isHermitian.eigenvalues k B := by
  have hr : Fintype.card (PositiveSupport hX.1.isHermitian.eigenvalues) = X.rank :=
    density_positiveSupport_card_eq_rank X hX.1
  apply iid_subset_tail_strict_direct hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) c c₀ hc hlo _ ε hε
  rw [hr]
  exact hhi

def entropyCardinalityCutoff (D : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  c k-(D:ℝ)*Real.log ((k:ℝ)+1)/k

theorem entropyCardinalityCutoff_tendsto (D : ℕ) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (entropyCardinalityCutoff D c) atTop (𝓝 c₀) := by
  have hlog : Tendsto (fun k : ℕ => (D:ℝ)*Real.log ((k:ℝ)+1)/k) atTop (𝓝 0) := by
    have h := polynomial_overhead_div_nat_tendsto_zero 0 (D:ℝ)
    simpa only [zero_add] using h
  change Tendsto (fun k : ℕ => c k-(D:ℝ)*Real.log ((k:ℝ)+1)/k) atTop (𝓝 c₀)
  simpa only [sub_zero] using hc.sub hlog

/-- A concrete entropy-selected set, independent of `p`, fits the cardinality
budget exactly, including its polynomial count of types. -/
theorem lowEntropyWords_cardinality_budget (c : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    ((lowEntropyWords (ι := ι) k (entropyCardinalityCutoff (Fintype.card ι) c k)).card:ℝ) ≤
      Real.exp ((k:ℝ)*c k) := by
  have h := lowEntropyWords_card_le (ι := ι) k (entropyCardinalityCutoff (Fintype.card ι) c k)
  apply h.trans_eq
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hpow : ((k+1:ℝ)^Fintype.card ι) = Real.exp ((Fintype.card ι:ℝ)*Real.log ((k:ℝ)+1)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hpow, ← Real.exp_add]
  congr 1
  unfold entropyCardinalityCutoff
  field_simp
  ring

/-- The uniform missed-mass converse matches an explicit source code up to
arbitrarily small exponential losses at every strict-direct moving rate. -/
theorem iid_subset_tail_matching (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀))
    (hlo : entropy p < c₀) (hhi : c₀ < Real.log (Fintype.card (PositiveSupport p)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (∀ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c k) →
        Real.exp (-(k:ℝ)*(strictDirectExponent p c₀+ε)) ≤ 1-wordMass p k B) ∧
      (∃ B : Finset (Fin k → ι), (B.card:ℝ) ≤ Real.exp ((k:ℝ)*c k) ∧
        1-wordMass p k B ≤ Real.exp (-(k:ℝ)*(strictDirectExponent p c₀-ε))) := by
  have hcut := entropyCardinalityCutoff_tendsto (Fintype.card ι) c c₀ hc
  have hupper := empiricalEntropyError_strict_direct_exponential p hp hs
    (entropyCardinalityCutoff (Fintype.card ι) c) c₀ hcut hlo hhi ε hε
  filter_upwards [iid_subset_tail_strict_direct p hp hs c c₀ hc hlo hhi ε hε,
    hupper,eventually_gt_atTop 0] with k hk hupperk hkpos
  refine ⟨hk,lowEntropyWords k (entropyCardinalityCutoff (Fintype.card ι) c k),
    lowEntropyWords_cardinality_budget c hkpos,?_⟩
  exact hupperk

end
end ExtractionDeviation
