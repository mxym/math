import ContinuumGeometric.RoutingInterfaces
import ContinuumGeometric.ShiftedActivation
import ContinuumGeometric.LocalSignatures

/-!
Finite candidate enumeration and strict output-window counts for the ORIGINAL
dyadic subsequence `dyadic (m*n)`. The coefficient shift and original tail are
explicit. No discretization of the exponent/coefficient rectangle is used.
-/
namespace ContinuumGeometric

open Set

/-- A stride strictly larger than `3/s₀`, selected without an existence axiom. -/
noncomputable def candidateStride (s₀ : ℝ) : ℕ := Nat.ceil (3 / s₀) + 2

theorem candidateStride_gap (s₀ : ℝ) (hs₀ : 0 < s₀) :
    0 < candidateStride s₀ ∧ 3 < (candidateStride s₀ : ℝ) * s₀ := by
  have hc : 3 / s₀ ≤ (Nat.ceil (3 / s₀) : ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hs₀).1 hc
  constructor
  · simp [candidateStride]
  · simp only [candidateStride, Nat.cast_add, Nat.cast_ofNat]
    nlinarith

theorem candidateStride_gt_div (s₀ : ℝ) (hs₀ : 0 < s₀) :
    3 / s₀ < (candidateStride s₀ : ℝ) :=
  (div_lt_iff₀ hs₀).2 (candidateStride_gap s₀ hs₀).2

/-- The paper's absolute-position candidate budget; its `+1` is retained. -/
noncomputable def candidateLabelBudget (U T : ℝ) (k : ℤ) : ℕ :=
  Nat.ceil ((U + T + |(k : ℝ)|) / 3) + 1

theorem active_subsequence_label_lt_budget (s₀ s₁ U T u v : ℝ)
    (m n : ℕ) (k : ℤ) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hv : v ≤ U + T) (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation (m * n) k u v) :
    n < candidateLabelBudget U T k := by
  have hmul : 3 * (n : ℝ) ≤ p.1.1 * (m * n : ℕ) := by
    have h₁ := mul_le_mul_of_nonneg_left p.1.2.1 (Nat.cast_nonneg m)
    have h₂ := mul_le_mul_of_nonneg_right (hgap.trans h₁) (Nat.cast_nonneg n)
    push_cast
    nlinarith [h₂]
  have hbound : (n : ℝ) < (U + T + |(k : ℝ)|) / 3 := by
    have hk : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
    have ha : p.1.1 * (m * n : ℕ) - (k : ℝ) < v := hp.2
    linarith
  have hn : n < Nat.ceil ((U + T + |(k : ℝ)|) / 3) := Nat.lt_ceil.2 hbound
  exact hn.trans (Nat.lt_succ_self _)

/-- The guard uses the ORIGINAL requested tail `N`, rather than a label tail. -/
theorem active_original_index_tail (s₀ s₁ u v : ℝ) (n N : ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (htail : s₁ * N ≤ u + (k : ℝ))
    (p : PowerParams s₀ s₁) (hp : p ∈ powerActivation n k u v) : N ≤ n := by
  have hs : 0 < p.1.1 := hs₀.trans_le p.1.2.1
  have hNs : p.1.1 * (N : ℝ) ≤ s₁ * N :=
    mul_le_mul_of_nonneg_right p.1.2.2 (Nat.cast_nonneg N)
  have hNn : (N : ℝ) < n := by
    have hlo : u < p.1.1 * n - (k : ℝ) := hp.1
    nlinarith
  exact_mod_cast hNn.le

/-- Every potentially active original subsequence index has a finite address. -/
noncomputable def candidateOriginalIndices (m N : ℕ) (U T : ℝ) (k : ℤ) : Finset ℕ :=
  ((Finset.range (candidateLabelBudget U T k)).filter (fun n => N ≤ m * n)).image
    (fun n => m * n)

theorem mem_candidateOriginalIndices_iff (m N j : ℕ) (U T : ℝ) (k : ℤ) :
    j ∈ candidateOriginalIndices m N U T k ↔
      ∃ n : ℕ, n < candidateLabelBudget U T k ∧ N ≤ m * n ∧ m * n = j := by
  simp only [candidateOriginalIndices, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  aesop

theorem candidateOriginalIndices_card_le (m N : ℕ) (U T : ℝ) (k : ℤ) :
    (candidateOriginalIndices m N U T k).card ≤ candidateLabelBudget U T k := by
  exact Finset.card_image_le.trans
    ((Finset.card_filter_le _ _).trans (by simp))

theorem active_original_index_mem_candidates (s₀ s₁ U T u v : ℝ)
    (m n N : ℕ) (k : ℤ) (hs₀ : 0 < s₀) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hv : v ≤ U + T) (htail : s₁ * N ≤ u + (k : ℝ))
    (p : PowerParams s₀ s₁) (hp : p ∈ powerActivation (m * n) k u v) :
    m * n ∈ candidateOriginalIndices m N U T k := by
  exact (mem_candidateOriginalIndices_iff _ _ _ _ _ _).2
    ⟨n, active_subsequence_label_lt_budget _ _ _ _ _ _ _ _ _ hgap hv p hp,
      active_original_index_tail _ _ _ _ _ _ _ hs₀ htail p hp, rfl⟩

/-- Natural endpoints supplied by the actual finite routing template. -/
theorem active_original_index_mem_candidates_nat (s₀ s₁ : ℝ)
    (U T u v m n N : ℕ) (k : ℤ) (hs₀ : 0 < s₀)
    (hgap : 3 ≤ (m : ℝ) * s₀) (hv : v ≤ U + T)
    (htail : s₁ * N ≤ (u : ℝ) + (k : ℝ)) (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation (m * n) k u v) :
    m * n ∈ candidateOriginalIndices m N U T k := by
  apply active_original_index_mem_candidates s₀ s₁ U T u v m n N k hs₀ hgap
  · exact_mod_cast hv
  · exact htail
  · exact hp

/-- Generic upper count for an OPEN arithmetic output window, retaining endpoints. -/
theorem activation_card_upper (u ℓ δ : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) :
    ((activeIntegers u ℓ δ).card : ℝ) ≤ 1 + ℓ / δ := by
  rw [activation_card_exact u ℓ δ hδ hℓ]
  have hf := Int.lt_floor_add_one (u / δ)
  have hc := Int.ceil_lt_add_one ((u + ℓ) / δ)
  rw [add_div] at hc ⊢
  linarith

/-- Active labels use `u < s*(m*n)-k < u+ℓ`, with BOTH endpoints strict. -/
noncomputable def activeSubsequenceLabels {s₀ s₁ : ℝ}
    (m : ℕ) (u ℓ : ℝ) (k : ℤ) (p : PowerParams s₀ s₁) : Finset ℕ :=
  activeNaturals (u + (k : ℝ)) ℓ ((m : ℝ) * p.1.1)

noncomputable def activeOriginalIndices {s₀ s₁ : ℝ}
    (m : ℕ) (u ℓ : ℝ) (k : ℤ) (p : PowerParams s₀ s₁) : Finset ℕ :=
  (activeSubsequenceLabels m u ℓ k p).image (fun n => m * n)

theorem mem_activeSubsequenceLabels_iff (s₀ s₁ u ℓ : ℝ) (m n : ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hshift : 0 ≤ u + (k : ℝ))
    (p : PowerParams s₀ s₁) :
    n ∈ activeSubsequenceLabels m u ℓ k p ↔
      p ∈ powerActivation (m * n) k u (u + ℓ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < (m : ℝ) * p.1.1 := mul_pos hmr (hs₀.trans_le p.1.2.1)
  rw [activeSubsequenceLabels, mem_activeNaturals_iff _ _ _ hδ hshift]
  change _ ↔ u < p.1.1 * (m * n : ℕ) - (k : ℝ) ∧
    p.1.1 * (m * n : ℕ) - (k : ℝ) < u + ℓ
  push_cast
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem activeOriginalIndices_card (s₀ s₁ u ℓ : ℝ) (m : ℕ) (k : ℤ)
    (hm : 0 < m) (p : PowerParams s₀ s₁) :
    (activeOriginalIndices m u ℓ k p).card = (activeSubsequenceLabels m u ℓ k p).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.mul_left_cancel hm h)

theorem activeOriginalIndices_count_bounds (s₀ s₁ u ℓ : ℝ) (m N : ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hℓ : 2 * ((m : ℝ) * s₁) ≤ ℓ) (htail : s₁ * N ≤ u + (k : ℝ))
    (p : PowerParams s₀ s₁) :
    ℓ / (2 * ((m : ℝ) * s₁)) ≤ (activeOriginalIndices m u ℓ k p).card ∧
      ((activeOriginalIndices m u ℓ k p).card : ℝ) ≤ 1 + ℓ / 3 ∧
      ∀ j ∈ activeOriginalIndices m u ℓ k p,
        N ≤ j ∧ p ∈ powerActivation j k u (u + ℓ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < p.1.1 := hs₀.trans_le p.1.2.1
  have hs₁ : 0 < s₁ := hs.trans_le p.1.2.2
  have hδ : 0 < (m : ℝ) * p.1.1 := mul_pos hmr hs
  have hδD : (m : ℝ) * p.1.1 ≤ (m : ℝ) * s₁ :=
    mul_le_mul_of_nonneg_left p.1.2.2 hmr.le
  have hshift : 0 ≤ u + (k : ℝ) := (mul_nonneg hs₁.le (Nat.cast_nonneg N)).trans htail
  have hℓpos : 0 < ℓ := (by positivity : 0 < 2 * ((m : ℝ) * s₁)).trans_le hℓ
  have hcard : (activeOriginalIndices m u ℓ k p).card =
      (activeIntegers (u + (k : ℝ)) ℓ ((m : ℝ) * p.1.1)).card := by
    rw [activeOriginalIndices_card _ _ _ _ _ _ hm p, activeSubsequenceLabels,
      activeNaturals_card _ _ _ hδ hshift]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]
    exact activation_card_uniform _ _ _ _ hδ hδD hℓ
  · rw [hcard]
    have hδ₃ : 3 ≤ (m : ℝ) * p.1.1 :=
      hgap.trans (mul_le_mul_of_nonneg_left p.1.2.1 hmr.le)
    have hd := div_le_div_of_nonneg_left hℓpos.le (by norm_num : (0 : ℝ) < 3) hδ₃
    exact (activation_card_upper _ _ _ hδ hℓpos).trans (by linarith)
  · intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    have hp := (mem_activeSubsequenceLabels_iff _ _ _ _ _ _ _ hs₀ hm hshift p).1 hn
    exact ⟨active_original_index_tail _ _ _ _ _ _ _ hs₀ htail p hp, hp⟩

theorem mem_activeOriginalIndices_iff (s₀ s₁ u ℓ : ℝ) (m j : ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hshift : 0 ≤ u + (k : ℝ))
    (p : PowerParams s₀ s₁) :
    j ∈ activeOriginalIndices m u ℓ k p ↔
      (∃ n : ℕ, m * n = j) ∧ p ∈ powerActivation j k u (u + ℓ) := by
  constructor
  · intro hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    exact ⟨⟨n, rfl⟩,
      (mem_activeSubsequenceLabels_iff _ _ _ _ _ _ _ hs₀ hm hshift p).1 hn⟩
  · rintro ⟨⟨n, rfl⟩, hp⟩
    exact Finset.mem_image.2 ⟨n,
      (mem_activeSubsequenceLabels_iff _ _ _ _ _ _ _ hs₀ hm hshift p).2 hp, rfl⟩

/-- Keep EXACTLY candidate edge-index pairs active somewhere in the continuum.
The existential quantifier ranges over the full compact parameter rectangle.
-/
noncomputable def potentialOriginalPairs (s₀ s₁ : ℝ) {W : ℕ}
    (m N : ℕ) (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ) :
    Finset (Fin W × ℕ) := by
  classical
  exact (Finset.univ.product (candidateOriginalIndices m N U T k)).filter
    (fun q => ∃ p : PowerParams s₀ s₁,
      p ∈ powerActivation q.2 k (windows q.1).1 (windows q.1).2)

theorem mem_potentialOriginalPairs_iff (s₀ s₁ : ℝ) {W : ℕ}
    (m N : ℕ) (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ)
    (q : Fin W × ℕ) :
    q ∈ potentialOriginalPairs s₀ s₁ m N U T k windows ↔
      q.2 ∈ candidateOriginalIndices m N U T k ∧
        ∃ p : PowerParams s₀ s₁,
          p ∈ powerActivation q.2 k (windows q.1).1 (windows q.1).2 := by
  classical
  simp [potentialOriginalPairs]

theorem potentialOriginalPairs_card_le (s₀ s₁ : ℝ) {W : ℕ}
    (m N : ℕ) (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ) :
    (potentialOriginalPairs s₀ s₁ m N U T k windows).card ≤
      W * candidateLabelBudget U T k := by
  classical
  apply (Finset.card_filter_le _ _).trans
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
    Fintype.card_fin]
  exact Nat.mul_le_mul_left W (candidateOriginalIndices_card_le m N U T k)

theorem active_pair_mem_potentialOriginalPairs (s₀ s₁ U T : ℝ) {W : ℕ}
    (m n N : ℕ) (k : ℤ) (windows : Fin W → ℝ × ℝ)
    (hs₀ : 0 < s₀) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hv : ∀ e, (windows e).2 ≤ U + T)
    (htail : ∀ e, s₁ * N ≤ (windows e).1 + (k : ℝ))
    (p : PowerParams s₀ s₁) (e : Fin W)
    (hp : p ∈ powerActivation (m * n) k (windows e).1 (windows e).2) :
    (e, m * n) ∈ potentialOriginalPairs s₀ s₁ m N U T k windows := by
  apply (mem_potentialOriginalPairs_iff _ _ _ _ _ _ _ _ _).2
  exact ⟨active_original_index_mem_candidates s₀ s₁ U T _ _ m n N k hs₀
    hgap (hv e) (htail e) p hp, ⟨p, hp⟩⟩

/-- Every potentially active original index in the template is enumerated,
with its ACTUAL strict window. This is an equivalence, not just an upper count.
-/
theorem mem_potentialOriginalPairs_exact (s₀ s₁ U T : ℝ) {W : ℕ}
    (m N : ℕ) (k : ℤ) (windows : Fin W → ℝ × ℝ)
    (hs₀ : 0 < s₀) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hv : ∀ e, (windows e).2 ≤ U + T)
    (htail : ∀ e, s₁ * N ≤ (windows e).1 + (k : ℝ))
    (q : Fin W × ℕ) :
    q ∈ potentialOriginalPairs s₀ s₁ m N U T k windows ↔
      (∃ n : ℕ, m * n = q.2) ∧ ∃ p : PowerParams s₀ s₁,
        p ∈ powerActivation q.2 k (windows q.1).1 (windows q.1).2 := by
  constructor
  · intro hq
    obtain ⟨hc, hp⟩ := (mem_potentialOriginalPairs_iff _ _ _ _ _ _ _ _ _).1 hq
    obtain ⟨n, _, _, hn⟩ := (mem_candidateOriginalIndices_iff _ _ _ _ _ _).1 hc
    exact ⟨⟨n, hn⟩, hp⟩
  · rintro ⟨⟨n, hn⟩, p, hp⟩
    obtain ⟨e, j⟩ := q
    dsimp at hn hp
    subst j
    exact active_pair_mem_potentialOriginalPairs _ _ _ _ _ _ _ _ _ hs₀ hgap hv htail p e hp

/-- Canonical finite reindexing consumed by `LocalSignatures`'s `Fin P` API. -/
noncomputable def candidatePairEnumeration {W : ℕ} (pairs : Finset (Fin W × ℕ)) :
    Fin pairs.card ≃ {q // q ∈ pairs} := pairs.equivFin.symm

noncomputable def candidatePairEdge {W : ℕ} (pairs : Finset (Fin W × ℕ))
    (i : Fin pairs.card) : Fin W := (candidatePairEnumeration pairs i).1.1

noncomputable def candidatePairIndex {W : ℕ} (pairs : Finset (Fin W × ℕ))
    (i : Fin pairs.card) : ℕ := (candidatePairEnumeration pairs i).1.2

theorem candidatePairEnumeration_complete {W : ℕ} (pairs : Finset (Fin W × ℕ))
    (q : Fin W × ℕ) (hq : q ∈ pairs) :
    ∃ i : Fin pairs.card, candidatePairEdge pairs i = q.1 ∧
      candidatePairIndex pairs i = q.2 := by
  obtain ⟨i, hi⟩ := (candidatePairEnumeration pairs).surjective ⟨q, hq⟩
  exact ⟨i, by simp [candidatePairEdge, hi], by simp [candidatePairIndex, hi]⟩

theorem candidatePairEnumeration_injective {W : ℕ} (pairs : Finset (Fin W × ℕ)) :
    Function.Injective (fun i : Fin pairs.card =>
      (candidatePairEdge pairs i, candidatePairIndex pairs i)) := by
  intro i j hij
  apply (candidatePairEnumeration pairs).injective
  apply Subtype.ext
  exact hij

/-- The existing exact continuum entropy theorem on ACTUAL candidate addresses,
with the candidate-count cost proved above. Zero-sign strata and inactive strict
endpoints are already included by `actual_local_representatives_entropy_bound`.
-/
theorem potentialOriginalPairs_entropy_bound (s₀ s₁ x : ℝ) {W : ℕ}
    (hs : s₀ ≤ s₁) (m N U T : ℕ) (k : ℤ) (u v b : Fin W → ℕ) (ell : ℕ)
    (hspan : ∀ e, b e + 1 ≤ u e + 2 * ell) :
    let pairs := potentialOriginalPairs s₀ s₁ m N U T k
      (fun e => ((u e : ℝ), (v e : ℝ)))
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 *
        (W * candidateLabelBudget U T k * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        localGridVector x (candidatePairIndex pairs)
          (fun i => 2 ^ (b (candidatePairEdge pairs i) + 3)) k
          (fun i => ((u (candidatePairEdge pairs i) : ℝ),
            (v (candidatePairEdge pairs i) : ℝ))) r =
        localGridVector x (candidatePairIndex pairs)
          (fun i => 2 ^ (b (candidatePairEdge pairs i) + 3)) k
          (fun i => ((u (candidatePairEdge pairs i) : ℝ),
            (v (candidatePairEdge pairs i) : ℝ))) p := by
  dsimp only
  let pairs := potentialOriginalPairs s₀ s₁ m N U T k
    (fun e => ((u e : ℝ), (v e : ℝ)))
  obtain ⟨reps, hc, hr⟩ := actual_local_representatives_entropy_bound s₀ s₁ x hs
    (candidatePairIndex pairs) (fun i => u (candidatePairEdge pairs i))
    (fun i => v (candidatePairEdge pairs i)) (fun i => b (candidatePairEdge pairs i))
    k ell (fun i => hspan (candidatePairEdge pairs i))
  refine ⟨reps, hc.trans ?_, hr⟩
  have hp : pairs.card ≤ W * candidateLabelBudget U T k :=
    potentialOriginalPairs_card_le s₀ s₁ m N U T k _
  gcongr

/-- A concrete sufficiently late start for every requested ORIGINAL tail. -/
noncomputable def candidateTailStart (s₁ : ℝ) (N : ℕ) (k : ℤ) : ℕ :=
  Nat.ceil (s₁ * N + |(k : ℝ)|) + 5

theorem candidateTailStart_guards (s₁ : ℝ) (N U : ℕ) (k : ℤ)
    (hU : candidateTailStart s₁ N k ≤ U) :
    4 ≤ U ∧ s₁ * N ≤ (U : ℝ) + (k : ℝ) := by
  have hceil : s₁ * N + |(k : ℝ)| ≤
      (Nat.ceil (s₁ * N + |(k : ℝ)|) : ℝ) := Nat.le_ceil _
  have hUr : (candidateTailStart s₁ N k : ℝ) ≤ U := by exact_mod_cast hU
  have hk := neg_abs_le (k : ℝ)
  refine ⟨by unfold candidateTailStart at hU; omega, ?_⟩
  simp only [candidateTailStart, Nat.cast_add, Nat.cast_ofNat] at hUr
  linarith

theorem candidateLabelBudget_le_nat (U T : ℕ) (k : ℤ) :
    candidateLabelBudget U T k ≤ U + T + k.natAbs + 2 := by
  have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hc : Nat.ceil (((U : ℝ) + T + |(k : ℝ)|) / 3) ≤ U + T + k.natAbs := by
    rw [Nat.ceil_le]
    push_cast
    rw [habs]
    have hU := Nat.cast_nonneg (α := ℝ) U
    have hT := Nat.cast_nonneg (α := ℝ) T
    have hk := abs_nonneg (k : ℝ)
    linarith
  unfold candidateLabelBudget
  omega

/-- Equality with either activation endpoint is inactive, exactly as required
by the closed missed-center relation and continuum representatives.
-/
theorem original_activation_endpoints_inactive (s₀ s₁ u v : ℝ) (j : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁)
    (hboundary : p.1.1 * j - (k : ℝ) = u ∨ p.1.1 * j - (k : ℝ) = v) :
    p ∉ powerActivation j k u v := by
  intro hp
  rcases hboundary with h | h <;> change u < _ ∧ _ < v at hp <;> rcases hp with ⟨hl, hu⟩
  · linarith
  · linarith

/-- Actual active pairs across a vertex's prescribed outgoing windows. -/
noncomputable def activeOriginalPairs {s₀ s₁ : ℝ} {W : ℕ}
    (m : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (p : PowerParams s₀ s₁) :
    Finset (Fin W × ℕ) := by
  classical
  exact Finset.univ.biUnion fun e =>
    (activeOriginalIndices m (u e) ell k p).image (fun j => (e, j))

theorem activeOriginalPairs_card (s₀ s₁ : ℝ) {W : ℕ}
    (m : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (p : PowerParams s₀ s₁) :
    (activeOriginalPairs m u ell k p).card =
      ∑ e : Fin W, (activeOriginalIndices m (u e) ell k p).card := by
  classical
  unfold activeOriginalPairs
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
  · intro e _ f _ hef
    apply Finset.disjoint_left.2
    intro q hq hq'
    obtain ⟨j, _, hj⟩ := Finset.mem_image.1 hq
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.1 hq'
    exact hef (Prod.mk.inj (hj.trans hj'.symm)).1

theorem mem_activeOriginalPairs_iff (s₀ s₁ : ℝ) {W : ℕ}
    (m : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (p : PowerParams s₀ s₁)
    (q : Fin W × ℕ) :
    q ∈ activeOriginalPairs m u ell k p ↔ q.2 ∈ activeOriginalIndices m (u q.1) ell k p := by
  classical
  constructor
  · intro hq
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨j, hj, h⟩ := Finset.mem_image.1 he
    subst q
    exact hj
  · intro hj
    exact Finset.mem_biUnion.2 ⟨q.1, Finset.mem_univ _, Finset.mem_image.2 ⟨q.2, hj, rfl⟩⟩

open scoped Classical in
/-- The finite continuum candidate list retains ALL active tests at every fixed
parameter, and the active subset equals the actual original arithmetic tests.
-/
theorem activeOriginalPairs_eq_potential_filter (s₀ s₁ U T : ℝ) {W : ℕ}
    (m N : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hv : ∀ e, u e + ell ≤ U + T)
    (htail : ∀ e, s₁ * N ≤ u e + (k : ℝ)) (p : PowerParams s₀ s₁) :
    activeOriginalPairs m u ell k p =
      (potentialOriginalPairs s₀ s₁ m N U T k (fun e => (u e, u e + ell))).filter
        (fun q => p ∈ powerActivation q.2 k (u q.1) (u q.1 + ell)) := by
  classical
  have hs₁ : 0 < s₁ := (hs₀.trans_le p.1.2.1).trans_le p.1.2.2
  have hshift : ∀ e, 0 ≤ u e + (k : ℝ) := fun e =>
    (mul_nonneg hs₁.le (Nat.cast_nonneg N)).trans (htail e)
  ext q
  rw [mem_activeOriginalPairs_iff, mem_activeOriginalIndices_iff _ _ _ _ _ _ _ hs₀ hm
    (hshift q.1) p, Finset.mem_filter]
  constructor
  · rintro ⟨⟨n, hn⟩, hp⟩
    have hq := (mem_potentialOriginalPairs_exact s₀ s₁ U T m N k
      (fun e => (u e, u e + ell)) hs₀ hgap hv htail q).2 ⟨⟨n, hn⟩, ⟨p, hp⟩⟩
    exact ⟨hq, hp⟩
  · rintro ⟨hq, hp⟩
    have hq' := (mem_potentialOriginalPairs_exact s₀ s₁ U T m N k
      (fun e => (u e, u e + ell)) hs₀ hgap hv htail q).1 hq
    exact ⟨hq'.1, hp⟩

theorem activeOriginalPairs_count_bounds (s₀ s₁ : ℝ) {W : ℕ}
    (m N : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hℓ : 2 * ((m : ℝ) * s₁) ≤ ell)
    (htail : ∀ e, s₁ * N ≤ u e + (k : ℝ)) (p : PowerParams s₀ s₁) :
    (W : ℝ) * (ell / (2 * ((m : ℝ) * s₁))) ≤
        (activeOriginalPairs m u ell k p).card ∧
      ((activeOriginalPairs m u ell k p).card : ℝ) ≤ (W : ℝ) * (1 + ell / 3) := by
  have hc : ((activeOriginalPairs m u ell k p).card : ℝ) =
      ∑ e : Fin W, ((activeOriginalIndices m (u e) ell k p).card : ℝ) := by
    rw [activeOriginalPairs_card, Nat.cast_sum]
  rw [hc]
  constructor
  · calc
      (W : ℝ) * (ell / (2 * ((m : ℝ) * s₁))) =
          ∑ _e : Fin W, ell / (2 * ((m : ℝ) * s₁)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun e _ =>
        (activeOriginalIndices_count_bounds s₀ s₁ (u e) ell m N k hs₀ hm hgap hℓ
          (htail e) p).1
  · calc
      _ ≤ ∑ _e : Fin W, (1 + ell / 3) := Finset.sum_le_sum fun e _ =>
        (activeOriginalIndices_count_bounds s₀ s₁ (u e) ell m N k hs₀ hm hgap hℓ
          (htail e) p).2.1
      _ = _ := by simp; ring

open scoped Classical in
theorem potentialOriginalPairs_active_count (s₀ s₁ U T : ℝ) {W : ℕ}
    (m N : ℕ) (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hℓ : 2 * ((m : ℝ) * s₁) ≤ ell) (hv : ∀ e, u e + ell ≤ U + T)
    (htail : ∀ e, s₁ * N ≤ u e + (k : ℝ)) (p : PowerParams s₀ s₁) :
    let active :=
      (potentialOriginalPairs s₀ s₁ m N U T k (fun e => (u e, u e + ell))).filter
        (fun q => p ∈ powerActivation q.2 k (u q.1) (u q.1 + ell))
    (W : ℝ) * (ell / (2 * ((m : ℝ) * s₁))) ≤ active.card ∧
      (active.card : ℝ) ≤ (W : ℝ) * (1 + ell / 3) := by
  dsimp only
  rw [← activeOriginalPairs_eq_potential_filter s₀ s₁ U T m N u ell k hs₀ hm hgap hv htail p]
  exact activeOriginalPairs_count_bounds s₀ s₁ m N u ell k hs₀ hm hgap hℓ htail p

open scoped Classical in
/-- Template-facing count for natural open endpoints `u` and `u+ell`.
In the paper the latter is `v_e+1`, while `b` is the finest subtree endpoint.
-/
theorem potentialOriginalPairs_active_count_nat (s₀ s₁ : ℝ) {W : ℕ}
    (m N U T ell : ℕ) (u : Fin W → ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hℓ : 2 * ((m : ℝ) * s₁) ≤ ell) (hv : ∀ e, u e + ell ≤ U + T)
    (htail : ∀ e, s₁ * N ≤ (u e : ℝ) + (k : ℝ)) (p : PowerParams s₀ s₁) :
    let active :=
      (potentialOriginalPairs s₀ s₁ m N U T k
        (fun e => ((u e : ℝ), ((u e + ell : ℕ) : ℝ)))).filter
        (fun q => p ∈ powerActivation q.2 k (u q.1) (u q.1 + ell : ℕ))
    (W : ℝ) * ((ell : ℝ) / (2 * ((m : ℝ) * s₁))) ≤ active.card ∧
      (active.card : ℝ) ≤ (W : ℝ) * (1 + (ell : ℝ) / 3) := by
  have hvr : ∀ e, (u e : ℝ) + ell ≤ (U : ℝ) + T := fun e => by exact_mod_cast hv e
  simpa only [Nat.cast_add] using
    potentialOriginalPairs_active_count s₀ s₁ U T m N (fun e => (u e : ℝ)) ell k
      hs₀ hm hgap hℓ hvr htail p

end ContinuumGeometric
