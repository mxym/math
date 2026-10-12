import ErdosSimilarityGrowingGaps.RoutingSampleMap
import ErdosSimilarityGrowingGaps.SequenceTransfer
import ErdosSimilarityGrowingGaps.RoutingAssembly
import ErdosSimilarityGrowingGaps.ScheduledAnnulus

namespace ErdosSimilarityGrowingGaps

open Set Filter Topology

/-!
Concrete first-ge transfer lemmas for a filled late annulus.  The hypotheses
are exactly the finite routing guards: every tested integer starts after the
annulus origin, its `D`-buffer stays inside the annulus, and the activation or
point margin absorbs that buffer.  No density or routing probability premise is
used here.
-/

/-- The first logarithmic sample has the required two-sided `D` bounds at every
integer test in the annulus. -/
theorem filled_firstGe_sample_bounds
    {Z : LogScale} {U R D : ℝ}
    (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ)
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U) :
    ∀ n : ℕ, n ∈ tests →
      (n : ℝ) ≤ Z.z (firstGeIndex Z (n : ℝ)) ∧
      Z.z (firstGeIndex Z (n : ℝ)) ≤ (n : ℝ) + D := by
  intro n hn
  have hU : 0 ≤ U := hfill.1.le
  have hRU : 0 < R := by linarith
  have hdiv : U / R ≤ U := by
    apply (div_le_iff₀ hRU).2
    nlinarith
  obtain ⟨m, hmlo, hmhi⟩ := hfill.sample_mem
    (hlo n hn) (hhi n hn)
  exact ⟨(firstGeIndex_spec Z (n : ℝ)).1,
    firstGeIndex_value_le_of_mem Z (n : ℝ) D m ⟨hmlo, hmhi⟩⟩

/-- Activation transfer for the first-ge sample map.  The endpoint equalities
are retained as non-strict bounds, while activation itself remains strict. -/
theorem filled_firstGe_sequence_activation
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    (hmargin : ∀ n : ℕ, n ∈ tests → ∀ e : Fin W,
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ))) :
    ∀ n : ℕ, n ∈ tests → ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      p ∈ sequenceWindowActivations Z (sample n) k windows := by
  intro n hn p hp
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hp
  have hbounds := filled_firstGe_sample_bounds hfill hR tests hlo hhi n hn
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by
    rw [hsample]
  rw [hsamp]
  exact sequence_activation_of_sample_interval windows e D p hK he
    hbounds.1 hbounds.2 (hmargin n hn e p he)

/-! A sharper activation variant only asks for annulus bounds on tests that
actually activate a parameter.  This is the form needed when a finite test
list contains harmless early indices; it avoids imposing the impossible
eventual condition `U / R ≤ N` on every enumerated test. -/

theorem filled_firstGe_sequence_activation_of_active_bounds
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hactiveBounds : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      U / R ≤ (n : ℝ) ∧ (n : ℝ) + D ≤ R * U)
    (hmargin : ∀ n : ℕ, n ∈ tests → ∀ e : Fin W,
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ))) :
    ∀ n : ℕ, n ∈ tests → ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      p ∈ sequenceWindowActivations Z (sample n) k windows := by
  intro n hn p hp
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hp
  have hbounds := hactiveBounds n hn p hp
  have hsample_mem : ∃ m : ℕ,
      (n : ℝ) ≤ Z.z m ∧ Z.z m ≤ (n : ℝ) + D :=
    hfill.sample_mem hbounds.1 hbounds.2
  obtain ⟨m, hmlo, hmhi⟩ := hsample_mem
  have hfirstlo : (n : ℝ) ≤ Z.z (firstGeIndex Z (n : ℝ)) :=
    (firstGeIndex_spec Z (n : ℝ)).1
  have hfirsthi : Z.z (firstGeIndex Z (n : ℝ)) ≤ (n : ℝ) + D :=
    firstGeIndex_value_le_of_mem Z (n : ℝ) D m ⟨hmlo, hmhi⟩
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by rw [hsample]
  rw [hsamp]
  exact sequence_activation_of_sample_interval windows e D p hK he
    hfirstlo hfirsthi (hmargin n hn e p he)

/-! The point estimate also admits the active-only form.  In a missed-center
 witness the parameter is already known to activate, so this is exactly the
 hypothesis needed by the inclusion argument. -/

theorem filled_firstGe_sequence_point_transfer_of_active_bounds
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hactiveBounds : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      U / R ≤ (n : ℝ) ∧ (n : ℝ) + D ≤ R * U)
    {G : Set ℝ} (ρ : ℝ)
    (hwidth : ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      p ∈ windowActivations n k windows →
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      |p.2.1 * ((2 : ℝ) ^ k)| *
          ((2 : ℝ) ^ (-((n : ℝ) * p.1.1)) -
            (2 : ℝ) ^ (-(((n : ℝ) + D) * p.1.1))) < ρ) :
    ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      p ∈ windowActivations n k windows →
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G := by
  intro n hn x p hp hideal
  have hbounds := hactiveBounds n hn p hp
  obtain ⟨m, hmlo, hmhi⟩ := hfill.sample_mem hbounds.1 hbounds.2
  have hfirstlo : (n : ℝ) ≤ Z.z (firstGeIndex Z (n : ℝ)) :=
    (firstGeIndex_spec Z (n : ℝ)).1
  have hfirsthi : Z.z (firstGeIndex Z (n : ℝ)) ≤ (n : ℝ) + D :=
    firstGeIndex_value_le_of_mem Z (n : ℝ) D m ⟨hmlo, hmhi⟩
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by rw [hsample]
  rw [hsamp]
  have hdyadic : dyadic n = (2 : ℝ) ^ (-(n : ℝ)) := by
    unfold dyadic
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
    simp
  have hideal' := hideal
  rw [hdyadic] at hideal'
  apply powerPoint_mem_thickening_of_z_bounds hK
    (by linarith [hfill.2.2.1]) hfirstlo hfirsthi (by positivity) hideal'
  simpa only [neg_mul] using hwidth n hn x p hp hideal

theorem sequence_missedCenters_subset_power_missedCenters_of_active_point
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (r : ℝ)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests →
      ∀ (p : PowerParams (1 / (K : ℝ)) K),
        p ∈ windowActivations n k windows → ∀ (x : ℝ),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening r G) :
    sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
    powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      tests k windows G := by
  classical
  intro x hx
  simp only [sequenceMissedCenters, powerMissedCenters] at hx ⊢
  rw [mem_missedCenters_iff] at hx ⊢
  by_contra hnot
  push_neg at hnot
  obtain ⟨p, hxmiss⟩ := hx
  obtain ⟨i, hi, hhit⟩ := hnot p
  have hseq := hactivate i.1 i.2 p hi
  have hpoint' := hpoint i.1 i.2 p hi x hhit
  let j : {m // m ∈ tests.image sample} :=
    ⟨sample i.1, Finset.mem_image.2 ⟨i.1, i.2, rfl⟩⟩
  exact hxmiss j hseq hpoint'

/-- Point transfer for the same first-ge sample map.  The ideal dyadic point
is rewritten exactly as `2 ^ (-(n : ℝ))`, so no approximation premise is
hidden in this bridge. -/
theorem filled_firstGe_sequence_point_transfer
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    {G : Set ℝ} (ρ : ℝ)
    (hwidth : ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      |p.2.1 * ((2 : ℝ) ^ k)| *
          ((2 : ℝ) ^ (-((n : ℝ) * p.1.1)) -
            (2 : ℝ) ^ (-(((n : ℝ) + D) * p.1.1))) < ρ) :
    ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G := by
  intro n hn x p hideal
  have hbounds := filled_firstGe_sample_bounds hfill hR tests hlo hhi n hn
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by rw [hsample]
  rw [hsamp]
  have hdyadic : dyadic n = (2 : ℝ) ^ (-(n : ℝ)) := by
    unfold dyadic
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
    simp
  have hideal' := hideal
  rw [hdyadic] at hideal'
  apply powerPoint_mem_thickening_of_z_bounds hK
    (by linarith [hfill.2.2.1]) hbounds.1 hbounds.2 (by positivity)
    hideal'
  simpa only [neg_mul] using hwidth n hn x p hideal

/-- A lower bound on all prior logarithms forces first-ge samples into the
requested input tail.  This is the explicit index-tail guard needed when the
logarithmic test coordinate is not itself a sequence index. -/
theorem firstGe_image_tail_of_prefix_bound
    {Z : LogScale} (tests : Finset ℕ) (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (N : ℕ)
    (hprefix : ∀ n : ℕ, n ∈ tests →
      ∀ m : ℕ, m < N → Z.z m < (n : ℝ)) :
    ∀ n : ℕ, n ∈ tests.image sample → N ≤ n := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn
  have hsamp : sample m = firstGeIndex Z (m : ℝ) := by rw [hsample]
  rw [hsamp]
  by_contra hN
  have hlt : firstGeIndex Z (m : ℝ) < N := Nat.lt_of_not_ge hN
  exact (not_lt_of_ge (firstGeIndex_spec Z (m : ℝ)).1)
    (hprefix m hm (firstGeIndex Z (m : ℝ)) hlt)

/-! The finite prefix condition in the preceding result is constructive.  The
following elementary bound is useful when the routing tail starts at a later
integer than the requested input tail. -/

theorem exists_integer_bound_on_prefix
    (Z : LogScale) (N : ℕ) :
    ∃ B : ℕ, ∀ m : ℕ, m < N → Z.z m < (B : ℝ) := by
  induction N with
  | zero =>
      exact ⟨0, by simp⟩
  | succ N ih =>
      obtain ⟨B, hB⟩ := ih
      obtain ⟨C, hC⟩ := exists_nat_gt (Z.z N)
      refine ⟨max B C, ?_⟩
      intro m hm
      by_cases hmN : m < N
      · exact lt_of_lt_of_le (hB m hmN)
          (by exact_mod_cast (Nat.le_max_left B C))
      · have hEq : m = N := by omega
        subst m
        exact lt_of_lt_of_le hC
          (by exact_mod_cast (Nat.le_max_right B C))

/-! Every member of the finite candidate list is bounded by the stride times
the label budget.  This is the numerical upper endpoint used to place all
tests inside a selected annulus. -/

theorem candidateOriginalIndices_le_stride_budget
    (m N : ℕ) (U T : ℝ) (k : ℤ)
    {j : ℕ} (hj : j ∈ candidateOriginalIndices m N U T k) :
    j ≤ m * candidateLabelBudget U T k := by
  obtain ⟨a, ha, _hN, rfl⟩ :=
    (mem_candidateOriginalIndices_iff _ _ _ _ _ _).1 hj
  exact Nat.mul_le_mul_left m (Nat.le_of_lt ha)

theorem globalRoutingTests_bounds_of_budget
    {Z : LogScale} {M d K N : ℕ} {k : ℤ}
    (c : RoutingTemplate M d) {U R D : ℝ}
    (hOrigin : (c.origin : ℝ) = U)
    (hR : 2 ≤ R)
    (hLower : U / R ≤ (N : ℝ))
    (hUpper :
      ((candidateStride (1 / (K : ℝ)) : ℕ) *
        candidateLabelBudget (c.origin : ℝ)
          (RoutingTemplate.span M c.gap c.baseLength d) k : ℝ) + D ≤
        R * (c.origin : ℝ)) :
    ∀ n : ℕ, n ∈ globalRoutingTests c K N k →
      U / R ≤ (n : ℝ) ∧ (n : ℝ) + D ≤ R * U := by
  intro n hn
  have htail := globalRoutingTests_tail c K N k n hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast htail
  have hlo : U / R ≤ (n : ℝ) := hLower.trans hnN
  have hnb := candidateOriginalIndices_le_stride_budget
    (candidateStride (1 / (K : ℝ))) N (c.origin : ℝ)
      (RoutingTemplate.span M c.gap c.baseLength d) k hn
  have hnb' : (n : ℝ) ≤
      ((candidateStride (1 / (K : ℝ)) : ℕ) *
        candidateLabelBudget (c.origin : ℝ)
          (RoutingTemplate.span M c.gap c.baseLength d) k : ℕ) := by
    exact_mod_cast hnb
  have hnb'' : (n : ℝ) ≤
      ((candidateStride (1 / (K : ℝ)) : ℕ) *
        candidateLabelBudget (c.origin : ℝ)
          (RoutingTemplate.span M c.gap c.baseLength d) k : ℝ) := by
    exact_mod_cast hnb'
  have hhi0 : (n : ℝ) + D ≤ R * (c.origin : ℝ) := by
    have hh := add_le_add_left hnb'' D
    exact hh.trans hUpper
  exact ⟨hlo, by simpa [hOrigin] using hhi0⟩

/-! Active routing windows themselves force the tested integer into the late
annulus.  This is the useful eventual form: early, inactive members of the
finite candidate list need no annular sample.  The two numerical guards are
transparent (`R ≥ 2K`, `|k| ≤ origin/2`, and the displayed upper budget). -/

theorem globalRoutingWindow_active_bounds
    {M d K : ℕ} {k : ℤ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) (hspan :
      (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ c.origin)
    {R D : ℝ} (hR : 2 * (K : ℝ) ≤ R)
    (hK : 0 < (K : ℝ)) (hO : 0 < (c.origin : ℝ))
    (hk : |(k : ℝ)| ≤ (c.origin : ℝ) / 2)
    (hUpper : 3 * (K : ℝ) * (c.origin : ℝ) + D ≤
      R * (c.origin : ℝ))
    (n : ℕ) (e : Fin (Fintype.card (RoutingEdge M d)))
    (p : PowerParams (1 / (K : ℝ)) K)
    (hp : p ∈ powerActivation n k
      (globalRoutingWindows c e).1 (globalRoutingWindows c e).2) :
    (c.origin : ℝ) / R ≤ (n : ℝ) ∧
      (n : ℝ) + D ≤ R * (c.origin : ℝ) := by
  let q : RoutingEdge M d := globalRoutingEdgeEnumeration M d e
  have hqstart : c.origin ≤ c.edgeStart q :=
    RoutingTemplate.edgeStart_ge_origin c q
  have hqend := RoutingTemplate.edgeEnd_within_total c hM hL q
  have hqspan : c.edgeEnd q + 1 ≤
      c.origin + RoutingTemplate.span M c.gap c.baseLength d := hqend.2
  have hqwindow : c.edgeStart q + c.edgeLength q ≤
      c.origin + RoutingTemplate.span M c.gap c.baseLength d := by
    unfold RoutingTemplate.edgeEnd at hqspan
    omega
  have hstart : (c.origin : ℝ) ≤ (c.edgeStart q : ℝ) := by
    exact_mod_cast hqstart
  have hwindow : (c.edgeStart q : ℝ) + (c.edgeLength q : ℝ) ≤
      2 * (c.origin : ℝ) := by
    have hqwindow' : (c.edgeStart q : ℝ) + (c.edgeLength q : ℝ) ≤
        (c.origin : ℝ) +
          (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
      exact_mod_cast hqwindow
    linarith
  have hslo : (1 / (K : ℝ)) ≤ p.1.1 := p.1.2.1
  have hsup : p.1.1 ≤ (K : ℝ) := p.1.2.2
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hp' :
      (c.edgeStart q : ℝ) < p.1.1 * (n : ℝ) - (k : ℝ) ∧
      p.1.1 * (n : ℝ) - (k : ℝ) <
        (c.edgeStart q : ℝ) + (c.edgeLength q : ℝ) := by
    simpa [globalRoutingWindows, q, powerActivation] using hp
  have hklo : -((c.origin : ℝ) / 2) ≤ (k : ℝ) :=
    neg_le_of_abs_le hk
  have hkhi : (k : ℝ) ≤ (c.origin : ℝ) / 2 :=
    le_of_abs_le hk
  have hsupper : p.1.1 * (n : ℝ) ≤ (K : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hsup hn0
  have hslow : (1 / (K : ℝ)) * (n : ℝ) ≤ p.1.1 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hslo hn0
  have hhalf : (c.origin : ℝ) / 2 < (K : ℝ) * (n : ℝ) := by
    linarith [hstart, hp'.1, hsupper, hklo]
  have hnlow : (c.origin : ℝ) / (2 * (K : ℝ)) < (n : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * (K : ℝ))).2
    nlinarith
  have hdiv : (c.origin : ℝ) / R ≤
      (c.origin : ℝ) / (2 * (K : ℝ)) := by
    apply div_le_div_of_nonneg_left hO.le
    · positivity
    · exact hR
  have hnlow' : (c.origin : ℝ) / R ≤ (n : ℝ) :=
    hdiv.trans hnlow.le
  have hsupper' : (1 / (K : ℝ)) * (n : ℝ) <
      2 * (c.origin : ℝ) + (c.origin : ℝ) / 2 := by
    linarith [hp'.2, hwindow, hkhi]
  have hnupper : (n : ℝ) < 3 * (K : ℝ) * (c.origin : ℝ) := by
    have hcancel : (K : ℝ) * ((1 / (K : ℝ)) * (n : ℝ)) = (n : ℝ) := by
      field_simp
    nlinarith [hslow, hsupper', hcancel]
  have hnupper' : (n : ℝ) + D ≤ R * (c.origin : ℝ) := by
    have hnle : (n : ℝ) ≤ 3 * (K : ℝ) * (c.origin : ℝ) := hnupper.le
    exact (add_le_add_left hnle D).trans hUpper
  exact ⟨hnlow', hnupper'⟩

theorem globalRoutingTests_firstGe_activation
    {Z : LogScale} {M d K N : ℕ} {k : ℤ}
    (hKnat : 2 ≤ K) (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ c.origin)
    {R D : ℝ} (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hRann : 2 ≤ R) (hR : 2 * (K : ℝ) ≤ R)
    (hO : 0 < (c.origin : ℝ))
    (hk : |(k : ℝ)| ≤ (c.origin : ℝ) / 2)
    (hUpper : 3 * (K : ℝ) * (c.origin : ℝ) + D ≤
      R * (c.origin : ℝ))
    (windows : Fin (Fintype.card (RoutingEdge M d)) → ℝ × ℝ)
    (hsame : windows = globalRoutingWindows c)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hmargin : ∀ n : ℕ, n ∈ globalRoutingTests c K N k →
      ∀ e : Fin (Fintype.card (RoutingEdge M d)),
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ))) :
    ∀ n : ℕ, n ∈ globalRoutingTests c K N k →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      p ∈ sequenceWindowActivations Z (sample n) k windows := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hactiveBounds : ∀ n : ℕ, n ∈ globalRoutingTests c K N k →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k (globalRoutingWindows c) →
      (c.origin : ℝ) / R ≤ (n : ℝ) ∧
        (n : ℝ) + D ≤ R * (c.origin : ℝ) := by
    intro n hn p hp
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hp
    have he' : p ∈ powerActivation n k
        (globalRoutingWindows c e).1 (globalRoutingWindows c e).2 := by
      simpa [hsame] using he
    exact globalRoutingWindow_active_bounds c hM hL hspan hR hKr hO hk hUpper n e p he'
  have hmarg' : ∀ n : ℕ, n ∈ globalRoutingTests c K N k →
      ∀ e : Fin (Fintype.card (RoutingEdge M d)),
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (globalRoutingWindows c e).1
        (globalRoutingWindows c e).2 →
      p.1.1 * D < (globalRoutingWindows c e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ)) := by
    simpa [hsame] using hmargin
  have hres := filled_firstGe_sequence_activation_of_active_bounds hKnat hfill hRann
    (globalRoutingTests c K N k) (globalRoutingWindows c) sample hsample
    (by
      intro n hn p hp
      exact hactiveBounds n hn p hp)
    (by
      intro n hn e p he
      exact hmarg' n hn e p he)
  simpa [hsame] using hres

/-! The late-window hypothesis supplies the remaining numerical guards after a
single harmless choice of annular ratio.  The proof only uses the eventual
origin, the ratio `D / log log U → 0`, and the schedule's eventual placement;
no unproved relation between a sequence index and its logarithm is used. -/

theorem WindowFilling.exists_scheduled_annulus_with_active_guards
    {Z : LogScale} (hW : WindowFilling Z)
    (K : ℕ) (hK : 2 ≤ K) (k : ℤ) (N : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ U : ℕ → ℕ, ∃ D : ℕ → ℝ, ∃ j : ℕ, ∃ s : RoutingSchedule K k N p,
      s.template.origin = U j ∧
      1 < Real.log (U j : ℝ) ∧
      FillsAnnulus Z (U j) (4 * K) (D j) ∧
      D j / Real.log (Real.log (U j : ℝ)) < (K : ℝ) ∧
      |(k : ℝ)| ≤ (U j : ℝ) / 2 ∧
      3 * (K : ℝ) * (U j : ℝ) + D j ≤
        (4 * K : ℕ) * (U j : ℝ) := by
  let R₀ : ℕ := 4 * K
  have hR₀ : 2 ≤ R₀ := by
    dsimp [R₀]
    omega
  have hη : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  obtain ⟨Ufun, Dfun, hUtend, hUlog, hUfill, hUratio⟩ :=
    hW R₀ hR₀
  have hSched := routing_schedule_eventually_at_origin K hK k N p hp
  obtain ⟨Uₛ, hUₛ⟩ := eventually_atTop.1 hSched
  let Umin : ℝ := max (2 : ℝ) (2 * |(k : ℝ)| + 1)
  have hUmin : 0 < Umin := by
    dsimp [Umin]
    positivity
  have hlate : ∀ᶠ j : ℕ in atTop, Uₛ ≤ Ufun j := by
    have hreal : ∀ᶠ j : ℕ in atTop, (Uₛ : ℝ) ≤ (Ufun j : ℝ) :=
      hUtend.eventually (eventually_ge_atTop (Uₛ : ℝ))
    filter_upwards [hreal] with j hj
    exact_mod_cast hj
  have hlarge : ∀ᶠ j : ℕ in atTop, Umin ≤ (Ufun j : ℝ) := by
    exact hUtend.eventually (eventually_ge_atTop Umin)
  have hsched : ∀ᶠ j : ℕ in atTop, ∃ s : RoutingSchedule K k N p,
      s.template.origin = Ufun j := by
    filter_upwards [hlate] with j hj
    obtain ⟨s, hs⟩ := hUₛ (Ufun j) hj
    exact ⟨s, hs⟩
  have hratio : ∀ᶠ j : ℕ in atTop,
      Dfun j / Real.log (Real.log (Ufun j : ℝ)) < (K : ℝ) :=
    hUratio.eventually (Iio_mem_nhds hη)
  obtain ⟨j, hjS, hjratio, hjlarge⟩ :=
    (hsched.and (hratio.and hlarge)).exists
  obtain ⟨s, hs⟩ := hjS
  have hlog : 1 < Real.log (Ufun j : ℝ) := hUlog j
  have hllpos : 0 < Real.log (Real.log (Ufun j : ℝ)) :=
    Real.log_pos hlog
  have hUpos : 0 < (Ufun j : ℝ) := by
    have : (2 : ℝ) ≤ (Ufun j : ℝ) :=
      (show (2 : ℝ) ≤ Umin by exact le_max_left _ _).trans hjlarge
    linarith
  have hll_le : Real.log (Real.log (Ufun j : ℝ)) ≤ (Ufun j : ℝ) := by
    have hlogUpos : 0 < Real.log (Ufun j : ℝ) := by linarith [hlog]
    have h₁ := Real.log_le_sub_one_of_pos hlogUpos
    have h₂ := Real.log_le_sub_one_of_pos hUpos
    linarith
  have hD : Dfun j ≤ (K : ℝ) * (Ufun j : ℝ) := by
    have hratio' := (div_lt_iff₀ hllpos).1 hjratio
    nlinarith [mul_le_mul_of_nonneg_left hll_le hη.le]
  have hUpper : 3 * (K : ℝ) * (Ufun j : ℝ) + Dfun j ≤
      (4 * K : ℕ) * (Ufun j : ℝ) := by
    have hKcast : ((4 * K : ℕ) : ℝ) = 4 * (K : ℝ) := by norm_num
    rw [hKcast]
    nlinarith
  have hkbound : |(k : ℝ)| ≤ (Ufun j : ℝ) / 2 := by
    have hsmall : 2 * |(k : ℝ)| + 1 ≤ (Ufun j : ℝ) :=
      (le_max_right _ _).trans hjlarge
    nlinarith
  exact ⟨Ufun, Dfun, j, s, hs, hlog, (by simpa [R₀] using hUfill j),
    hjratio, hkbound, hUpper⟩

/-! Combining the schedule's tail enumeration with a finite logarithmic prefix
bound gives the exact image-tail premise required by the transfer layer.  The
tail used by the schedule may be chosen independently of the requested input
tail; this avoids any hidden assumption that `z m < m`. -/

theorem globalRoutingTests_firstGe_image_tail
    {Z : LogScale} {M d K Nₛ : ℕ} {k : ℤ}
    (c : RoutingTemplate M d) (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (N₀ B : ℕ)
    (hprefix : ∀ m : ℕ, m < N₀ → Z.z m < (B : ℝ))
    (hB : B ≤ Nₛ) :
    ∀ n : ℕ, n ∈ (globalRoutingTests c K Nₛ k).image sample → N₀ ≤ n := by
  apply firstGe_image_tail_of_prefix_bound
    (globalRoutingTests c K Nₛ k) sample hsample N₀
  intro q hq m hm
  have htail := globalRoutingTests_tail c K Nₛ k q hq
  have hBN : (B : ℝ) ≤ (Nₛ : ℝ) := by exact_mod_cast hB
  have hNq : (Nₛ : ℝ) ≤ (q : ℝ) := by exact_mod_cast htail
  exact lt_of_lt_of_le (hprefix m hm) (hBN.trans hNq)

/-! A single conjunction with exactly the three transfer fields consumed by
`UniformPowerTransferSpec`.  The density/error fields remain independent
finite-routing obligations. -/
theorem filled_firstGe_transfer_subfields
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    (hmargin : ∀ n : ℕ, n ∈ tests → ∀ e : Fin W,
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ)))
    {G : Set ℝ} (ρ : ℝ)
    (hwidth : ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      |p.2.1 * ((2 : ℝ) ^ k)| *
          ((2 : ℝ) ^ (-((n : ℝ) * p.1.1)) -
            (2 : ℝ) ^ (-(((n : ℝ) + D) * p.1.1))) < ρ)
    (N : ℕ)
    (hprefix : ∀ n : ℕ, n ∈ tests →
      ∀ m : ℕ, m < N → Z.z m < (n : ℝ)) :
    (∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows) ∧
    (∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G) ∧
    (∀ n : ℕ, n ∈ tests.image sample → N ≤ n) := by
  have hA := filled_firstGe_sequence_activation hK hfill hR tests windows sample
      hsample hlo hhi hmargin
  have hB := filled_firstGe_sequence_point_transfer hK hfill hR tests windows sample
      hsample hlo hhi ρ hwidth
  have hC := firstGe_image_tail_of_prefix_bound tests sample hsample N hprefix
  exact And.intro hA (And.intro hB hC)

end ErdosSimilarityGrowingGaps
