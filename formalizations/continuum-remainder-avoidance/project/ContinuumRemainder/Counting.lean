import ContinuumRemainder.Sampling
import ContinuumGeometric.CandidateBounds
import ContinuumRemainder.LogGeometry

set_option autoImplicit false

namespace ContinuumRemainder

open Set Filter Topology ContinuumGeometric

/-- Telescoping estimates use every consecutive gap, without an arithmetic
progression assumption on the prescribed configuration. -/
theorem sequence_span_bounds (w : ℕ → ℝ) (q D : ℝ)
    (hlo : ∀ n, q ≤ w (n + 1) - w n)
    (hup : ∀ n, w (n + 1) - w n ≤ D) (i n : ℕ) :
    q * n ≤ w (i + n) - w i ∧ w (i + n) - w i ≤ D * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl := hlo (i + n)
    have hu := hup (i + n)
    push_cast
    simp only [Nat.add_succ]
    constructor <;> nlinarith [ih.1, ih.2]

/-- Counts for BOTH-STRICT output windows of a nonarithmetic sequence.
Equality at either endpoint is retained as inactive. -/
theorem open_window_count_bounds (w : ℕ → ℝ) (hw : Tendsto w atTop atTop)
    (hmono : Monotone w) (D : ℝ) (hD : 0 < D)
    (hlo : ∀ n, 3 ≤ w (n + 1) - w n)
    (hup : ∀ n, w (n + 1) - w n ≤ D)
    (u ell : ℝ) (hstart : w 0 ≤ u) (hell : 0 < ell)
    (S : Finset ℕ) (hS : ∀ n, n ∈ S ↔ u < w n ∧ w n < u + ell) :
    ell / D - 1 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 1 + ell / 3 := by
  classical
  have haex : ∃ n, u < w n := by
    obtain ⟨n, hn⟩ := (hw.eventually_ge_atTop (u + 1)).exists
    exact ⟨n, by linarith⟩
  have hbex : ∃ n, u + ell ≤ w n :=
    (hw.eventually_ge_atTop (u + ell)).exists
  let a := Nat.find haex
  let b := Nat.find hbex
  have ha : u < w a := Nat.find_spec haex
  have hb : u + ell ≤ w b := Nat.find_spec hbex
  have hab : a ≤ b := Nat.find_min' haex (by linarith : u < w b)
  have ha0 : 0 < a := by
    by_contra h
    have haz : a = 0 := by omega
    rw [haz] at ha
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hprev : w (a - 1) ≤ u := by
    have hm := Nat.find_min haex (by dsimp [a]; omega : a - 1 < a)
    exact le_of_not_gt hm
  have hS_eq : S = Finset.Ico a b := by
    ext n
    rw [hS, Finset.mem_Ico]
    constructor
    · rintro ⟨hl, hu⟩
      refine ⟨Nat.find_min' haex hl, ?_⟩
      by_contra hnb
      have := hmono (show b ≤ n by omega)
      linarith
    · rintro ⟨hl, hu⟩
      refine ⟨ha.trans_le (hmono hl), ?_⟩
      exact lt_of_not_ge (Nat.find_min hbex hu)
  have hcard : S.card = b - a := by rw [hS_eq, Nat.card_Ico]
  have hspan := (sequence_span_bounds w 3 D hlo hup (a - 1) (b - (a - 1))).2
  have heq : a - 1 + (b - (a - 1)) = b := by omega
  rw [heq] at hspan
  have hdiff : (b - (a - 1) : ℕ) = (b - a) + 1 := by omega
  rw [hdiff, Nat.cast_add, Nat.cast_one, ← hcard] at hspan
  refine ⟨?_, ?_⟩
  · have hcover : ell ≤ D * ((S.card : ℝ) + 1) := by linarith
    have hh : ell / D ≤ (S.card : ℝ) + 1 :=
      (div_le_iff₀ hD).2 (by nlinarith [hcover])
    nlinarith
  · by_cases hab' : a < b
    · have hlast : w (b - 1) < u + ell :=
        lt_of_not_ge (Nat.find_min hbex (by dsimp [b]; omega : b - 1 < b))
      have hloSpan := (sequence_span_bounds w 3 D hlo hup a (b - 1 - a)).1
      have heq' : a + (b - 1 - a) = b - 1 := by omega
      rw [heq'] at hloSpan
      have hdiff' : ((b - 1 - a : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
        rw [hcard, Nat.cast_sub hab]
        rw [Nat.cast_sub (by omega : a ≤ b - 1), Nat.cast_sub (by omega : 1 ≤ b)]
        norm_num
        ring
      rw [hdiff'] at hloSpan
      linarith
    · have he : b = a := by omega
      rw [hcard, he]
      simp only [Nat.sub_self, Nat.cast_zero]
      positivity

namespace SampledLogConfiguration

variable {A : Set ℝ} {s₀ : ℝ} {h : ℕ}

noncomputable def output (C : SampledLogConfiguration A s₀ h) (k : ℤ)
    (s : ℝ) (n : ℕ) : ℝ := s * C.z n - k

theorem output_gap_bounds (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ s : ℝ) (hs : s ∈ Icc s₀ s₁) (n : ℕ) {k : ℤ} :
    3 < C.output k s (n + 1) - C.output k s n ∧
      C.output k s (n + 1) - C.output k s n < s₁ * C.B := by
  have hspos : 0 < s := hs₀.trans_le hs.1
  have hgap := C.gap_lower n
  have hgpos : 0 < C.z (n + 1) - C.z n :=
    (by positivity : 0 < 3 / s₀).trans hgap
  have hl := (div_lt_iff₀ hs₀).1 hgap
  have hm := mul_le_mul_of_nonneg_right hs.1 hgpos.le
  have hu := mul_lt_mul_of_pos_left (C.gap_upper n) hspos
  have hm' := mul_le_mul_of_nonneg_right hs.2 C.B_pos.le
  dsimp [output]
  constructor <;> nlinarith

theorem output_linear_lower (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s : ℝ) (hs : s₀ ≤ s) (n : ℕ) :
    3 * (n : ℝ) ≤ s * C.z n := by
  induction n with
  | zero => simpa using mul_nonneg (hs₀.trans_le hs).le (C.z_nonneg 0)
  | succ n ih =>
    have hg := (C.output_gap_bounds hs₀ s s ⟨hs, le_rfl⟩ n (k := 0)).1
    dsimp [output] at hg
    push_cast
    nlinarith

theorem output_strictMono (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s : ℝ) (hs : s₀ ≤ s) (k : ℤ) :
    StrictMono (C.output k s) := by
  intro i j hij
  dsimp [output]
  exact sub_lt_sub_right
    (mul_lt_mul_of_pos_left (C.z_strictMono hs₀ hij) (hs₀.trans_le hs)) _

theorem output_tendsto (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s : ℝ) (hs : s₀ ≤ s) (k : ℤ) :
    Tendsto (C.output k s) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  have hz := (C.z_tendsto.const_mul_atTop (hs₀.trans_le hs)).eventually_ge_atTop (R + k)
  filter_upwards [hz] with n hn
  dsimp [output]
  linarith

theorem active_label_lt_budget (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s : ℝ) (hs : s₀ ≤ s)
    (U T v : ℝ) (k : ℤ) (hv : v ≤ U + T) (n : ℕ)
    (hn : C.output k s n < v) : n < candidateLabelBudget U T k := by
  have hl := C.output_linear_lower hs₀ s hs n
  have hk := le_abs_self (k : ℝ)
  have hb : (n : ℝ) < (U + T + |(k : ℝ)|) / 3 := by
    dsimp [output] at hn
    linarith
  exact (Nat.lt_ceil.2 hb).trans (Nat.lt_succ_self _)

/-- Canonical finite representation of every strictly active sample label. -/
noncomputable def activeLabels (C : SampledLogConfiguration A s₀ h)
    (k : ℤ) (s u ell : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (candidateLabelBudget u ell k)).filter
    (fun n => u < C.output k s n ∧ C.output k s n < u + ell)

theorem mem_activeLabels_iff (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (k : ℤ) (s u ell : ℝ) (hs : s₀ ≤ s) (n : ℕ) :
    n ∈ C.activeLabels k s u ell ↔
      u < C.output k s n ∧ C.output k s n < u + ell := by
  classical
  simp only [activeLabels, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun hn =>
    ⟨C.active_label_lt_budget hs₀ s hs u ell (u + ell) k le_rfl n hn.2, hn⟩⟩

theorem activeLabels_count_bounds (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ : ℝ) (k : ℤ) (s u ell : ℝ)
    (hs : s ∈ Icc s₀ s₁) (hstart : s₁ * C.z 0 - k ≤ u)
    (hell : 2 * (s₁ * C.B) ≤ ell) :
    ell / (2 * (s₁ * C.B)) ≤ (C.activeLabels k s u ell).card ∧
      ((C.activeLabels k s u ell).card : ℝ) ≤ 1 + ell / 3 := by
  have hs₁ : 0 < s₁ := (hs₀.trans_le hs.1).trans_le hs.2
  have hD : 0 < s₁ * C.B := mul_pos hs₁ C.B_pos
  have hstart' : C.output k s 0 ≤ u := by
    have := mul_le_mul_of_nonneg_right hs.2 (C.z_nonneg 0)
    dsimp [output]
    linarith
  obtain ⟨hl, hu⟩ := open_window_count_bounds (C.output k s)
    (C.output_tendsto hs₀ s hs.1 k) (C.output_strictMono hs₀ s hs.1 k).monotone
    (s₁ * C.B) hD
    (fun n => (C.output_gap_bounds hs₀ s₁ s hs n (k := k)).1.le)
    (fun n => (C.output_gap_bounds hs₀ s₁ s hs n (k := k)).2.le)
    u ell hstart' (by linarith) (C.activeLabels k s u ell)
    (C.mem_activeLabels_iff hs₀ k s u ell hs.1)
  refine ⟨?_, hu⟩
  have hh : (2 : ℝ) ≤ ell / (s₁ * C.B) := (le_div_iff₀ hD).2 hell
  have he : ell / (2 * (s₁ * C.B)) = ell / (s₁ * C.B) / 2 := by ring
  rw [he]
  linarith

theorem a_eq_logInput (C : SampledLogConfiguration A s₀ h) (n : ℕ) :
    C.a n = logInput (C.z n) := C.a_eq_rpow n

theorem mem_activeLabels_iff_logActivation (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ : ℝ) (k : ℤ) (u ell : ℝ)
    (p : PowerParams s₀ s₁) (n : ℕ) :
    n ∈ C.activeLabels k p.1.1 u ell ↔
      p ∈ logActivation (C.z n) k u (u + ell) :=
  C.mem_activeLabels_iff hs₀ k p.1.1 u ell p.1.2.1 n

theorem output_gap_of_lt (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s : ℝ) (hs : s₀ ≤ s) (i j : ℕ) (hij : i < j) :
    3 ≤ s * C.z j - s * C.z i := by
  have hg := fun n => (C.output_gap_bounds hs₀ s s ⟨hs, le_rfl⟩ n (k := 0)).1.le
  have hD := fun n => (C.output_gap_bounds hs₀ s s ⟨hs, le_rfl⟩ n (k := 0)).2.le
  have hspan := (sequence_span_bounds (C.output 0 s) 3 (s * C.B) hg hD i (j - i)).1
  rw [Nat.add_sub_of_le hij.le] at hspan
  have hn : (1 : ℝ) ≤ (j - i : ℕ) := by exact_mod_cast (by omega : 1 ≤ j - i)
  dsimp [output] at hspan
  linarith

theorem active_z_bounds (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ u v : ℝ) (k : ℤ) (p : PowerParams s₀ s₁)
    (n : ℕ) (hn : p ∈ logActivation (C.z n) k u v) :
    (u + (k : ℝ)) / s₁ < C.z n ∧ C.z n < (v + (k : ℝ)) / s₀ := by
  have hs₁ : 0 < s₁ := (hs₀.trans_le p.1.2.1).trans_le p.1.2.2
  have hlow := mul_le_mul_of_nonneg_right p.1.2.2 (C.z_nonneg n)
  have hupp := mul_le_mul_of_nonneg_right p.1.2.1 (C.z_nonneg n)
  constructor
  · apply (div_lt_iff₀ hs₁).2
    linarith [hn.1]
  · apply (lt_div_iff₀ hs₀).2
    linarith [hn.2]

/-- Every sample potentially active at some full continuum parameter is kept.
The candidate count explicitly depends on the absolute position `U+T+|k|`. -/
noncomputable def potentialPairs (C : SampledLogConfiguration A s₀ h)
    (s₁ : ℝ) {W : ℕ} (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ) :
    Finset (Fin W × ℕ) := by
  classical
  exact (Finset.univ.product (Finset.range (candidateLabelBudget U T k))).filter
    (fun q => ∃ p : PowerParams s₀ s₁,
      p ∈ logActivation (C.z q.2) k (windows q.1).1 (windows q.1).2)

theorem mem_potentialPairs_iff (C : SampledLogConfiguration A s₀ h)
    (s₁ : ℝ) {W : ℕ} (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ)
    (q : Fin W × ℕ) :
    q ∈ C.potentialPairs s₁ U T k windows ↔
      q.2 < candidateLabelBudget U T k ∧ ∃ p : PowerParams s₀ s₁,
        p ∈ logActivation (C.z q.2) k (windows q.1).1 (windows q.1).2 := by
  classical
  simp [potentialPairs]

theorem potentialPairs_card_le (C : SampledLogConfiguration A s₀ h)
    (s₁ : ℝ) {W : ℕ} (U T : ℝ) (k : ℤ) (windows : Fin W → ℝ × ℝ) :
    (C.potentialPairs s₁ U T k windows).card ≤ W * candidateLabelBudget U T k := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem mem_potentialPairs_exact (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ : ℝ) {W : ℕ} (U T : ℝ) (k : ℤ)
    (windows : Fin W → ℝ × ℝ) (hv : ∀ e, (windows e).2 ≤ U + T)
    (q : Fin W × ℕ) :
    q ∈ C.potentialPairs s₁ U T k windows ↔ ∃ p : PowerParams s₀ s₁,
      p ∈ logActivation (C.z q.2) k (windows q.1).1 (windows q.1).2 := by
  rw [C.mem_potentialPairs_iff]
  constructor
  · exact And.right
  · rintro ⟨p, hp⟩
    exact ⟨C.active_label_lt_budget hs₀ p.1.1 p.1.2.1 U T (windows q.1).2 k
      (hv q.1) q.2 hp.2, p, hp⟩

noncomputable def activePairs (C : SampledLogConfiguration A s₀ h)
    {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (s : ℝ) :
    Finset (Fin W × ℕ) := by
  classical
  exact Finset.univ.biUnion fun e =>
    (C.activeLabels k s (u e) ell).image (fun j => (e, j))

theorem activePairs_card (C : SampledLogConfiguration A s₀ h)
    {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (s : ℝ) :
    (C.activePairs u ell k s).card = ∑ e : Fin W, (C.activeLabels k s (u e) ell).card := by
  classical
  unfold activePairs
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

theorem mem_activePairs_iff (C : SampledLogConfiguration A s₀ h)
    {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ) (s : ℝ) (q : Fin W × ℕ) :
    q ∈ C.activePairs u ell k s ↔ q.2 ∈ C.activeLabels k s (u q.1) ell := by
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
theorem activePairs_eq_potential_filter (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ U T : ℝ) {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hv : ∀ e, u e + ell ≤ U + T) (p : PowerParams s₀ s₁) :
    C.activePairs u ell k p.1.1 =
      (C.potentialPairs s₁ U T k (fun e => (u e, u e + ell))).filter
        (fun q => p ∈ logActivation (C.z q.2) k (u q.1) (u q.1 + ell)) := by
  classical
  ext q
  rw [C.mem_activePairs_iff, C.mem_activeLabels_iff_logActivation hs₀ s₁ k _ _ p,
    Finset.mem_filter, C.mem_potentialPairs_exact hs₀ s₁ U T k _ hv]
  exact ⟨fun hp => ⟨⟨p, hp⟩, hp⟩, And.right⟩

theorem activePairs_count_bounds (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ : ℝ) {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hell : 2 * (s₁ * C.B) ≤ ell)
    (hstart : ∀ e, s₁ * C.z 0 - k ≤ u e) (p : PowerParams s₀ s₁) :
    (W : ℝ) * (ell / (2 * (s₁ * C.B))) ≤ (C.activePairs u ell k p.1.1).card ∧
      ((C.activePairs u ell k p.1.1).card : ℝ) ≤ (W : ℝ) * (1 + ell / 3) := by
  have hc : ((C.activePairs u ell k p.1.1).card : ℝ) =
      ∑ e : Fin W, ((C.activeLabels k p.1.1 (u e) ell).card : ℝ) := by
    rw [C.activePairs_card, Nat.cast_sum]
  rw [hc]
  constructor
  · calc
      (W : ℝ) * (ell / (2 * (s₁ * C.B))) =
          ∑ _e : Fin W, ell / (2 * (s₁ * C.B)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun e _ =>
        (C.activeLabels_count_bounds hs₀ s₁ k p.1.1 (u e) ell p.1.2 (hstart e) hell).1
  · calc
      _ ≤ ∑ _e : Fin W, (1 + ell / 3) := Finset.sum_le_sum fun e _ =>
        (C.activeLabels_count_bounds hs₀ s₁ k p.1.1 (u e) ell p.1.2 (hstart e) hell).2
      _ = _ := by simp; ring

open scoped Classical in
theorem potentialPairs_active_count (C : SampledLogConfiguration A s₀ h)
    (hs₀ : 0 < s₀) (s₁ U T : ℝ) {W : ℕ} (u : Fin W → ℝ) (ell : ℝ) (k : ℤ)
    (hell : 2 * (s₁ * C.B) ≤ ell) (hv : ∀ e, u e + ell ≤ U + T)
    (hstart : ∀ e, s₁ * C.z 0 - k ≤ u e) (p : PowerParams s₀ s₁) :
    let active := (C.potentialPairs s₁ U T k (fun e => (u e, u e + ell))).filter
      (fun q => p ∈ logActivation (C.z q.2) k (u q.1) (u q.1 + ell))
    (W : ℝ) * (ell / (2 * (s₁ * C.B))) ≤ active.card ∧
      (active.card : ℝ) ≤ (W : ℝ) * (1 + ell / 3) := by
  dsimp only
  rw [← C.activePairs_eq_potential_filter hs₀ s₁ U T u ell k hv p]
  exact C.activePairs_count_bounds hs₀ s₁ u ell k hell hstart p

end SampledLogConfiguration

end ContinuumRemainder
