import ContinuumGeometric.RoutingGeometry
import ContinuumGeometric.CandidateBounds

/-!
Actual dyadic power points in the strict integer output windows of the routing
template. The estimates retain original indices and exact periodic grid keys.
-/
namespace ContinuumGeometric

/-- The strict upper activation endpoint gives a strict lower offset bound. -/
theorem active_power_offset_lower (s₀ s₁ x u v : ℝ) (j : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hp : p ∈ powerActivation j k u v) :
    (2 : ℝ) ^ (-v) < powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) - x := by
  have hpow : (2 : ℝ) ^ (-v) < (2 : ℝ) ^ ((k : ℝ) - p.1.1 * j) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hp.2])
  have hmul : (2 : ℝ) ^ ((k : ℝ) - p.1.1 * j) ≤
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * j) := by
    nlinarith [p.2.2.1, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
      ((k : ℝ) - p.1.1 * j)]
  simpa only [powerPoint, dyadic_shifted_offset, add_sub_cancel_left] using hpow.trans_le hmul

/-- A window ending at `u+ell-1` has four cells across its lower offset scale. -/
theorem active_window_grid_scale (u ell : ℕ) (hell : 0 < ell) :
    ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) * (2 : ℝ) ^ (-((u : ℝ) + ell)) = 4 := by
  have he : ((u + ell - 1 + 3 : ℕ) : ℝ) = (u : ℝ) + ell + 2 := by
    have hn : u + ell - 1 + 3 = u + ell + 2 := by omega
    rw [hn]
    push_cast
    ring
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_add (by norm_num), he]
  have he' : (u : ℝ) + ell + 2 + -((u : ℝ) + ell) = 2 := by ring
  rw [he']
  norm_num

/-- Every active point at a start at least four stays within one eighth of its center. -/
theorem active_power_point_short (s₀ s₁ x : ℝ) (u ell j : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell)) :
    x < powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) ∧
      powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) - x < 1 / 8 := by
  have hr := active_power_point_range s₀ s₁ x u ((u : ℝ) + ell) j k p hp
  have hur : (4 : ℝ) ≤ u := by exact_mod_cast hu
  have he : (2 : ℝ) ^ (1 - (u : ℝ)) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  norm_num at he
  exact ⟨hr.1, by linarith [hr.2]⟩

/-- The local estimate needed to exclude equality of exact periodic addresses. -/
theorem gridAddress_ne_of_scaled_small_gap (b : ℕ) (z z' : ℝ)
    (hl : 1 ≤ ((2 ^ (b + 3) : ℕ) : ℝ) * (z' - z))
    (hu : z' - z ≤ 1 / 8) : gridAddress b z ≠ gridAddress b z' := by
  have hN : (8 : ℝ) ≤ ((2 ^ (b + 3) : ℕ) : ℝ) := by
    have hn : 2 ^ 3 ≤ (2 : ℕ) ^ (b + 3) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast hn
  have hNp : (0 : ℝ) ≤ ((2 ^ (b + 3) : ℕ) : ℝ) := by positivity
  have hupper : ((2 ^ (b + 3) : ℕ) : ℝ) * (z' - z) ≤
      ((2 ^ (b + 3) : ℕ) : ℝ) - 1 := by
    have hm := mul_le_mul_of_nonneg_left hu hNp
    nlinarith
  intro heq
  exact periodicGridKey_ne_of_scaled_gap (2 ^ (b + 3)) (by positivity) z z' hl hupper
    ((gridAddress_eq_iff b z z').1 heq)

/-- Own-grid addresses of an actual active original dyadic point avoid the center. -/
theorem active_power_gridAddress_ne_center (s₀ s₁ x : ℝ) (u ell j : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0 < ell) (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell)) :
    gridAddress (u + ell - 1) (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) ≠
      gridAddress (u + ell - 1) x := by
  have hlo := active_power_offset_lower s₀ s₁ x u ((u : ℝ) + ell) j k p hp
  have hs := active_power_point_short s₀ s₁ x u ell j k hu p hp
  have hN : (0 : ℝ) < ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hlo hN
  rw [active_window_grid_scale u ell hell] at hscaled
  exact (gridAddress_ne_of_scaled_small_gap (u + ell - 1) x
    (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) (by linarith) hs.2.le).symm

/-- Three output-log units force a factor of eight between actual offsets. -/
theorem power_point_offset_ratio_of_output_gap (s₀ s₁ x : ℝ) (j j' : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hgap : 3 ≤ p.1.1 * j' - p.1.1 * j) :
    8 * (powerPoint (dyadic j') ((2 : ℝ) ^ k) (x, p) - x) ≤
      powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) - x := by
  have hr : (2 : ℝ) ^ (((k : ℝ) - p.1.1 * j') + 3) ≤
      (2 : ℝ) ^ ((k : ℝ) - p.1.1 * j) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_add (by norm_num)] at hr
  norm_num at hr
  have ht : (0 : ℝ) ≤ p.2.1 := by linarith [p.2.2.1]
  have hm := mul_le_mul_of_nonneg_left hr ht
  simp only [powerPoint, dyadic_shifted_offset, add_sub_cancel_left]
  nlinarith [hm]

/-- Actual offset separation, retaining strict activation at the upper endpoint. -/
theorem active_power_point_gap_lower (s₀ s₁ x u v : ℝ) (j j' : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hgap : 3 ≤ p.1.1 * j' - p.1.1 * j)
    (hp' : p ∈ powerActivation j' k u v) :
    7 * (2 : ℝ) ^ (-v) <
      powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) -
        powerPoint (dyadic j') ((2 : ℝ) ^ k) (x, p) := by
  have hr := power_point_offset_ratio_of_output_gap s₀ s₁ x j j' k p hgap
  have hl := active_power_offset_lower s₀ s₁ x u v j' k p hp'
  linarith

/-- Separated output logarithms have distinct actual own-grid keys. -/
theorem active_power_gridAddress_ne_of_output_gap (s₀ s₁ x : ℝ)
    (u ell j j' : ℕ) (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell)
    (p : PowerParams s₀ s₁) (hgap : 3 ≤ p.1.1 * j' - p.1.1 * j)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell))
    (hp' : p ∈ powerActivation j' k u ((u : ℝ) + ell)) :
    gridAddress (u + ell - 1) (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) ≠
      gridAddress (u + ell - 1) (powerPoint (dyadic j') ((2 : ℝ) ^ k) (x, p)) := by
  have hl := active_power_point_gap_lower s₀ s₁ x u ((u : ℝ) + ell) j j' k p hgap hp'
  have hs := active_power_point_short s₀ s₁ x u ell j k hu p hp
  have hs' := active_power_point_short s₀ s₁ x u ell j' k hu p hp'
  have hN : (0 : ℝ) < ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) := by positivity
  have hm := mul_lt_mul_of_pos_left hl hN
  have he : ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) *
      (7 * (2 : ℝ) ^ (-((u : ℝ) + ell))) = 28 := by
    calc
      _ = 7 * (((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((u : ℝ) + ell))) := by ring
      _ = 28 := by rw [active_window_grid_scale u ell hell]; norm_num
  rw [he] at hm
  exact (gridAddress_ne_of_scaled_small_gap (u + ell - 1)
    (powerPoint (dyadic j') ((2 : ℝ) ^ k) (x, p))
    (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) (by linarith) (by linarith)).symm

/-- The actual original indices `m*n` inherit the output-log spacing. -/
theorem subsequence_output_log_gap (s₀ s₁ : ℝ) (m n n' : ℕ)
    (hgap : 3 ≤ (m : ℝ) * s₀) (hn : n < n') (p : PowerParams s₀ s₁) :
    3 ≤ p.1.1 * (m * n' : ℕ) - p.1.1 * (m * n : ℕ) := by
  have hs : 3 ≤ (m : ℝ) * p.1.1 :=
    hgap.trans (mul_le_mul_of_nonneg_left p.1.2.1 (Nat.cast_nonneg m))
  have hn' : (1 : ℝ) ≤ (n' : ℝ) - n := by
    have hi : n + 1 ≤ n' := hn
    have hr : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hi
    linarith
  have hmul := mul_le_mul_of_nonneg_left hn' (by linarith : 0 ≤ (m : ℝ) * p.1.1)
  push_cast
  nlinarith [hmul]

/-- Distinct active subsequence labels have pairwise distinct actual addresses. -/
theorem active_subsequence_gridAddress_ne (s₀ s₁ x : ℝ) (u ell m n n' : ℕ)
    (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell) (hgap : 3 ≤ (m : ℝ) * s₀)
    (hne : n ≠ n') (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation (m * n) k u ((u : ℝ) + ell))
    (hp' : p ∈ powerActivation (m * n') k u ((u : ℝ) + ell)) :
    gridAddress (u + ell - 1) (powerPoint (dyadic (m * n)) ((2 : ℝ) ^ k) (x, p)) ≠
      gridAddress (u + ell - 1) (powerPoint (dyadic (m * n')) ((2 : ℝ) ^ k) (x, p)) := by
  rcases lt_or_gt_of_ne hne with hn | hn
  · exact active_power_gridAddress_ne_of_output_gap s₀ s₁ x u ell (m * n) (m * n') k
      hu hell p (subsequence_output_log_gap s₀ s₁ m n n' hgap hn p) hp hp'
  · exact (active_power_gridAddress_ne_of_output_gap s₀ s₁ x u ell (m * n') (m * n) k
      hu hell p (subsequence_output_log_gap s₀ s₁ m n' n hgap hn p) hp' hp).symm

/-- Distinct own-grid addresses remain distinct on every finer grid. -/
theorem gridAddress_ne_of_coarser_ne (b b' : ℕ) (hb : b ≤ b') (z z' : ℝ)
    (hne : gridAddress b z ≠ gridAddress b z') :
    gridAddress b' z ≠ gridAddress b' z' := by
  intro heq
  exact hne (dyadic_grid_eq_of_finer_eq b b' hb z z' heq)

theorem active_power_finer_gridAddress_ne_center (s₀ s₁ x : ℝ)
    (u ell j b : ℕ) (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell)
    (hb : u + ell - 1 ≤ b) (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell)) :
    gridAddress b (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) ≠ gridAddress b x :=
  gridAddress_ne_of_coarser_ne _ _ hb _ _
    (active_power_gridAddress_ne_center s₀ s₁ x u ell j k hu hell p hp)

theorem active_subsequence_finer_gridAddress_ne (s₀ s₁ x : ℝ)
    (u ell m n n' b : ℕ) (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell)
    (hgap : 3 ≤ (m : ℝ) * s₀) (hne : n ≠ n') (hb : u + ell - 1 ≤ b)
    (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation (m * n) k u ((u : ℝ) + ell))
    (hp' : p ∈ powerActivation (m * n') k u ((u : ℝ) + ell)) :
    gridAddress b (powerPoint (dyadic (m * n)) ((2 : ℝ) ^ k) (x, p)) ≠
      gridAddress b (powerPoint (dyadic (m * n')) ((2 : ℝ) ^ k) (x, p)) :=
  gridAddress_ne_of_coarser_ne _ _ hb _ _
    (active_subsequence_gridAddress_ne s₀ s₁ x u ell m n n' k hu hell hgap hne p hp hp')

/-- An original-index API: distinct multiples of the stride need no relabeling
in the downstream finite candidate enumeration. -/
theorem active_original_finer_gridAddress_ne (s₀ s₁ x : ℝ)
    (u ell m j j' b : ℕ) (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell)
    (hgap : 3 ≤ (m : ℝ) * s₀) (hne : j ≠ j') (hb : u + ell - 1 ≤ b)
    (hj : ∃ n : ℕ, m * n = j) (hj' : ∃ n' : ℕ, m * n' = j')
    (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell))
    (hp' : p ∈ powerActivation j' k u ((u : ℝ) + ell)) :
    gridAddress b (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) ≠
      gridAddress b (powerPoint (dyadic j') ((2 : ℝ) ^ k) (x, p)) := by
  obtain ⟨n, rfl⟩ := hj
  obtain ⟨n', rfl⟩ := hj'
  have hn : n ≠ n' := fun h => hne (congrArg (fun r => m * r) h)
  exact active_subsequence_finer_gridAddress_ne s₀ s₁ x u ell m n n' b k hu hell
    hgap hn hb p hp hp'

/-- Direct injectivity on any list of distinct active original stride indices. -/
theorem active_original_gridAddress_injective {ι : Type*} (s₀ s₁ x : ℝ)
    (u ell m b : ℕ) (k : ℤ) (hu : 4 ≤ u) (hell : 0 < ell)
    (hgap : 3 ≤ (m : ℝ) * s₀) (hb : u + ell - 1 ≤ b)
    (indices : ι → ℕ) (hinj : Function.Injective indices)
    (hmul : ∀ i, ∃ n : ℕ, m * n = indices i) (p : PowerParams s₀ s₁)
    (hactive : ∀ i, p ∈ powerActivation (indices i) k u ((u : ℝ) + ell)) :
    Function.Injective (fun i => gridAddress b
      (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) := by
  intro i i' heq
  apply hinj
  by_contra hne
  exact active_original_finer_gridAddress_ne s₀ s₁ x u ell m (indices i) (indices i') b k
    hu hell hgap hne hb (hmul i) (hmul i') p (hactive i) (hactive i') heq

/-- A stable predecessor interval preserves the exact preceding key for every
actual active power point. -/
theorem active_power_preceding_gridAddress_eq (s₀ s₁ x : ℝ)
    (u ell j b₀ g : ℕ) (k : ℤ) (hu : u = b₀ + g + 1)
    (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell))
    (hstable : NoGridBoundary (2 ^ (b₀ + 3)) x (2 ^ (-((b₀ : ℝ) + g)))) :
    gridAddress b₀ (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) = gridAddress b₀ x := by
  apply (gridAddress_eq_iff _ _ _).2
  apply periodicGridKey_eq_of_no_boundary _ (by positivity) x
    (2 ^ (-((b₀ : ℝ) + g))) _ ?_ hstable
  have hr := active_power_point_range s₀ s₁ x u ((u : ℝ) + ell) j k p hp
  have he : (1 : ℝ) - u = -((b₀ : ℝ) + g) := by
    rw [hu]
    push_cast
    ring
  rw [he] at hr
  exact ⟨hr.1.le, hr.2.le⟩

/-- Nesting carries stable preceding keys to every coarser endpoint. -/
theorem active_power_coarser_preceding_gridAddress_eq (s₀ s₁ x : ℝ)
    (u ell j b b₀ g : ℕ) (k : ℤ) (hu : u = b₀ + g + 1) (hb : b ≤ b₀)
    (p : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation j k u ((u : ℝ) + ell))
    (hstable : NoGridBoundary (2 ^ (b₀ + 3)) x (2 ^ (-((b₀ : ℝ) + g)))) :
    gridAddress b (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) = gridAddress b x :=
  dyadic_grid_eq_of_finer_eq b b₀ hb _ _
    (active_power_preceding_gridAddress_eq s₀ s₁ x u ell j b₀ g k hu p hp hstable)

end ContinuumGeometric
