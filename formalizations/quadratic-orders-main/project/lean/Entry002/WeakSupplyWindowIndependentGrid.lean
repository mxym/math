import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic
import Entry002.WeakSupplyWindowLogCertificate

/-!
Independent round 5 audit of the finite covering step for the weaker supply.
The generic lemmas keep numerical bounds as explicit hypotheses; the actual
`Real.log 100` corollaries use the separately proved rational certificate.
This module does not prove any density, arithmetic supply, or finite-sieve
conclusion.
-/
set_option autoImplicit false
namespace Entry002
open scoped BigOperators

/-- Overlapping equally spaced closed intervals cover their whole span. -/
theorem independent_grid_cover (n : ℕ) {d h t : ℝ}
    (hdh : d ≤ h) (ht0 : 0 ≤ t) (ht : t ≤ (n : ℝ) * d + h) :
    ∃ k : ℕ, k ≤ n ∧ (k : ℝ) * d ≤ t ∧ t ≤ (k : ℝ) * d + h := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · simpa using ht0
      · simpa using ht
  | succ n ih =>
      by_cases ht' : t ≤ (n : ℝ) * d + h
      · obtain ⟨k, hkn, hlo, hhi⟩ := ih ht'
        exact ⟨k, hkn.trans (Nat.le_succ n), hlo, hhi⟩
      · refine ⟨n + 1, le_rfl, ?_, ht⟩
        push_cast
        have hlt := lt_of_not_ge ht'
        linarith

theorem independent_weak_window_log_width_lower :
    (1 / 21 : ℝ) ≤ Real.log (21 / 20 : ℝ) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 21 / 20)
  norm_num at hh ⊢
  exact hh

theorem independent_weak_window_log_width_lt_one :
    Real.log (21 / 20 : ℝ) < 1 := by
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 20)
  norm_num at hh
  linarith

theorem independent_weak_window_step_bounds {L : ℝ}
    (hLlo : (4605 / 1000 : ℝ) ≤ L) (hLhi : L ≤ (4606 / 1000 : ℝ)) :
    (1 / 40 : ℝ) ≤ 5 * L - 23 ∧
      5 * L - 23 ≤ (3 / 100 : ℝ) ∧
      5 * L - 23 < Real.log (21 / 20 : ℝ) := by
  have hh := independent_weak_window_log_width_lower
  constructor
  · linarith
  constructor <;> linarith

/-- The exact forty closed phase intervals cover `[0,1]`. -/
theorem independent_weak_window_forty_cover {L t : ℝ}
    (hLlo : (4605 / 1000 : ℝ) ≤ L) (hLhi : L ≤ (4606 / 1000 : ℝ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ k : ℕ, k < 40 ∧ (k : ℝ) * (5 * L - 23) ≤ t ∧
      t ≤ (k : ℝ) * (5 * L - 23) + Real.log (21 / 20 : ℝ) := by
  obtain ⟨hdlo, _, hdh⟩ := independent_weak_window_step_bounds hLlo hLhi
  have hh := independent_weak_window_log_width_lower
  have ht : t ≤ (39 : ℝ) * (5 * L - 23) + Real.log (21 / 20 : ℝ) := by
    linarith
  obtain ⟨k, hk, hlo, hhi⟩ := independent_grid_cover 39 hdh.le ht0 ht
  exact ⟨k, by omega, hlo, hhi⟩

/-- An atom is caught by an integer translate of one selected window in each
196-block. This is a real interval statement, without any equidistribution
or irrationality assumption. -/
theorem independent_weak_window_integer_catch {L : ℝ}
    (hLlo : (4605 / 1000 : ℝ) ≤ L) (hLhi : L ≤ (4606 / 1000 : ℝ))
    (b : ℕ) (x : ℝ) :
    ∃ k : ℕ, k < 40 ∧ ∃ m : ℤ,
      (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * L ≤ x ∧
      x ≤ (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * L +
        Real.log (21 / 20 : ℝ) := by
  let s : ℝ := x - (196 * b : ℕ) * L
  let a : ℤ := ⌊s⌋
  have ha0 : 0 ≤ s - (a : ℝ) := by
    dsimp [a]
    exact sub_nonneg.mpr (Int.floor_le s)
  have ha1 : s - (a : ℝ) ≤ 1 := by
    dsimp [a]
    exact sub_le_iff_le_add.mpr (by
      simpa only [add_comm] using (Int.lt_floor_add_one s).le)
  obtain ⟨k, hk, hlo, hhi⟩ :=
    independent_weak_window_forty_cover hLlo hLhi ha0 ha1
  refine ⟨k, hk, a - 23 * (k : ℤ), ?_, ?_⟩
  · dsimp [s] at hlo
    push_cast at hlo ⊢
    nlinarith only [hlo]
  · dsimp [s] at hhi
    push_cast at hhi ⊢
    nlinarith only [hhi]

/-- All forty selected offsets lie in their advertised 196-block. -/
theorem independent_weak_window_block_offset {b k q : ℕ}
    (hb : b < q) (hk : k < 40) :
    196 * b ≤ 196 * b + 5 * k ∧ 196 * b + 5 * k < 196 * q := by
  omega

/-- Interior atoms are caught using an integer in the requested range.
The lower margin `196*q*L+h` is deliberately conservative and fixed for `q`.
-/
theorem independent_weak_window_integer_catch_in_range {L : ℝ}
    (hLlo : (4605 / 1000 : ℝ) ≤ L) (hLhi : L ≤ (4606 / 1000 : ℝ))
    {q b : ℕ} (hb : b < q) (M N : ℤ) (x : ℝ)
    (hxlo : (M : ℝ) + ((196 * q : ℕ) : ℝ) * L +
      Real.log (21 / 20 : ℝ) ≤ x) (hxhi : x ≤ (N : ℝ)) :
    ∃ k : ℕ, k < 40 ∧ ∃ m : ℤ, M ≤ m ∧ m ≤ N ∧
      (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * L ≤ x ∧
      x ≤ (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * L +
        Real.log (21 / 20 : ℝ) := by
  obtain ⟨k, hk, m, hlo, hhi⟩ := independent_weak_window_integer_catch hLlo hLhi b x
  have hL0 : 0 ≤ L := by linarith
  have hw := (independent_weak_window_block_offset hb hk).2
  have hw' : ((196 * b + 5 * k : ℕ) : ℝ) ≤ ((196 * q : ℕ) : ℝ) := by
    exact_mod_cast hw.le
  have hprod := mul_le_mul_of_nonneg_right hw' hL0
  have hprod0 : 0 ≤ ((196 * b + 5 * k : ℕ) : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg _) hL0
  have hmlo : (M : ℝ) ≤ (m : ℝ) := by linarith
  have hmhi : (m : ℝ) ≤ (N : ℝ) := by linarith
  exact ⟨k, hk, m, by exact_mod_cast hmlo, by exact_mod_cast hmhi, hlo, hhi⟩

/-- Actual logarithmic phases, with no unproved numerical premise. -/
theorem independent_actual_weak_window_forty_cover {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ k : ℕ, k < 40 ∧ (k : ℝ) * (5 * Real.log (100 : ℝ) - 23) ≤ t ∧
      t ≤ (k : ℝ) * (5 * Real.log (100 : ℝ) - 23) + Real.log (21 / 20 : ℝ) := by
  exact independent_weak_window_forty_cover weakSupplyWindow_log100_bounds.1
    weakSupplyWindow_log100_bounds.2 ht0 ht1

/-- An actual atom is caught once in each 196-block using the frozen integer
base parameter and the original actual logarithmic window width. -/
theorem independent_actual_weak_window_integer_catch (b : ℕ) (x : ℝ) :
    ∃ k : ℕ, k < 40 ∧ ∃ m : ℤ,
      (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * Real.log (100 : ℝ) ≤ x ∧
      x ≤ (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * Real.log (100 : ℝ) +
        Real.log (21 / 20 : ℝ) := by
  exact independent_weak_window_integer_catch weakSupplyWindow_log100_bounds.1
    weakSupplyWindow_log100_bounds.2 b x

/-- The actual 196-block catch with the endpoint margin and range guards. -/
theorem independent_actual_weak_window_integer_catch_in_range
    {q b : ℕ} (hb : b < q) (M N : ℤ) (x : ℝ)
    (hxlo : (M : ℝ) + ((196 * q : ℕ) : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ) ≤ x) (hxhi : x ≤ (N : ℝ)) :
    ∃ k : ℕ, k < 40 ∧ ∃ m : ℤ, M ≤ m ∧ m ≤ N ∧
      (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * Real.log (100 : ℝ) ≤ x ∧
      x ≤ (m : ℝ) + ((196 * b + 5 * k : ℕ) : ℝ) * Real.log (100 : ℝ) +
        Real.log (21 / 20 : ℝ) := by
  exact independent_weak_window_integer_catch_in_range weakSupplyWindow_log100_bounds.1
    weakSupplyWindow_log100_bounds.2 hb M N x hxlo hxhi

/-- Maximum total weight in a residue class preserves at least `1/K` of
the finite supply, and enforces the exact global `K`-separation guard. -/
theorem independent_weighted_thin_bins (J : Finset ℕ) (weight : ℕ → ℝ)
    {K : ℕ} (hK : 0 < K) :
    ∃ a < K, (∑ j ∈ J, weight j) / (K : ℝ) ≤
      ∑ j ∈ J.filter (fun j => j % K = a), weight j ∧
      ∀ i ∈ J.filter (fun j => j % K = a),
        ∀ j ∈ J.filter (fun j => j % K = a), i < j → i + K ≤ j := by
  classical
  have hh : (Finset.range K).card • ((∑ j ∈ J, weight j) / (K : ℝ)) ≤
      ∑ j ∈ J, weight j := by
    rw [Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (by exact_mod_cast hK.ne')]
  obtain ⟨a, ha, hc⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := J) (t := Finset.range K) (f := fun j => j % K) (w := weight)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hK))
    (Finset.nonempty_range_iff.mpr hK.ne') hh
  refine ⟨a, Finset.mem_range.mp ha, hc, ?_⟩
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hd : i % K = j % K := hi'.trans hj'.symm
  have hei := Nat.mod_add_div i K
  have hej := Nat.mod_add_div j K
  have hq : i / K < j / K := by nlinarith only [hei, hej, hd, hij]
  nlinarith only [hei, hej, hd, hq]

end Entry002
