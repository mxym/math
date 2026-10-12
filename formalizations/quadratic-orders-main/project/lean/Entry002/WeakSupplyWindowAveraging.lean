import Entry002.WeakSupplyWindowIndependentGrid
import Mathlib.Tactic

/-! Actual finite 196-block counting and averaging. Every finite mass and
endpoint condition is explicit. This file does not postulate a cofinal supply
or fill the former arithmetic density field. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open scoped BigOperators Classical

noncomputable def weakWindowCatches (x : ℝ) (m w : ℕ) : Prop :=
  (m : ℝ) + (w : ℝ) * Real.log (100 : ℝ) ≤ x ∧
  x ≤ (m : ℝ) + (w : ℝ) * Real.log (100 : ℝ) + Real.log (21 / 20 : ℝ)

noncomputable def weakWindowAtomCatches (q M N : ℕ) (x : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc M N) ×ˢ (Finset.range (196 * q))).filter
    (fun mw => weakWindowCatches x mw.1 mw.2)

theorem weakWindow_nat_catch_in_range {q b : ℕ} (hb : b < q) (M N : ℕ) (x : ℝ)
    (hxlo : (M : ℝ) + ((196 * q : ℕ) : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ) ≤ x) (hxhi : x ≤ (N : ℝ)) :
    ∃ k : ℕ, k < 40 ∧ ∃ m : ℕ, M ≤ m ∧ m ≤ N ∧
      weakWindowCatches x m (196 * b + 5 * k) := by
  obtain ⟨k, hk, m, hmlo, hmhi, hlo, hhi⟩ :=
    independent_actual_weak_window_integer_catch_in_range hb (M : ℤ) (N : ℤ) x
      (by simpa using hxlo) (by simpa using hxhi)
  have hm0 : 0 ≤ m := le_trans (Int.natCast_nonneg M) hmlo
  have hmcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0
  refine ⟨k, hk, m.toNat, ?_, ?_, ?_⟩
  · have hh : (M : ℤ) ≤ (m.toNat : ℤ) := by simpa only [hmcast] using hmlo
    exact_mod_cast hh
  · have hh : (m.toNat : ℤ) ≤ (N : ℤ) := by simpa only [hmcast] using hmhi
    exact_mod_cast hh
  · have hmreal : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hmcast
    simpa only [weakWindowCatches, hmreal] using And.intro hlo hhi

/-- A genuine atom beyond the fixed lower margin has at least one distinct
catch in each of the `q` 196-blocks. -/
theorem weakWindow_atom_catches_card_ge (q M N : ℕ) (x : ℝ)
    (hxlo : (M : ℝ) + ((196 * q : ℕ) : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ) ≤ x) (hxhi : x ≤ (N : ℝ)) :
    q ≤ (weakWindowAtomCatches q M N x).card := by
  classical
  have hcatch (b : Fin q) := weakWindow_nat_catch_in_range b.isLt M N x hxlo hxhi
  choose k hk m hmlo hmhi hmc using hcatch
  let f : Fin q → ℕ × ℕ := fun b => (m b, 196 * b.val + 5 * k b)
  have hmaps : ∀ b ∈ (Finset.univ : Finset (Fin q)),
      f b ∈ weakWindowAtomCatches q M N x := by
    intro b _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hmlo b, hmhi b⟩,
      Finset.mem_range.mpr (independent_weak_window_block_offset b.isLt (hk b)).2⟩, ?_⟩
    exact hmc b
  have hfinj : Function.Injective f := by
    intro b₁ b₂ he
    have hw := congrArg Prod.snd he
    dsimp [f] at hw
    have hk₁ := hk b₁
    have hk₂ := hk b₂
    apply Fin.ext
    omega
  have hh := Finset.card_le_card_of_injOn f hmaps
    (fun a _ b _ he => hfinj he)
  simpa only [Finset.card_univ, Fintype.card_fin] using hh

noncomputable def weakWindowFiniteMass (atoms : Finset ℕ) (coord weight : ℕ → ℝ)
    (q m : ℕ) : ℝ := by
  classical
  exact ∑ j ∈ atoms, ∑ w ∈ Finset.range (196 * q),
    if weakWindowCatches (coord j) m w then weight j else 0

theorem weakWindow_atom_weighted_count (q M N : ℕ) (x v : ℝ) :
    (∑ m ∈ Finset.Icc M N, ∑ w ∈ Finset.range (196 * q),
      if weakWindowCatches x m w then v else 0) =
      ((weakWindowAtomCatches q M N x).card : ℝ) * v := by
  classical
  change (∑ m ∈ Finset.Icc M N, ∑ w ∈ Finset.range (196 * q),
    (fun mw : ℕ × ℕ => if weakWindowCatches x mw.1 mw.2 then v else 0) (m, w)) = _
  rw [← Finset.sum_product (Finset.Icc M N) (Finset.range (196 * q))
    (fun mw : ℕ × ℕ => if weakWindowCatches x mw.1 mw.2 then v else 0)]
  rw [← Finset.sum_filter]
  simp only [weakWindowAtomCatches, Finset.sum_const, nsmul_eq_mul]

/-- Finite double counting of the actual closed logarithmic windows. There
is no exchange of an infinite sum and no assumption of equidistribution. -/
theorem weakWindow_finite_weighted_double_count (atoms : Finset ℕ)
    (coord weight : ℕ → ℝ) (q M N : ℕ)
    (hweight : ∀ j ∈ atoms, 0 ≤ weight j)
    (hlo : ∀ j ∈ atoms, (M : ℝ) + ((196 * q : ℕ) : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ) ≤ coord j)
    (hhi : ∀ j ∈ atoms, coord j ≤ (N : ℝ)) :
    (q : ℝ) * (∑ j ∈ atoms, weight j) ≤
      ∑ m ∈ Finset.Icc M N, weakWindowFiniteMass atoms coord weight q m := by
  classical
  calc
    _ = ∑ j ∈ atoms, (q : ℝ) * weight j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ atoms, ((weakWindowAtomCatches q M N (coord j)).card : ℝ) * weight j := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hweight j hj)
      exact_mod_cast weakWindow_atom_catches_card_ge q M N (coord j) (hlo j hj) (hhi j hj)
    _ = _ := by
      simp_rw [← weakWindow_atom_weighted_count]
      rw [Finset.sum_comm]
      rfl

/-- Finite averaging gives an actual natural integer base at least `M`.
This conditional finite lemma does not promote a cofinal supply to an
eventual statement for all bases. -/
theorem weakWindow_finite_average (atoms : Finset ℕ)
    (coord weight : ℕ → ℝ) (q M N : ℕ) (hMN : M ≤ N)
    (hweight : ∀ j ∈ atoms, 0 ≤ weight j)
    (hlo : ∀ j ∈ atoms, (M : ℝ) + ((196 * q : ℕ) : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ) ≤ coord j)
    (hhi : ∀ j ∈ atoms, coord j ≤ (N : ℝ)) :
    ∃ m : ℕ, M ≤ m ∧ m ≤ N ∧
      ((q : ℝ) * ∑ j ∈ atoms, weight j) / ((N - M + 1 : ℕ) : ℝ) ≤
        weakWindowFiniteMass atoms coord weight q m := by
  classical
  have hI : (Finset.Icc M N).Nonempty := ⟨M, Finset.mem_Icc.mpr ⟨le_rfl, hMN⟩⟩
  have hcard0 : ((Finset.Icc M N).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hI).ne'
  have hbound := weakWindow_finite_weighted_double_count atoms coord weight q M N
    hweight hlo hhi
  have havg : (Finset.Icc M N).card •
      (((q : ℝ) * ∑ j ∈ atoms, weight j) / ((Finset.Icc M N).card : ℝ)) ≤
      ∑ m ∈ Finset.Icc M N, weakWindowFiniteMass atoms coord weight q m := by
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hcard0]
    exact hbound
  have havg' : (∑ _m ∈ Finset.Icc M N,
      ((q : ℝ) * ∑ j ∈ atoms, weight j) / ((Finset.Icc M N).card : ℝ)) ≤
      ∑ m ∈ Finset.Icc M N, weakWindowFiniteMass atoms coord weight q m := by
    simpa only [Finset.sum_const] using havg
  obtain ⟨m, hm, havg⟩ := Finset.exists_le_of_sum_le hI havg'
  refine ⟨m, (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2, ?_⟩
  have hcard : (Finset.Icc M N).card = N - M + 1 := by
    rw [Nat.card_Icc]
    omega
  simpa only [hcard] using havg

/-- A fixed base has disjoint actual logarithmic windows. -/
theorem weakWindow_catch_unique {x : ℝ} {m u v : ℕ}
    (hu : weakWindowCatches x m u) (hv : weakWindowCatches x m v) : u = v := by
  have hLlo := weakSupplyWindow_log100_bounds.1
  have hL0 : 0 ≤ Real.log (100 : ℝ) := by linarith
  have hh := independent_weak_window_log_width_lt_one
  have hnot (i k : ℕ) (hik : i < k) (hi : weakWindowCatches x m i)
      (hk : weakWindowCatches x m k) : False := by
    have hcast : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ k)
    have hmul := mul_le_mul_of_nonneg_right hcast hL0
    obtain ⟨_, hihi⟩ := hi
    obtain ⟨hklo, _⟩ := hk
    nlinarith only [hmul, hihi, hklo, hh, hLlo]
  rcases lt_trichotomy u v with huv | he | hvu
  · exact (hnot u v huv hu hv).elim
  · exact he
  · exact (hnot v u hvu hv hu).elim

/-- The logarithmic atom condition is exactly the original sieve window. -/
theorem weakWindow_catches_log_bin_iff {j : ℕ} (hj : 0 < j) (m w : ℕ) :
    weakWindowCatches (Real.log ((j : ℝ) * Real.log 2)) m w ↔
      (100 : ℝ)^w * Real.exp m ≤ (j : ℝ) * Real.log 2 ∧
      (j : ℝ) * Real.log 2 ≤ (21 / 20) * ((100 : ℝ)^w * Real.exp m) := by
  have hj0 : 0 < (j : ℝ) * Real.log 2 :=
    mul_pos (by exact_mod_cast hj) (Real.log_pos (by norm_num))
  have hscale : Real.exp ((m : ℝ) + (w : ℝ) * Real.log (100 : ℝ)) =
      (100 : ℝ)^w * Real.exp m := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    ring
  have hupper : Real.exp ((m : ℝ) + (w : ℝ) * Real.log (100 : ℝ) +
      Real.log (21 / 20 : ℝ)) = (21 / 20) * ((100 : ℝ)^w * Real.exp m) := by
    rw [Real.exp_add, hscale, Real.exp_log (by norm_num)]
    ring
  unfold weakWindowCatches
  rw [Real.le_log_iff_exp_le hj0, Real.log_le_iff_le_exp hj0, hscale, hupper]

noncomputable def weakWindowSelectedBins (atoms : Finset ℕ) (coord : ℕ → ℝ)
    (m w : ℕ) : Finset ℕ := atoms.filter (fun j => weakWindowCatches (coord j) m w)

theorem weakWindowSelectedBins_pairwise_disjoint (atoms : Finset ℕ)
    (coord : ℕ → ℝ) (m W : ℕ) :
    (↑(Finset.range W) : Set ℕ).PairwiseDisjoint (weakWindowSelectedBins atoms coord m) := by
  intro u _ v _ huv
  apply Finset.disjoint_left.mpr
  intro j hju hjv
  have hu := (Finset.mem_filter.mp hju).2
  have hv := (Finset.mem_filter.mp hjv).2
  exact huv (weakWindow_catch_unique hu hv)

/-- At a fixed base, the double sum counts each selected atom just once.
This identifies the finite averaging output with the weight of the genuine
union of selected window bins, including possibly empty individual windows. -/
theorem weakWindow_finite_mass_eq_union (atoms : Finset ℕ) (coord weight : ℕ → ℝ)
    (q m : ℕ) :
    weakWindowFiniteMass atoms coord weight q m =
      ∑ j ∈ (Finset.range (196 * q)).biUnion (weakWindowSelectedBins atoms coord m),
        weight j := by
  classical
  rw [Finset.sum_biUnion (weakWindowSelectedBins_pairwise_disjoint atoms coord m (196 * q))]
  unfold weakWindowFiniteMass weakWindowSelectedBins
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

end Entry002
