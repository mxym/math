import Entry002.GenericCommonWindowNumerics
import Entry002.GenericWalkTelescope

/-!
# Finite window choices before any walk

These are actual finite dyadic-bin selections and actual walk-word lengths.
The number of windows is chosen from the finite lattice step alphabet and
positive arithmetic constants, before a walk or residue family is supplied.
No coverage, information growth or no-walk conclusion is assumed here.
-/
set_option autoImplicit false
namespace Entry002
open Module
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

theorem exists_window_rate_excess (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) {c t : ℝ}
    (hc : 0<c) (ht : 0<t) :
    ∃ W : ℕ, 0<W ∧ Real.log (wordStepBall b e D).card+1 <
      (W:ℝ)*(c*t/10500000) := by
  have hr : 0<c*t/10500000 := by positivity
  obtain ⟨W,hW⟩ := exists_nat_gt
    (max 0 ((Real.log (wordStepBall b e D).card+1)/(c*t/10500000)))
  have hWpos : 0<W := by
    have hh : (0:ℝ)<W := (le_max_left _ _).trans_lt hW
    exact_mod_cast hh
  refine ⟨W,hWpos,?_⟩
  have hh := (le_max_right _ _).trans_lt hW
  exact (div_lt_iff₀ hr).mp hh

lemma allBins_member_window {W j : ℕ} (J : ℕ → Finset ℕ)
    (hj : j∈allBins W J) : ∃ w<W, j∈J w := by
  obtain ⟨w,hw,hj⟩ := Finset.mem_biUnion.mp hj
  exact ⟨w,Finset.mem_range.mp hw,hj⟩

lemma allBins_card_pos_of_density {W : ℕ} (J : ℕ → Finset ℕ)
    {X t : ℝ} (hW : 0<W) (hX : 0<X) (ht : 0<t)
    (hdense : ∀ w<W, t*((100:ℝ)^w*X)≤(J w).card) :
    0<(allBins W J).card := by
  have hh := hdense 0 hW
  simp only [pow_zero,one_mul] at hh
  have hcard : 0<(J 0).card := by
    exact_mod_cast (mul_pos ht hX).trans_le hh
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hcard
  apply Finset.card_pos.mpr
  exact ⟨j,Finset.mem_biUnion.mpr ⟨0,Finset.mem_range.mpr hW,hj⟩⟩

lemma enumerated_window_lengths_dvd {W n j : ℕ} (J : ℕ → Finset ℕ)
    (hcard : (allBins W J).card=n+1) (hj : j<n) :
    batchWordLength (binEnum (allBins W J) j) ∣
      batchWordLength (binEnum (allBins W J) (j+1)) := by
  apply batchWordLength_dvd
  exact (binEnum_strictMono (allBins W J) (Nat.lt_succ_self j)
    (by omega)).le

lemma enumerated_window_rate_lower {W : ℕ} (J : ℕ → Finset ℕ)
    {X c t : ℝ} (hX : 0<X) (hc : 0<c)
    (hb : ∀ w<W, ∀ j∈J w,
      (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hdense : ∀ w<W, t*((100:ℝ)^w*X)≤(J w).card) :
    (W:ℝ)*(c*t/10500000)≤
      ∑ i∈Finset.range (allBins W J).card,
        windowBatchRate c (binEnum (allBins W J) i) := by
  rw [binEnum_sum]
  exact allBins_rate J hX hc hb hdense

end Entry002
