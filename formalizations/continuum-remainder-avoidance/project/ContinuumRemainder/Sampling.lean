import ContinuumRemainder.Specification
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ContinuumRemainder

open Set Filter Topology
open ContinuumGeometric

/-- Data selected from the prescribed set itself; it is discharged by
`LogSyndetic.exists_sampledLogConfiguration`, rather than an extra premise. -/
structure SampledLogConfiguration (A : Set ℝ) (s₀ : ℝ) (h : ℕ) where
  a : ℕ → ℝ
  z : ℕ → ℝ
  B : ℝ
  a_mem : ∀ n, a n ∈ A
  a_pos : ∀ n, 0 < a n
  a_tail : ∀ n, a n < dyadic h
  z_eq : ∀ n, z n = -Real.logb 2 (a n)
  z_nonneg : ∀ n, 0 ≤ z n
  gap_lower : ∀ n, 3 / s₀ < z (n + 1) - z n
  gap_upper : ∀ n, z (n + 1) - z n < B
  B_pos : 0 < B
  z_tendsto : Tendsto z atTop atTop

namespace SampledLogConfiguration

theorem a_eq_rpow {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (C : SampledLogConfiguration A s₀ h) (n : ℕ) :
    C.a n = (2 : ℝ) ^ (-C.z n) := by
  rw [C.z_eq, neg_neg]
  exact (Real.rpow_logb (by norm_num) (by norm_num) (C.a_pos n)).symm

theorem power_eq_rpow {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (C : SampledLogConfiguration A s₀ h) (n : ℕ) (s : ℝ) :
    (C.a n) ^ s = (2 : ℝ) ^ (-s * C.z n) := by
  rw [C.a_eq_rpow, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

theorem a_tendsto {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (C : SampledLogConfiguration A s₀ h) : Tendsto C.a atTop (𝓝 0) := by
  have hz : Tendsto (fun n => -C.z n) atTop atBot :=
    tendsto_neg_atTop_atBot.comp C.z_tendsto
  convert (tendsto_rpow_atBot_of_base_gt_one (2 : ℝ) (by norm_num)).comp hz using 1
  ext n
  exact C.a_eq_rpow n

theorem z_strictMono {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (C : SampledLogConfiguration A s₀ h) (hs₀ : 0 < s₀) : StrictMono C.z := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp : 0 < 3 / s₀ := by positivity
  linarith [C.gap_lower n]

theorem a_strictAnti {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (C : SampledLogConfiguration A s₀ h) (hs₀ : 0 < s₀) : StrictAnti C.a := by
  intro i j hij
  rw [C.a_eq_rpow, C.a_eq_rpow]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  exact neg_lt_neg (C.z_strictMono hs₀ hij)

end SampledLogConfiguration

theorem dyadic_eq_rpow_neg (j : ℕ) : dyadic j = (2 : ℝ) ^ (-(j : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp [dyadic]

/-- Each occupied half-open dyadic bin supplies a point with logarithm in the
corresponding opposite half-open interval. -/
theorem logarithm_bin_bounds {a : ℝ} {j : ℕ}
    (ha : a ∈ Ioc (dyadic (j + 1)) (dyadic j)) :
    0 < a ∧ (j : ℝ) ≤ -Real.logb 2 a ∧ -Real.logb 2 a < (j : ℝ) + 1 := by
  have hp : 0 < a := (by unfold dyadic; positivity : 0 < dyadic (j + 1)).trans ha.1
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp ha.2
  have hu := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by unfold dyadic; positivity : 0 < dyadic (j + 1)) ha.1
  rw [dyadic_eq_rpow_neg, Real.logb_rpow (by norm_num) (by norm_num)] at hl hu
  push_cast at hu
  exact ⟨hp, by linarith, by linarith⟩

/-- Recursive occupied-bin choice with the actual syndetic gap budget. -/
theorem LogSyndetic.exists_spaced_bins {A : Set ℝ} (hA : LogSyndetic A)
    (m h : ℕ) (hm : 0 < m) :
    ∃ G : ℕ, 0 < G ∧ ∃ j : ℕ → ℕ,
      (∀ n, OccupiedBin A (j n)) ∧ (∀ n, h < j n) ∧
      (∀ n, j n + m ≤ j (n + 1) ∧ j (n + 1) < j n + m + G) ∧
      (∀ n, n ≤ j n) := by
  classical
  obtain ⟨G, J, hG, _, hcover⟩ := hA
  let start := max J (h + 1)
  obtain ⟨j₀, hj₀, _, ho₀⟩ := hcover start (le_max_left _ _)
  have hh₀ : h < j₀ := by have := le_max_right J (h + 1); omega
  have hJ₀ : J ≤ j₀ := (le_max_left _ _).trans hj₀
  let State := {j : ℕ // J ≤ j ∧ h < j ∧ OccupiedBin A j}
  have step : ∀ st : State, ∃ st' : State,
      st.1 + m ≤ st'.1 ∧ st'.1 < st.1 + m + G := by
    intro st
    obtain ⟨j', hj', hj'u, ho'⟩ := hcover (st.1 + m) (by omega)
    exact ⟨⟨j', by exact ⟨by omega, by omega, ho'⟩⟩, hj', hj'u⟩
  let seq : ℕ → State := fun n => Nat.rec ⟨j₀, hJ₀, hh₀, ho₀⟩
    (fun _ st => Classical.choose (step st)) n
  have hseq : ∀ n, (seq n).1 + m ≤ (seq (n + 1)).1 ∧
      (seq (n + 1)).1 < (seq n).1 + m + G := by
    intro n
    exact Classical.choose_spec (step (seq n))
  refine ⟨G, hG, (fun n => (seq n).1), (fun n => (seq n).2.2.2),
    (fun n => (seq n).2.2.1), hseq, ?_⟩
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    change n ≤ (seq n).1 at ih
    change n + 1 ≤ (seq (n + 1)).1
    have := (hseq n).1
    omega

/-- The prescribed configuration supplies the uniformly spaced subsequence
required by all output windows, including arbitrarily late requested tails. -/
theorem LogSyndetic.exists_sampledLogConfiguration {A : Set ℝ}
    (hA : LogSyndetic A) (s₀ : ℝ) (_hs₀ : 0 < s₀) (h : ℕ) :
    Nonempty (SampledLogConfiguration A s₀ h) := by
  classical
  let m := Nat.ceil (3 / s₀) + 2
  have hm : 0 < m := by dsimp [m]; omega
  obtain ⟨G, hG, j, ho, hjh, hstep, hjn⟩ := hA.exists_spaced_bins m h hm
  let a : ℕ → ℝ := fun n => Classical.choose (ho n)
  have ha : ∀ n, a n ∈ A ∧ a n ∈ Ioc (dyadic (j n + 1)) (dyadic (j n)) :=
    fun n => Classical.choose_spec (ho n)
  let z : ℕ → ℝ := fun n => -Real.logb 2 (a n)
  have hzb : ∀ n, (j n : ℝ) ≤ z n ∧ z n < (j n : ℝ) + 1 :=
    fun n => (logarithm_bin_bounds (ha n).2).2
  have hznonneg : ∀ n, 0 ≤ z n := fun n => (Nat.cast_nonneg _).trans (hzb n).1
  refine ⟨{
    a := a
    z := z
    B := ((m + G : ℕ) : ℝ)
    a_mem := fun n => (ha n).1
    a_pos := fun n => (logarithm_bin_bounds (ha n).2).1
    a_tail := ?_
    z_eq := fun _ => rfl
    z_nonneg := hznonneg
    gap_lower := ?_
    gap_upper := ?_
    B_pos := ?_
    z_tendsto := ?_ }⟩
  · intro n
    apply (ha n).2.2.trans_lt
    rw [dyadic_eq_rpow_neg, dyadic_eq_rpow_neg]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    exact neg_lt_neg (by exact_mod_cast hjh n)
  · intro n
    have hc : 3 / s₀ ≤ (Nat.ceil (3 / s₀) : ℝ) := Nat.le_ceil _
    have hj : (j n : ℝ) + m ≤ j (n + 1) := by exact_mod_cast (hstep n).1
    have hmr : (m : ℝ) = (Nat.ceil (3 / s₀) : ℝ) + 2 := by simp [m]
    linarith [(hzb n).2, (hzb (n + 1)).1]
  · intro n
    have hj : (j (n + 1) : ℝ) + 1 ≤ (j n : ℝ) + m + G := by
      exact_mod_cast (hstep n).2
    push_cast
    linarith [(hzb n).1, (hzb (n + 1)).2]
  · exact_mod_cast (by omega : 0 < m + G)
  · apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact (by exact_mod_cast hjn n : (n : ℝ) ≤ j n).trans (hzb n).1

end ContinuumRemainder
