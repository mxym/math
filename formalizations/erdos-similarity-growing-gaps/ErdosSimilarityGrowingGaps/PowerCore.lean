import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic


namespace ErdosSimilarityGrowingGaps

open Filter Topology

noncomputable def dyadic (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- Exact equality for every index, not approximation of a real exponent. -/
theorem dyadic_power_eq (s : ℝ) (n : ℕ) :
    (dyadic n) ^ s = ((1 / 2 : ℝ) ^ s) ^ n := by
  unfold dyadic
  calc
    ((1 / 2 : ℝ) ^ n) ^ s = (1 / 2 : ℝ) ^ ((n : ℝ) * s) :=
      (Real.rpow_natCast_mul (by norm_num) n s).symm
    _ = (1 / 2 : ℝ) ^ (s * (n : ℝ)) := by rw [mul_comm]
    _ = ((1 / 2 : ℝ) ^ s) ^ n := Real.rpow_mul_natCast (by norm_num) s n

/-- The entire continuum of ratios is parametrized by positive real powers. -/
theorem geometric_parameter (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ s : ℝ, 0 < s ∧ ∀ n : ℕ, q ^ n = (dyadic n) ^ s := by
  refine ⟨Real.logb (1 / 2) q, ?_, ?_⟩
  · exact Real.logb_pos_of_base_lt_one (by norm_num) (by norm_num) hq₀ hq₁
  · intro n
    rw [dyadic_power_eq, Real.rpow_logb (by norm_num) (by norm_num) hq₀]

/-- The limit used for repairing exceptional centers; it allows either sign of `a`. -/
theorem affine_geometric_tendsto (a b q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (fun n : ℕ => a * q ^ n + b) atTop (𝓝 b) := by
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁).const_mul a).add_const b

/-- A neighborhood of the limiting center hits every geometric tail. -/
theorem every_tail_hits_open (V : Set ℝ) (hV : IsOpen V)
    (a b q : ℝ) (hb : b ∈ V) (hq₀ : 0 < q) (hq₁ : q < 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∈ V := by
  have hev : ∀ᶠ n : ℕ in atTop, a * q ^ n + b ∈ V :=
    (affine_geometric_tendsto a b q hq₀ hq₁).eventually (hV.mem_nhds hb)
  rcases (eventually_atTop.1 hev) with ⟨K, hK⟩
  exact ⟨max N K, le_max_left _ _, hK _ (le_max_right _ _)⟩

end ErdosSimilarityGrowingGaps

/-!
Section 7: strict activation makes the failure relation closed. Compactness
of the actual parameter rectangle makes its projection closed on all real
centers. No representative-set theorem, probability assumption, analytic-set
projection theorem, or uniform blocker is used.
-/
namespace ErdosSimilarityGrowingGaps

open Set Filter Topology

section General
variable {X P Y ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y]

def failureRelation (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) : Set (X × P) :=
  ⋂ i, (Prod.snd ⁻¹' (active i)ᶜ) ∪ (point i ⁻¹' hitᶜ)

def missedCenters (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) : Set X :=
  Prod.fst '' failureRelation active hit point

omit [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y] in
theorem mem_failureRelation_iff (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) (z : X × P) :
    z ∈ failureRelation active hit point ↔
      ∀ i, z.2 ∈ active i → point i z ∉ hit := by
  classical
  simp [failureRelation, or_iff_not_imp_left]

theorem isClosed_failureRelation (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) (hactive : ∀ i, IsOpen (active i))
    (hhit : IsOpen hit) (hpoint : ∀ i, Continuous (point i)) :
    IsClosed (failureRelation active hit point) := by
  apply isClosed_iInter
  intro i
  exact ((hactive i).isClosed_compl.preimage continuous_snd).union
    (hhit.isClosed_compl.preimage (hpoint i))

omit [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y] in
theorem mem_missedCenters_iff (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) (x : X) :
    x ∈ missedCenters active hit point ↔
      ∃ p : P, ∀ i, p ∈ active i → point i (x, p) ∉ hit := by
  constructor
  · rintro ⟨⟨x', p⟩, hbad, hcenter⟩
    change x' = x at hcenter
    subst x'
    exact ⟨p, (mem_failureRelation_iff active hit point (x, p)).1 hbad⟩
  · rintro ⟨p, hp⟩
    exact ⟨(x, p), (mem_failureRelation_iff active hit point (x, p)).2 hp, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y] in
theorem not_mem_missedCenters_iff (active : ι → Set P) (hit : Set Y)
    (point : ι → X × P → Y) (x : X) :
    x ∉ missedCenters active hit point ↔
      ∀ p : P, ∃ i, p ∈ active i ∧ point i (x, p) ∈ hit := by
  classical
  rw [mem_missedCenters_iff]
  simp

/-- Closed projection needs compact parameters, not compactness or a grid of centers. -/
theorem isClosed_missedCenters [CompactSpace P]
    (active : ι → Set P) (hit : Set Y) (point : ι → X × P → Y)
    (hactive : ∀ i, IsOpen (active i)) (hhit : IsOpen hit)
    (hpoint : ∀ i, Continuous (point i)) :
    IsClosed (missedCenters active hit point) := by
  exact isClosedMap_fst_of_compactSpace _
    (isClosed_failureRelation active hit point hactive hhit hpoint)

end General

/-- The actual compact exponent/coefficient rectangle, including both endpoints. -/
abbrev PowerParams (s₀ s₁ : ℝ) := Icc s₀ s₁ × Icc (1 : ℝ) 2

noncomputable def powerPoint {s₀ s₁ : ℝ} (input C : ℝ)
    (z : ℝ × PowerParams s₀ s₁) : ℝ :=
  z.1 + z.2.2.1 * C * input ^ z.2.1.1

theorem continuous_powerPoint (s₀ s₁ input C : ℝ) (hinput : input ≠ 0) :
    Continuous (powerPoint (s₀ := s₀) (s₁ := s₁) input C) := by
  have hs : Continuous (fun z : ℝ × PowerParams s₀ s₁ => z.2.1.1) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have ht : Continuous (fun z : ℝ × PowerParams s₀ s₁ => z.2.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact continuous_fst.add ((ht.mul continuous_const).mul
    ((Real.continuous_const_rpow hinput).comp hs))

def powerActivation {s₀ s₁ : ℝ} (n : ℕ) (k u v : ℝ) : Set (PowerParams s₀ s₁) :=
  {p | u < p.1.1 * n - k ∧ p.1.1 * n - k < v}

theorem isOpen_powerActivation (s₀ s₁ : ℝ) (n : ℕ) (k u v : ℝ) :
    IsOpen (powerActivation (s₀ := s₀) (s₁ := s₁) n k u v) := by
  have hs : Continuous (fun p : PowerParams s₀ s₁ => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  exact isOpen_Ioo.preimage ((hs.mul continuous_const).sub continuous_const)

def windowActivations {s₀ s₁ : ℝ} (n : ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) : Set (PowerParams s₀ s₁) :=
  ⋃ e, powerActivation n k (windows e).1 (windows e).2

theorem isOpen_windowActivations (s₀ s₁ : ℝ) (n : ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) :
    IsOpen (windowActivations (s₀ := s₀) (s₁ := s₁) n k windows) := by
  exact isOpen_iUnion fun e => isOpen_powerActivation s₀ s₁ n k _ _

noncomputable def powerMissedCenters {s₀ s₁ : ℝ} (tests : Finset ℕ)
    (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ) (B₁ : Set ℝ) : Set ℝ :=
  missedCenters (P := PowerParams s₀ s₁)
    (fun i : {n // n ∈ tests} => windowActivations i.1 k windows)
    B₁ (fun i => powerPoint (dyadic i.1) ((2 : ℝ) ^ k))

/-- Section 7 closedness for the actual finite dyadic tests and strict routing windows. -/
theorem isClosed_powerMissedCenters (s₀ s₁ : ℝ) (tests : Finset ℕ)
    (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ) (B₁ : Set ℝ)
    (hB₁ : IsOpen B₁) :
    IsClosed (powerMissedCenters (s₀ := s₀) (s₁ := s₁) tests k windows B₁) := by
  apply isClosed_missedCenters
  · intro i
    exact isOpen_windowActivations s₀ s₁ i.1 k windows
  · exact hB₁
  · intro i
    apply continuous_powerPoint
    exact ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) i.1)

/-- The real missed-center set is Borel measurable directly from closedness. -/
theorem measurableSet_powerMissedCenters (s₀ s₁ : ℝ) (tests : Finset ℕ)
    (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ) (B₁ : Set ℝ)
    (hB₁ : IsOpen B₁) :
    MeasurableSet (powerMissedCenters (s₀ := s₀) (s₁ := s₁) tests k windows B₁) :=
  (isClosed_powerMissedCenters s₀ s₁ tests k windows B₁ hB₁).measurableSet

/-- The infinite sequence remains available outside the finite routing index set. -/
theorem power_tail_hits_open (s₀ s₁ C x : ℝ) (hs₀ : 0 < s₀)
    (p : PowerParams s₀ s₁) (V : Set ℝ) (hV : IsOpen V) (hx : x ∈ V) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ powerPoint (dyadic n) C (x, p) ∈ V := by
  have hs : 0 < p.1.1 := lt_of_lt_of_le hs₀ p.1.2.1
  have hq₀ : 0 < (1 / 2 : ℝ) ^ p.1.1 := Real.rpow_pos_of_pos (by norm_num) _
  have hq₁ : (1 / 2 : ℝ) ^ p.1.1 < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hs
  obtain ⟨n, hn, hhit⟩ := every_tail_hits_open V hV (p.2.1 * C) x
    ((1 / 2 : ℝ) ^ p.1.1) hx hq₀ hq₁ N
  refine ⟨n, hn, ?_⟩
  simpa [powerPoint, dyadic_power_eq, add_comm] using hhit

/-- Full center repair, with zero error and the two open buffers kept distinct.

The hypotheses provide already chosen finite tests and an open cover V of R;
there is no hypothesis asserting a uniform blocker or a probability bound.
Outside R an active finite point hits B₁ ⊆ B₂. Inside R an arbitrary late
point of the infinite sequence hits V, even if absent from the finite tests.
-/
theorem power_repair_all_centers (s₀ s₁ : ℝ) (hs₀ : 0 < s₀)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ B₂ V : Set ℝ) (hB₁₂ : B₁ ⊆ B₂) (hV : IsOpen V)
    (hcover : powerMissedCenters (s₀ := s₀) (s₁ := s₁) tests k windows B₁ ⊆ V)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n) :
    ∀ (x : ℝ) (p : PowerParams s₀ s₁),
      ∃ n : ℕ, N ≤ n ∧ powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ B₂ ∪ V := by
  classical
  intro x p
  by_cases hx : x ∈ powerMissedCenters (s₀ := s₀) (s₁ := s₁) tests k windows B₁
  · obtain ⟨n, hn, hhit⟩ := power_tail_hits_open s₀ s₁ ((2 : ℝ) ^ k) x hs₀ p V hV
      (hcover hx) N
    exact ⟨n, hn, Or.inr hhit⟩
  · have hfinite := (not_mem_missedCenters_iff
      (fun i : {n // n ∈ tests} => windowActivations (s₀ := s₀) (s₁ := s₁) i.1 k windows)
      B₁ (fun i => powerPoint (dyadic i.1) ((2 : ℝ) ^ k)) x).1 hx
    obtain ⟨i, _, hhit⟩ := hfinite p
    exact ⟨i.1, htail i.1 i.2, Or.inl (hB₁₂ hhit)⟩

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

open Filter Topology

/-- Uniform tail control on the compact power rectangle.  The center variable
is unrestricted because the power perturbation is independent of it. -/
theorem powerPoint_uniform_tail
    {s₀ s₁ C : ℝ} (hs₀ : 0 < s₀) (hs₀₁ : s₀ ≤ s₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x : ℝ, ∀ p : PowerParams s₀ s₁,
        |powerPoint (dyadic n) C (x, p) - x| < ε := by
  have hq₀ : 0 < (1 / 2 : ℝ) ^ s₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hq₁ : (1 / 2 : ℝ) ^ s₀ < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hs₀
  have hlim : Tendsto (fun n : ℕ => (dyadic n) ^ s₀) atTop (𝓝 0) := by
    rw [show (fun n : ℕ => (dyadic n) ^ s₀) =
      (fun n : ℕ => ((1 / 2 : ℝ) ^ s₀) ^ n) by
        funext n; exact dyadic_power_eq s₀ n]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁
  have hconst : 0 ≤ 2 * |C| := by positivity
  by_cases hC : 2 * |C| = 0
  · have hC' : C = 0 := by
      have : |C| = 0 := by nlinarith
      exact abs_eq_zero.mp this
    refine ⟨0, ?_⟩
    intro n _ x p
    simpa [powerPoint, hC'] using hε
  · have hev : ∀ᶠ n : ℕ in atTop, 2 * |C| * (dyadic n) ^ s₀ < ε :=
      hlim.const_mul (2 * |C|) |>.eventually (Iio_mem_nhds (by simpa using hε))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, ?_⟩
    intro n hn x p
    have hdy : 0 < dyadic n := by
      unfold dyadic
      positivity
    have hdy1 : dyadic n ≤ 1 := by
      unfold dyadic
      exact (pow_le_one₀ (by positivity) (by norm_num : (1 / 2 : ℝ) ≤ 1))
    have hpow : (dyadic n) ^ p.1.1 ≤ (dyadic n) ^ s₀ := by
      apply Real.rpow_le_rpow_of_exponent_ge hdy hdy1
      exact p.1.2.1
    rw [powerPoint]
    have habs : |p.2.1 * C| ≤ 2 * |C| := by
      rw [abs_mul, abs_of_nonneg (by linarith [p.2.2.1])]
      exact mul_le_mul_of_nonneg_right p.2.2.2 (abs_nonneg C)
    have hnonneg : 0 ≤ (dyadic n) ^ p.1.1 := Real.rpow_nonneg hdy.le _
    have hbound : |p.2.1 * C| * (dyadic n) ^ p.1.1 ≤
        2 * |C| * (dyadic n) ^ s₀ :=
      calc
        _ ≤ (2 * |C|) * (dyadic n) ^ p.1.1 :=
          mul_le_mul_of_nonneg_right habs hnonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hconst
    have hform : (x, p).1 + (x, p).2.2.1 * C * (dyadic n) ^ (x, p).2.1.1 - x =
        p.2.1 * C * (dyadic n) ^ p.1.1 := by ring
    rw [hform, abs_mul, abs_of_nonneg hnonneg]
    exact hbound.trans_lt (hN n hn)

end ErdosSimilarityGrowingGaps
