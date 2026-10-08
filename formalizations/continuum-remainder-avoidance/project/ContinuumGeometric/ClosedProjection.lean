import ContinuumGeometric.GeometricParameters
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
Section 7: strict activation makes the failure relation closed. Compactness
of the actual parameter rectangle makes its projection closed on all real
centers. No representative-set theorem, probability assumption, analytic-set
projection theorem, or uniform blocker is used.
-/
namespace ContinuumGeometric

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

end ContinuumGeometric
