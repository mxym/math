import ErdosSimilarityGrowingGaps.Basic
import ErdosSimilarityGrowingGaps.GreedySampling
import ErdosSimilarityGrowingGaps.GreedyTailBounds
import ErdosSimilarityGrowingGaps.SequenceGeometry
import ErdosSimilarityGrowingGaps.HerrorActivation
import ErdosSimilarityGrowingGaps.SequenceRouting
import ErdosSimilarityGrowingGaps.SequenceRoutingProbability
import ErdosSimilarityGrowingGaps.SequenceSignatures
import ErdosSimilarityGrowingGaps.First
import ErdosSimilarityGrowingGaps.Corollary
import ErdosSimilarityGrowingGaps.Input
import ErdosSimilarityGrowingGaps.AnnulusSequence
import ErdosSimilarityGrowingGaps.WindowBridge
import ErdosSimilarityGrowingGaps.GridBoundary
import ErdosSimilarityGrowingGaps.VariableTree
import ErdosSimilarityGrowingGaps.FiniteRouting
import ErdosSimilarityGrowingGaps.Avoidance
import ErdosSimilarityGrowingGaps.TailAnalysis
import ErdosSimilarityGrowingGaps.RobustExhaustion
import ErdosSimilarityGrowingGaps.ParameterStrata
import ErdosSimilarityGrowingGaps.SignFiberQuadratic
import ErdosSimilarityGrowingGaps.LineSignQuadratic
import ErdosSimilarityGrowingGaps.ParameterStrataQuadratic
import ErdosSimilarityGrowingGaps.RoutingMain
import ErdosSimilarityGrowingGaps.GeometricMain
import ErdosSimilarityGrowingGaps.ExplicitExample
import ErdosSimilarityGrowingGaps.WindowRepair
import ErdosSimilarityGrowingGaps.ScheduledAnnulus
import ErdosSimilarityGrowingGaps.SequenceTransfer
import ErdosSimilarityGrowingGaps.RoutingSampleMap
import ErdosSimilarityGrowingGaps.RoutingSequenceBridge
import ErdosSimilarityGrowingGaps.UniformPowerTransfer
import ErdosSimilarityGrowingGaps.SequenceCounting
import ErdosSimilarityGrowingGaps.SequenceGreedyRouting
import ErdosSimilarityGrowingGaps.SequenceGreedyFamily
import ErdosSimilarityGrowingGaps.SequenceGreedyProbability
import ErdosSimilarityGrowingGaps.VariableSchedule
import ErdosSimilarityGrowingGaps.VariableBridge
import ErdosSimilarityGrowingGaps.SequenceTransferFill
import ErdosSimilarityGrowingGaps.SequenceFiniteAssembly
import ErdosSimilarityGrowingGaps.SequenceStableGeometry
import ErdosSimilarityGrowingGaps.SequenceStableProbability
import ErdosSimilarityGrowingGaps.GlobalGreedyTests
import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker

namespace ErdosSimilarityGrowingGaps
open GrowingGap
open Set MeasureTheory Filter Topology
open scoped BigOperators
open scoped ENNReal

/-- Public replay roots for the formally closed sampling layer. -/
theorem replay_first_sample :
    ∀ (Z : LogScale) (v : ℝ),
      ∃ n : ℕ, v ≤ Z.z n ∧ ∀ m : ℕ, m < n → Z.z m < v := by
  intro Z v
  exact exists_first_ge Z v

theorem replay_annular_sampling :
    ∀ (Z : LogScale), ConsecutiveLogGapLittleO Z → AnnularFilling Z := by
  intro Z h
  exact consecutiveGap_implies_annularFilling h

theorem replay_greedy_sampling_gap
    {Z : LogScale} {U R D v δ : ℝ} (hfill : FillsAnnulus Z U R D)
    (hδ : 0 < δ) (i : ℕ)
    (hlo : U / R ≤ Z.z (greedyIndex Z v δ i))
    (hhi : Z.z (greedyIndex Z v δ i) + δ + D ≤ R * U) :
    δ ≤ Z.z (greedyIndex Z v δ (i + 1)) -
      Z.z (greedyIndex Z v δ i) ∧
    Z.z (greedyIndex Z v δ (i + 1)) -
      Z.z (greedyIndex Z v δ i) ≤ δ + D :=
  greedyIndex_log_gap_lt_of_filling hfill hδ i hlo hhi

theorem replay_greedy_sampling_separation
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) :
    Function.Injective (greedyIndex Z v δ) :=
  greedyIndex_injective Z v δ hδ

theorem replay_sequence_offset_identity
    (Z : LogScale) (m : ℕ) (s t : ℝ) (k : ℤ) :
    t * (2 : ℝ) ^ k * (input Z m) ^ s =
      t * (2 : ℝ) ^ ((k : ℝ) - s * Z.z m) :=
  sequence_shifted_offset Z m s t k

theorem replay_sequence_active_range
    (Z : LogScale) (s₀ s₁ x u v : ℝ) (m : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k u v p) :
    x < sequencePoint Z m ((2 : ℝ) ^ k) x p ∧
      sequencePoint Z m ((2 : ℝ) ^ k) x p < x + (2 : ℝ) ^ (1 - u) :=
  sequence_active_point_range Z s₀ s₁ x u v m k p hp

theorem replay_sequence_local_address_separation
    {M d t : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (x : ℝ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (child : Fin t → Fin (M - 1))
    (indices : Fin t → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (hindex : Function.Injective (fun i => (child i, indices i)))
    (hactive : ∀ i, sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)) p)
    (hgap : ∀ i j, i ≠ j → child i = child j →
      3 ≤ p.1.1 * |Z.z (indices j) - Z.z (indices i)|) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v child
        (fun i => sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p))
      (localTerminalAddresses c hM hd v child
        (fun i => sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) :=
  sequence_local_address_separation Z c hM hd hL hU x bits v child indices k p
    hindex hactive hgap

theorem replay_sequence_fixed_parameter_joint_miss
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (s₀ s₁ x : ℝ) (k : ℤ) (p : ℝ)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (r : PowerParams s₀ s₁)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap : ∀ i j, i ≠ j → children i = children j →
      3 ≤ r.1.1 * |Z.z (indices j) - Z.z (indices i)|) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
        (fun i => ⟨v, children i⟩) indices r ω) =
      tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        (1 - p / 2) ^
          (sequenceActiveLocalCandidates Z c v children indices k r).card :=
  sequence_fixed_parameter_joint_miss Z c hM hd hL hU s₀ s₁ x k p bits v children indices r
    hindex hgap

theorem replay_sequence_continuum_joint_miss_bound_of_lower_gap
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (p s₀ s₁ x η : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hs : s₀ ≤ s₁) (k : ℤ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) = ell)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap₀ : ∀ i j, i ≠ j → children i = children j →
      3 ≤ s₀ * |Z.z (indices j) - Z.z (indices i)|)
    (hmany : ∀ r : PowerParams s₀ s₁, η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k r).card) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
          (fun i => ⟨v, children i⟩) indices r ω) ≤
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) :=
  sequence_continuum_joint_miss_bound_of_lower_gap Z c hM hd hL hU p s₀ s₁ x η hp₀ hp₁ hs k bits v children indices ell hell hindex hgap₀ hmany

theorem replay_sequence_local_miss_representatives
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (k : ℤ)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) = ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        ∀ ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd),
          sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
            (fun i => ⟨v, children i⟩) indices r ω ↔
          sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
            (fun i => ⟨v, children i⟩) indices p ω :=
  sequence_local_miss_representatives Z c hM hd hL s₀ s₁ x hs k v children indices ell hell

theorem replay_sequence_center_separation
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (m : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0 < ell) (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k (u : ℝ) ((u : ℝ) + ell) p) :
    gridAddress (u + ell - 1)
        (sequencePoint Z m ((2 : ℝ) ^ k) x p) ≠ gridAddress (u + ell - 1) x :=
  sequence_active_gridAddress_ne_center Z s₀ s₁ x u ell m k hu hell p hp

theorem replay_sequence_grid_separation
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (m m' : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0 < ell) (p : PowerParams s₀ s₁)
    (hgap : 3 ≤ p.1.1 * (Z.z m' - Z.z m))
    (hp : sequencePowerActivation Z m k (u : ℝ) ((u : ℝ) + ell) p)
    (hp' : sequencePowerActivation Z m' k (u : ℝ) ((u : ℝ) + ell) p) :
    gridAddress (u + ell - 1)
        (sequencePoint Z m ((2 : ℝ) ^ k) x p) ≠
      gridAddress (u + ell - 1)
        (sequencePoint Z m' ((2 : ℝ) ^ k) x p) :=
  sequence_gridAddress_ne_of_log_gap Z s₀ s₁ x u ell m m' k hu hell p hgap hp hp'

theorem replay_sampled_output_buffer
    {Z : LogScale} {f : ℝ → ℝ} {B : Set ℝ} {n : ℕ}
    {s α y c M v D r : ℝ} (hs : 0 < s) (hα : 0 < α) (hM : 0 ≤ M)
    (happrox : |f (input Z n) - y - c * (input Z n) ^ s| ≤
      M * (input Z n) ^ (s + α))
    (hideal : y + c * (2 : ℝ) ^ (-v * s) ∈ B)
    (hpower : |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
      |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)))
    (hwidth : |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) +
        M * (input Z n) ^ (s + α) < r) :
    f (input Z n) ∈ Metric.thickening r B :=
  sampled_output_mem_thickening hs hα hM happrox hideal hpower hwidth

theorem replay_grid_boundary_budget (N : ℕ) (hN : 0 < N) (R : ℝ) :
    unitDensity (gridBoundaryBad N R) ≤ ENNReal.ofReal ((N : ℝ) * R) :=
  unitDensity_gridBoundaryBad_le N hN R

theorem replay_window_power_error
    {Z : LogScale} {U R D v s c : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hs : 0 < s) :
    ∃ n : ℕ,
      |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
        |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) :=
  h.sample_power_error hv hvD hs

theorem replay_sample_powerPoint_error
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C : ℝ} (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hC : 0 ≤ C) :
    ∃ n : ℕ,
      |powerPoint (input Z n) C (x, p) -
        powerPoint ((2 : ℝ) ^ (-v)) C (x, p)| ≤
        |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
          (2 : ℝ) ^ (-(v + D) * p.1.1)) :=
  h.sample_powerPoint_error hK hv hvD hC

theorem replay_sample_powerPoint_stable_key
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C : ℝ} {b : ℕ} (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hC : 0 ≤ C)
    (hstable : NoGridBoundary (2 ^ (b + 3)) x R)
    (hideal : x ≤ powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ∧
      powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ≤ x + R) :
    ∃ n : ℕ,
      gridAddress b (powerPoint (input Z n) C (x, p)) =
        gridAddress b (powerPoint ((2 : ℝ) ^ (-v)) C (x, p)) :=
  h.sample_powerPoint_stable_key hK hv hvD hC hstable hideal

theorem replay_sample_powerPoint_mem_thickening
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C r : ℝ} (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hC : 0 ≤ C)
    {G : Set ℝ}
    (hideal : powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ∈ G)
    (hwidth : |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
      (2 : ℝ) ^ (-(v + D) * p.1.1)) < r) :
    ∃ n : ℕ,
      powerPoint (input Z n) C (x, p) ∈ Metric.thickening r G :=
  h.sample_powerPoint_mem_thickening hK hv hvD hC hideal hwidth

theorem replay_sequence_missedCenters_transfer
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (r : ℝ)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening r G) :
    sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
    powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      tests k windows G :=
  sequence_missedCenters_subset_power_missedCenters tests k windows G r sample
    hactivate hpoint

theorem replay_sequence_activation_of_sample_interval
    {Z : LogScale} {K : ℕ} {n m : ℕ} {k : ℤ}
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (e : Fin W) (D : ℝ)
    (p : PowerParams (1 / (K : ℝ)) K) (hK : 2 ≤ K)
    (hideal : p ∈ powerActivation n k (windows e).1 (windows e).2)
    (hlo : (n : ℝ) ≤ Z.z m) (hhi : Z.z m ≤ (n : ℝ) + D)
    (hmargin : p.1.1 * D < (windows e).2 -
      (p.1.1 * (n : ℝ) - (k : ℝ))) :
    p ∈ sequenceWindowActivations Z m k windows :=
  sequence_activation_of_sample_interval windows e D p hK hideal hlo hhi hmargin

theorem replay_sequence_outcome_density
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (r p : ℝ)
    (sample : ℕ → ℕ)
    (hsubset : sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
      powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G)
    (houtcome : unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G) ≤ ENNReal.ofReal (5 * p)) :
    unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        Z (tests.image sample) k windows (Metric.thickening r G)) ≤
      ENNReal.ofReal (5 * p) :=
  sequence_outcome_density_of_power_outcome tests k windows G r p sample
    hsubset houtcome

theorem replay_late_window {Z : LogScale} (hW : WindowFilling Z)
    (R : ℕ) (hR : 2 ≤ R) (U₀ η : ℝ) (hU₀ : 0 < U₀) (hη : 0 < η) :
    ∃ U : ℕ, ∃ D : ℝ, U₀ ≤ (U : ℝ) ∧ 1 < Real.log (U : ℝ) ∧
      FillsAnnulus Z (U : ℝ) R D ∧
      D / Real.log (Real.log (U : ℝ)) < η :=
  hW.exists_late_annulus R hR U₀ η hU₀ hη

theorem replay_variable_tree_span (b g L : ℝ) (hb : 2 ≤ b) (hg : 0 ≤ g)
    (n : ℕ) : span b g L (n + 1) + 2 * g ≤ b * (2 * b) ^ n * (L + 2 * g) :=
  uniform_span b g L hb hg n

theorem replay_distinct_terminal_all_miss
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    (p : ℝ) (address : I → T) (hinj : Function.Injective address) :
    (∑ τ : T → Bool, bitTableWeight p τ *
      ∏ i, if τ (address i) = true then 0 else 1) =
      (1 - p) ^ Fintype.card I :=
  distinct_terminal_all_miss p address hinj

theorem replay_uniform_power_tail
    {s₀ s₁ C : ℝ} (hs₀ : 0 < s₀) (hs₀₁ : s₀ ≤ s₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x : ℝ, ∀ p : PowerParams s₀ s₁,
        |powerPoint (dyadic n) C (x, p) - x| < ε :=
  powerPoint_uniform_tail hs₀ hs₀₁ ε hε

theorem replay_compact_power_blocker {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal δ ∧ CompactPowerHits H K k N :=
  exists_compact_power_blocker hK hδ hδ₁

theorem replay_geometric_main_target : MainTarget :=
  geometric_main_target

theorem replay_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ := by
  obtain ⟨E, hEc, hEp, hEi, _, _⟩ :=
    closed_periodic_avoidance_of_blockers B ε hε hε1 hsum
  exact ⟨E, hEc, hEp, hEi⟩

theorem replay_compact_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Set.Icc (0 : ℝ) 1 ∧ interior K = ∅ := by
  obtain ⟨K, hKc, hKsub, hKi, _, _⟩ :=
    compact_restriction_of_blockers B ε hε hε1 hsum
  exact ⟨K, hKc, hKsub, hKi⟩

theorem replay_theorem2_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (hB : WindowBlockerSpec F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ := by
  obtain ⟨E, hEc, hEp, hEi, _⟩ := theorem2_of_windowBlockerSpec hB ε hε hε1
  exact ⟨E, hEc, hEp, hEi⟩

theorem replay_tail_grid_reduction {Z : LogScale} {H : Set ℝ}
    (hH : GridWeakRobustBlocker Z H) : RobustBlocker Z H :=
  weakRobustBlocker_implies_robust (gridWeakRobustBlocker_implies_weak hH)

theorem replay_robust_exhaustion_of_compactRobustSpec
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (hC : CompactRobustFamilySpec F) :
    WindowBlockerSpec F :=
  robustExhaustion_of_compactRobustSpec hC

theorem replay_compactRobustSpec_of_uniformPowerTransfer
    {Z : LogScale} (hT : UniformPowerTransferSpec Z) :
    CompactRobustSpec Z :=
  compactRobustSpec_of_uniformPowerTransfer hT

theorem replay_parameter_representatives (m : ℕ)
    (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ) :
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧ reps.card ≤ 3 ^ m := by
  obtain ⟨reps, hrep, hcard, _⟩ :=
    finite_parameter_representatives m cuts lo hi
  exact ⟨reps, hrep, hcard⟩

theorem replay_quadratic_parameter_representatives (m : ℕ)
    (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ)
    (hlo : lo.1 ≤ hi.1) (hhi : lo.2 ≤ hi.2) :
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧ reps.card ≤ 20 * (m + 5) ^ 2 := by
  obtain ⟨reps, hrep, hcard, _⟩ :=
    quadratic_arrangement_representative_bound m cuts lo hi hlo hhi
  exact ⟨reps, hrep, hcard⟩

theorem replay_budget_allocation {ι : Type*} [Countable ι] [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ι → ℝ≥0∞, (∀ i, 0 < b i) ∧ ∑' i, b i < ENNReal.ofReal ε :=
  exists_budget_allocation hε

theorem replay_grid_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} {ε : ℝ}
    (w : ι × (ℕ × ℕ) → ℝ≥0∞)
    (hw : ∑' p, w p < ENNReal.ofReal ε)
    (hgrid : ∀ (i : ι) (j q : ℕ), ∃ H : Set ℝ,
      IsOpen H ∧ OnePeriodic H ∧ unitDensity H ≤ w (i, (j, q)) ∧
      ∀ s y c : ℝ, 0 < s → c ≠ 0 →
        ∀ f : ℝ → ℝ,
          TailApproximation (F i) f s (1 / (j + 1 : ℝ)) y c q →
          ∀ ρ : ℝ, 0 < ρ →
            ∃ n : ℕ, input (F i) n < ρ ∧ f (input (F i) n) ∈ H) :
    ∃ B : BlockerFamily F, ∑' i, B.budget i < ENNReal.ofReal ε :=
  blockerFamily_of_grid_blockers w hw hgrid

theorem replay_window_filling (Z : LogScale) (h : ConsecutiveLogGapLittleO Z) :
    WindowFilling Z := consecutiveGap_implies_windowFilling h

theorem replay_input_sequence (Z : LogScale) :
    (∀ n, 0 < input Z n) ∧ StrictAnti (input Z) ∧
      Filter.Tendsto (input Z) Filter.atTop (nhds 0) ∧
      ∀ n, -Real.logb 2 (input Z n) = Z.z n := by
  exact ⟨input_pos Z, input_strictAnti Z, input_tendsto_zero Z, input_logb Z⟩

theorem replay_uniform_tail_error_budget {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {α q r : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        q * (input Z n) ^ (p.1.1 + α) < r :=
  uniform_tail_error_budget hK hα hq hr

theorem replay_sequence_repair_all_centers {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (G V : Set ℝ) (r : ℝ) (hr : 0 < r) (hV : IsOpen V)
    (hcover : sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z tests k windows (Metric.thickening r G) ⊆ V)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (p : PowerParams (1 / (K : ℝ)) K) (n : ℕ), n ∈ tests →
      p ∈ sequenceWindowActivations Z n k windows →
        q * (input Z n) ^ (p.1.1 + α) < r) :
    CompactRobustHits Z (Metric.thickening (2 * r) G ∪ V) K k N α q :=
  sequence_repair_all_centers hK tests k windows G V r hr hV hcover N htail α q hα hq herror

theorem replay_routing_schedule_eventual (K : ℕ) (hK : 2 ≤ K) (k : ℤ)
    (N : ℕ) (p : ℝ) (hp : 0 < p) :
    ∀ᶠ U : ℕ in atTop, ∃ s : RoutingSchedule K k N p,
      s.template.origin = U :=
  routing_schedule_eventually_at_origin K hK k N p hp

theorem replay_scheduled_annulus
    {Z : LogScale} (hW : WindowFilling Z)
    (K : ℕ) (hK : 2 ≤ K) (k : ℤ) (N : ℕ) (p : ℝ) (hp : 0 < p)
    (R : ℕ) (hR : 2 ≤ R) (η : ℝ) (hη : 0 < η) :
    ∃ U : ℕ → ℕ, ∃ D : ℕ → ℝ, ∃ j : ℕ, ∃ s : RoutingSchedule K k N p,
      s.template.origin = U j ∧
      1 < Real.log (U j : ℝ) ∧
      FillsAnnulus Z (U j) R (D j) ∧
      D j / Real.log (Real.log (U j : ℝ)) < η :=
  hW.exists_scheduled_annulus K hK k N p hp R hR η hη

theorem replay_routing_sample_index_bounds
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D ≤ c.baseLength) (e : RoutingEdge M d) :
    (c.edgeStart e : ℝ) ≤ Z.z (routingSampleIndex Z c D e) ∧
      Z.z (routingSampleIndex Z c D e) ≤ (c.edgeStart e : ℝ) + D :=
  routingSampleIndex_bounds c hM hL hspan hR hfill hD e

theorem replay_routing_sample_index_injective
    {Z : LogScale} {M d t : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D < c.baseLength) (edges : Fin t → RoutingEdge M d)
    (hstart : Function.Injective (fun i => c.edgeStart (edges i)))
    (hsep : ∀ i j, c.edgeStart (edges i) < c.edgeStart (edges j) →
      c.edgeEnd (edges i) + 1 ≤ c.edgeStart (edges j)) :
    Function.Injective (fun i => routingSampleIndex Z c D (edges i)) :=
  routingSampleIndex_injective c hM hL hspan hR hfill hD edges hstart hsep

theorem replay_routing_sample_index_activation
    {Z : LogScale} {M d K : ℕ} (c : RoutingTemplate M d)
    {D : ℝ} (hD : 0 ≤ D) (e : RoutingEdge M d)
    {k : ℤ} (p : PowerParams (1 / (K : ℝ)) K) (hK : 2 ≤ K)
    (hp : p ∈ powerActivation (c.edgeStart e) k
      (c.edgeStart e) ((c.edgeStart e : ℝ) + c.edgeLength e))
    (hsample : (c.edgeStart e : ℝ) ≤ Z.z (routingSampleIndex Z c D e))
    (hsample' : Z.z (routingSampleIndex Z c D e) ≤
      (c.edgeStart e : ℝ) + D)
    (hmargin : p.1.1 * D <
      (c.edgeStart e : ℝ) + c.edgeLength e -
        (p.1.1 * (c.edgeStart e : ℝ) - (k : ℝ))) :
    p ∈ sequenceWindowActivations Z (routingSampleIndex Z c D e) k
      (fun _ : Fin 1 => ((c.edgeStart e : ℝ),
        (c.edgeStart e : ℝ) + c.edgeLength e)) :=
  routingSampleIndex_activation_of_margin c hD e p hK hp hsample hsample' hmargin




theorem replay_routing_sample_index_filling_activation
    {Z : LogScale} {M d K : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D ≤ c.baseLength) (e : RoutingEdge M d)
    {k : ℤ} (p : PowerParams (1 / (K : ℝ)) K) (hK : 2 ≤ K)
    (hp : p ∈ powerActivation (c.edgeStart e) k
      (c.edgeStart e) ((c.edgeStart e : ℝ) + c.edgeLength e))
    (hmargin : p.1.1 * D <
      (c.edgeStart e : ℝ) + c.edgeLength e -
        (p.1.1 * (c.edgeStart e : ℝ) - (k : ℝ))) :
    p ∈ sequenceWindowActivations Z (routingSampleIndex Z c D e) k
      (fun _ : Fin 1 => ((c.edgeStart e : ℝ),
        (c.edgeStart e : ℝ) + c.edgeLength e)) :=
  routingSampleIndex_activation_of_filling_margin c hM hL hspan hR hfill hD e p hK hp hmargin

theorem replay_periodic_sequence_blocker_of_power_transfer
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (hGp : OnePeriodic G)
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ q : PowerParams (1 / (K : ℝ)) K,
        q ∈ windowActivations n k windows →
        q ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (q : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, q) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, q) ∈
        Metric.thickening r G)
    (N : ℕ) (htail : ∀ n ∈ tests.image sample, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (q₀ : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      n ∈ tests.image sample →
      q₀ ∈ sequenceWindowActivations Z n k windows →
        q * (input Z n) ^ (q₀.1.1 + α) < r)
    (houtcome : unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G) ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧
      CompactRobustHits Z H K k N α q :=
  periodic_sequence_blocker_of_power_transfer hK tests k windows G hGp r p hr hp sample
    hactivate hpoint N htail α q hα hq herror houtcome

theorem replay_finite_sequence_routing_blocker
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p)
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (N : ℕ) (htail : ∀ n ∈ finiteSequenceRoutingTests s, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      n ∈ finiteSequenceRoutingTests s →
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows s.template) →
        q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius s.template p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧
      CompactRobustHits Z H K k N α q :=
  finite_sequence_routing_blocker s hK hp hp₁ N htail α q hα hq herror

theorem replay_compactRobustSpec_of_finiteSequenceBlockerSpec
    {Z : LogScale} (hB : FiniteSequenceBlockerSpec Z) :
    CompactRobustSpec Z :=
  compactRobustSpec_of_finiteSequenceBlockerSpec hB

theorem replay_finiteSequenceBlockerSpec_of_windowFilling_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingFiniteSequenceProvider Z) :
    FiniteSequenceBlockerSpec Z :=
  finiteSequenceBlockerSpec_of_windowFilling_provider hW hP

theorem replay_routing_sample_index_all_edges_injective
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D < c.baseLength) :
    Function.Injective (routingSampleIndex Z c D) :=
  routingSampleIndex_all_edges_injective c hM hL hspan hR hfill hD

theorem replay_routing_edge_start_injective
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) :
    Function.Injective c.edgeStart :=
  routingEdge_edgeStart_injective c hM hL

theorem replay_explicit_example_gap {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    ConsecutiveLogGapLittleO (explicitLogScale β hβ) :=
  explicitLogScale_consecutiveGapLittleO hβ hβ₁

theorem replay_explicit_example_ratio {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => input (explicitLogScale β hβ) (n + 1) /
      input (explicitLogScale β hβ) n) atTop (𝓝 0) :=
  explicitLogScale_input_ratio_tendsto_zero hβ

theorem replay_input_ratio_zero {Z : LogScale}
    (hgap : Filter.Tendsto (fun n : ℕ => Z.z (n + 1) - Z.z n)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => input Z (n + 1) / input Z n)
      Filter.atTop (nhds 0) :=
  input_ratio_tendsto_zero hgap

#print axioms replay_uniform_power_tail
#print axioms replay_compact_power_blocker
#print axioms replay_geometric_main_target
#print axioms replay_window_filling
#print axioms replay_input_sequence
#print axioms replay_input_ratio_zero
#print axioms replay_first_sample
#print axioms replay_greedy_sampling_gap
#print axioms replay_sequence_offset_identity
#print axioms replay_sequence_active_range
#print axioms replay_sequence_fixed_parameter_joint_miss
#print axioms replay_sequence_continuum_joint_miss_bound_of_lower_gap
#print axioms replay_sequence_local_miss_representatives
#print axioms replay_sequence_local_address_separation
#print axioms replay_sequence_center_separation
#print axioms replay_sequence_grid_separation
#print axioms replay_greedy_sampling_separation
#print axioms replay_annular_sampling
#print axioms replay_late_window
#print axioms replay_grid_boundary_budget
#print axioms replay_window_power_error
#print axioms replay_sample_powerPoint_error
#print axioms replay_sample_powerPoint_stable_key
#print axioms replay_sample_powerPoint_mem_thickening
#print axioms replay_sequence_missedCenters_transfer
#print axioms replay_sequence_activation_of_sample_interval
#print axioms replay_sequence_outcome_density
#print axioms replay_sampled_output_buffer
#print axioms replay_variable_tree_span
#print axioms replay_distinct_terminal_all_miss
#print axioms replay_blocker_assembly
#print axioms replay_compact_blocker_assembly
#print axioms replay_theorem2_assembly
#print axioms replay_tail_grid_reduction
#print axioms replay_robust_exhaustion_of_compactRobustSpec
#print axioms replay_compactRobustSpec_of_uniformPowerTransfer
#print axioms replay_parameter_representatives
#print axioms replay_quadratic_parameter_representatives
#print axioms replay_budget_allocation
#print axioms replay_grid_blocker_assembly
#print axioms replay_routing_schedule_eventual
#print axioms replay_scheduled_annulus
#print axioms replay_routing_sample_index_bounds
#print axioms replay_routing_sample_index_injective
#print axioms replay_routing_sample_index_activation
#print axioms replay_routing_edge_start_injective
#print axioms replay_routing_sample_index_all_edges_injective
#print axioms replay_routing_sample_index_filling_activation
#print axioms replay_periodic_sequence_blocker_of_power_transfer
#print axioms finite_sequence_routing_blocker
#print axioms compactRobustSpec_of_finiteSequenceBlockerSpec
#print axioms replay_finiteSequenceBlockerSpec_of_windowFilling_provider
#print axioms greedyIndex_log_upper_of_filling_prefix
#print axioms greedyIndex_log_lower
#print axioms exists_greedyIndex_crossing
#print axioms open_window_card_lower_of_gap_le
#print axioms greedy_open_window_card_lower
#print axioms sequenceActiveLocalCandidates_card_ge_of_greedy_filter
#print axioms exists_sequenceActiveLocalCandidates_card_ge_of_greedy
#print axioms sequenceActiveLocalCandidates_hmany_of_injective_active
#print axioms variableDepth_log_littleO
#print axioms variableDepth_default_budget
#print axioms filled_firstGe_transfer_subfields
#print axioms exists_power_routing_data
#print axioms exists_sequenceRouting_outcome_density_add_le_of_stable
#print axioms sequence_routing_blocker_of_stable_estimate
#print axioms sequence_missedCenters_subset_power_missedCenters_buffer
#print axioms sequence_active_preceding_gridAddress_eq
#print axioms sequence_stable_earlier_address_agreement
#print axioms sequence_stable_local_success_mem_routedSet
#print axioms sequence_missed_center_forces_vertex_miss
#print axioms sequence_missed_center_forces_vertex_miss_sampled
#print axioms sequence_stable_missed_center_probability_le_of_vertex_bound
#print axioms scheduled_vertex_sequence_continuum_joint_miss_bound
#print axioms globalRoutingWindow_active_bounds
#print axioms globalRoutingTests_firstGe_activation
#print axioms greedyWindowSamples_injective
#print axioms greedyWindowSamples_gap
#print axioms sequenceGreedyWindow_hmany_and_gap
#print axioms sequenceGreedyActive_card_mono
#print axioms sequenceActiveLocalCandidates_card_ge_of_childwise
#print axioms sequenceActiveLocalCandidates_hmany_of_childwise
#print axioms exists_common_greedy_family
#print axioms sequence_missed_center_forces_vertex_miss_of_list
#print axioms sequence_stable_missed_center_probability_le_of_vertex_bound_of_list
#print axioms scheduled_vertex_sequence_continuum_joint_miss_bound_of_list

end ErdosSimilarityGrowingGaps
