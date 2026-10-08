import Entry005.FiniteHalfspaceConeLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Entry005.CompactProbabilitySubsequence

/-! Actual unit-ball laws lift to the compact Euclidean ball with exact
raw-coordinate pushforward recovery. This supplies compact probability laws
for the actual finite-body cone-law sequence. -/

noncomputable section
open Metric MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Entry005

abbrev CompactConeBall (d : ℕ) := {z : Space d // z ∈ closedBall (0 : Space d) 1}

instance compactConeBall_compactSpace (d : ℕ) : CompactSpace (CompactConeBall d) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) 1)

instance compactConeBall_inhabited (d : ℕ) : Inhabited (CompactConeBall d) :=
  ⟨⟨0, by simp⟩⟩

/-- The raw-coordinate embedding of the actual compact Euclidean unit ball. -/
def compactBallRaw {d : ℕ} (z : CompactConeBall d) : Fin d → ℝ :=
  WithLp.ofLp z.val

theorem continuous_compactBallRaw {d : ℕ} : Continuous (compactBallRaw (d := d)) :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp continuous_subtype_val

theorem measurable_compactBallRaw {d : ℕ} : Measurable (compactBallRaw (d := d)) :=
  continuous_compactBallRaw.measurable

/-- Outside the Euclidean unit ball, the measurable retraction takes value zero. -/
def rawToCompactBall {d : ℕ} (x : Fin d → ℝ) : CompactConeBall d :=
  ⟨if ‖WithLp.toLp 2 x‖ ≤ 1 then WithLp.toLp 2 x else 0, by
    split_ifs with hx
    · simpa only [mem_closedBall, dist_zero_right] using hx
    · simp⟩

theorem measurable_rawToCompactBall {d : ℕ} : Measurable (rawToCompactBall (d := d)) := by
  apply Measurable.subtype_mk
  exact Measurable.ite
    ((isClosed_le (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm continuous_const).measurableSet)
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable measurable_const

theorem compactBallRaw_retraction_of_norm_le {d : ℕ} (x : Fin d → ℝ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) : compactBallRaw (rawToCompactBall x) = x := by
  simp [compactBallRaw, rawToCompactBall, hx]

def compactBallLaw {d : ℕ} (ν : ProbabilityMeasure (Fin d → ℝ)) :
    ProbabilityMeasure (CompactConeBall d) := ν.map rawToCompactBall

theorem compactBallLaw_raw_pushforward {d : ℕ} (ν : ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) :
    (compactBallLaw ν : Measure (CompactConeBall d)).map compactBallRaw =
      (ν : Measure (Fin d → ℝ)) := by
  rw [compactBallLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_map measurable_compactBallRaw measurable_rawToCompactBall]
  calc
    _ = (ν : Measure (Fin d → ℝ)).map id := by
      apply Measure.map_congr
      filter_upwards [hball] with x hx
      exact compactBallRaw_retraction_of_norm_le x hx
    _ = _ := Measure.map_id

theorem compactBallLaw_raw_probability_pushforward {d : ℕ}
    (ν : ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) :
    (compactBallLaw ν).map compactBallRaw = ν :=
  Subtype.ext (compactBallLaw_raw_pushforward ν hball)

theorem compactBallLaw_integral_raw {d : ℕ} (ν : ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    (∫ z, f (compactBallRaw z) ∂(compactBallLaw ν : Measure (CompactConeBall d))) =
      ∫ x, f x ∂(ν : Measure (Fin d → ℝ)) := by
  rw [← compactBallLaw_raw_pushforward ν hball,
    integral_map measurable_compactBallRaw.aemeasurable hf.aestronglyMeasurable]

theorem compactBallLaw_integral_tendsto {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ))
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ν (φ k) : Measure (Fin d → ℝ))) atTop
      (𝓝 (∫ z, f (compactBallRaw z) ∂(μ : Measure (CompactConeBall d)))) := by
  let test : CompactConeBall d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => f (compactBallRaw z), hf.comp continuous_compactBallRaw⟩
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) test
  change Tendsto (fun k => ∫ z, f (compactBallRaw z)
    ∂(compactBallLaw (ν (φ k)) : Measure (CompactConeBall d))) atTop
      (𝓝 (∫ z, f (compactBallRaw z) ∂(μ : Measure (CompactConeBall d)))) at ht
  simp_rw [compactBallLaw_integral_raw _ (hball _) f hf] at ht
  exact ht

def compactBallRawLaw {d : ℕ} (μ : ProbabilityMeasure (CompactConeBall d)) :
    ProbabilityMeasure (Fin d → ℝ) := μ.map compactBallRaw

theorem compactBallRawLaw_ae_unit_ball {d : ℕ}
    (μ : ProbabilityMeasure (CompactConeBall d)) :
    ∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1 := by
  apply (ae_map_iff measurable_compactBallRaw.aemeasurable
    ((isClosed_le (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm continuous_const).measurableSet)).2
  apply Filter.Eventually.of_forall
  intro z
  simpa only [compactBallRaw, WithLp.toLp_ofLp, mem_closedBall, dist_zero_right] using z.property

theorem compactBallLaw_raw_tendsto {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ)) :
    Tendsto (fun k => ν (φ k)) atTop (𝓝 (compactBallRawLaw μ)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ μ hlim
    continuous_compactBallRaw
  simp_rw [compactBallLaw_raw_probability_pushforward _ (hball _)] at ht
  exact ht

theorem compactBallRawLaw_integral {d : ℕ} (μ : ProbabilityMeasure (CompactConeBall d))
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) =
      ∫ z, f (compactBallRaw z) ∂(μ : Measure (CompactConeBall d)) := by
  rw [compactBallRawLaw, ProbabilityMeasure.toMeasure_map,
    integral_map measurable_compactBallRaw.aemeasurable hf.aestronglyMeasurable]

theorem compactBallLaw_raw_integral_tendsto {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ))
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ν (φ k) : Measure (Fin d → ℝ))) atTop
      (𝓝 (∫ x, f x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)))) := by
  rw [compactBallRawLaw_integral μ f hf]
  exact compactBallLaw_integral_tendsto ν hball μ φ hlim f hf

theorem compactBallLaw_coordinate_integral_tendsto {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ)) (i : Fin d) :
    Tendsto (fun k => ∫ x, x i ∂(ν (φ k) : Measure (Fin d → ℝ))) atTop
      (𝓝 (∫ x, x i ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)))) :=
  compactBallLaw_raw_integral_tendsto ν hball μ φ hlim (fun x => x i) (continuous_apply i)

theorem compactBallLaw_negative_direction_integral_tendsto {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ)) (u : Fin d → ℝ) :
    Tendsto (fun k => negativeIntegral (ν (φ k) : Measure (Fin d → ℝ))
      (fun x => dotProduct u x)) atTop
      (𝓝 (negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
        (fun x => dotProduct u x))) := by
  have hf : Continuous (fun x : Fin d → ℝ => max (-dotProduct u x) 0) :=
    ((continuous_const.dotProduct continuous_id).neg).max continuous_const
  exact compactBallLaw_raw_integral_tendsto ν hball μ φ hlim _ hf

/-- Compactness of actual probability laws on the compact ball supplies a
limit and a strictly increasing subsequence, with exact raw-law convergence. -/
theorem compactBallLaw_exists_subsequence {d : ℕ}
    (ν : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hball : ∀ k, ∀ᵐ x ∂(ν k : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) :
    ∃ μ : ProbabilityMeasure (CompactConeBall d), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => compactBallLaw (ν (φ k))) atTop (𝓝 μ) ∧
      Tendsto (fun k => ν (φ k)) atTop (𝓝 (compactBallRawLaw μ)) ∧
      ∀ f : (Fin d → ℝ) → ℝ, Continuous f →
        Tendsto (fun k => ∫ x, f x ∂(ν (φ k) : Measure (Fin d → ℝ))) atTop
          (𝓝 (∫ x, f x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)))) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := compact_probability_tendsto_subseq (fun k => compactBallLaw (ν k))
  exact ⟨μ, φ, hφ, hlim, compactBallLaw_raw_tendsto ν hball μ φ hlim,
    fun f hf => compactBallLaw_raw_integral_tendsto ν hball μ φ hlim f hf⟩

/-- Package an actual probability measure without changing its underlying measure. -/
def rawProbabilityLaw {d : ℕ} (ν : Measure (Fin d → ℝ))
    (hprob : IsProbabilityMeasure ν) : ProbabilityMeasure (Fin d → ℝ) := ⟨ν, hprob⟩

/-- The input sequence consists of actual measures; probability and support
bounds construct a compact limit instead of assuming any limiting law. -/
theorem unit_ball_measure_exists_subsequence {d : ℕ}
    (ν : ℕ → Measure (Fin d → ℝ)) (hprob : ∀ k, IsProbabilityMeasure (ν k))
    (hball : ∀ k, ∀ᵐ x ∂ν k, ‖WithLp.toLp 2 x‖ ≤ 1) :
    ∃ μ : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => rawProbabilityLaw (ν (φ k)) (hprob (φ k)))
          atTop (𝓝 μ) ∧
        ∀ f : (Fin d → ℝ) → ℝ, Continuous f →
          Tendsto (fun k => ∫ x, f x ∂ν (φ k)) atTop (𝓝 (∫ x, f x ∂(μ : Measure (Fin d → ℝ)))) := by
  let νp : ℕ → ProbabilityMeasure (Fin d → ℝ) := fun k => rawProbabilityLaw (ν k) (hprob k)
  obtain ⟨μ, φ, hφ, _, hraw, hint⟩ := compactBallLaw_exists_subsequence νp hball
  exact ⟨compactBallRawLaw μ, compactBallRawLaw_ae_unit_ball μ, φ, hφ, hraw, hint⟩

section FiniteBody

variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

def finiteHalfspaceConeProbability (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) : ProbabilityMeasure (Fin d → ℝ) :=
  ⟨finiteHalfspaceConeLaw n h, finite_halfspace_cone_probability n h hn hh hinj hc⟩

def finiteHalfspaceCompactConeLaw (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) : ProbabilityMeasure (CompactConeBall d) :=
  compactBallLaw (finiteHalfspaceConeProbability n h hn hh hinj hc)

theorem finite_halfspace_compact_cone_raw_pushforward (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    (finiteHalfspaceCompactConeLaw n h hn hh hinj hc : Measure (CompactConeBall d)).map
      compactBallRaw = finiteHalfspaceConeLaw n h := by
  apply compactBallLaw_raw_pushforward
  exact finite_halfspace_cone_ae_unit_ball n h hn hb

end FiniteBody

section FiniteBodySequence

variable {ι : ℕ → Type*} [∀ k, Fintype (ι k)] {d : ℕ} [Nontrivial (Space d)]

/-- The facet index type may vary along the actual finite-body sequence.
Every probabilistic input is supplied by the proved geometric cone laws. -/
theorem finite_halfspace_cone_law_exists_subsequence
    (n : ∀ k, ι k → Space d) (h : ∀ k, ι k → ℝ)
    (hn : ∀ k i, ‖n k i‖ = 1) (hh : ∀ k i, 0 < h k i)
    (hinj : ∀ k, Function.Injective (n k))
    (hc : ∀ k, IsCompact (finiteHalfspaceSet (n k) (h k)))
    (hb : ∀ k, closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet (n k) (h k)) :
    ∃ μ : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => finiteHalfspaceConeProbability (n (φ k)) (h (φ k))
          (hn (φ k)) (hh (φ k)) (hinj (φ k)) (hc (φ k))) atTop (𝓝 μ) ∧
        ∀ f : (Fin d → ℝ) → ℝ, Continuous f →
          Tendsto (fun k => ∫ x, f x ∂finiteHalfspaceConeLaw (n (φ k)) (h (φ k)))
            atTop (𝓝 (∫ x, f x ∂(μ : Measure (Fin d → ℝ)))) := by
  exact unit_ball_measure_exists_subsequence
    (fun k => finiteHalfspaceConeLaw (n k) (h k))
    (fun k => finite_halfspace_cone_probability (n k) (h k) (hn k) (hh k) (hinj k) (hc k))
    (fun k => finite_halfspace_cone_ae_unit_ball (n k) (h k) (hn k) (hb k))

end FiniteBodySequence

end Entry005
