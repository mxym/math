import GaussianWinningPartition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Boundary continuity of actual Gaussian winning-cell masses and moments.
The limiting scores must be distinct, but no full-rank condition is imposed.
This module does not assert continuity of Gaussian facet areas. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace GaussianFourGlobal
open GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

/-- A strict winning label persists at any fixed point under converging scores
and prices. This assertion is pointwise and does not use a rank hypothesis. -/
theorem eventually_winningCell
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (i : Fin k) (x : Space d) (hx : x ∈ winningCell v b i) :
    ∀ᶠ n in atTop, x ∈ winningCell (vSeq n) (bSeq n) i := by
  have hs (j : Fin k) :
      Tendsto (fun n => ⟪vSeq n j, x⟫ - bSeq n j) atTop (𝓝 (⟪v j, x⟫ - b j)) :=
    ((hv j).inner tendsto_const_nhds).sub (hb j)
  change ∀ᶠ n in atTop, ∀ j, j ≠ i → _
  apply Filter.eventually_all.mpr
  intro j
  by_cases hji : j = i
  · exact Filter.Eventually.of_forall fun _ h => False.elim (h hji)
  · have hh := ((hs i).sub (hs j)).eventually
      (Ioi_mem_nhds (sub_pos.mpr (hx j hji)))
    filter_upwards [hh] with n hn
    intro _
    exact sub_pos.mp hn

/-- All winning memberships eventually agree with their limiting memberships
at a point having a strict limiting winner. -/
theorem eventually_winning_memberships
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (x : Space d) (r : Fin k) (hr : x ∈ winningCell v b r) :
    ∀ᶠ n in atTop, ∀ i,
      (x ∈ winningCell (vSeq n) (bSeq n) i ↔ x ∈ winningCell v b i) := by
  filter_upwards [eventually_winningCell vSeq bSeq v b hv hb r x hr] with n hnr i
  by_cases hir : i = r
  · subst i
    exact iff_of_true hnr hr
  · have hi0 : x ∉ winningCell v b i := by
      intro hi
      exact (not_lt_of_gt (hr i hir)) (hi r (Ne.symm hir))
    have hin : x ∉ winningCell (vSeq n) (bSeq n) i := by
      intro hi
      exact (not_lt_of_gt (hnr i hir)) (hi r (Ne.symm hir))
    exact iff_of_false hin hi0

/-- Pointwise stabilization away from the Gaussian-null limiting tie set.
The integrand can be scalar- or vector-valued and need not be continuous. -/
theorem ae_tendsto_winning_indicator {E : Type*} [NormedAddCommGroup E]
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hv0 : Function.Injective v) (i : Fin k) (f : Space d → E) :
    ∀ᵐ x ∂gaussian d, Tendsto
      (fun n => (winningCell (vSeq n) (bSeq n) i).indicator f x) atTop
      (𝓝 ((winningCell v b i).indicator f x)) := by
  filter_upwards [ae_unique_winner v b hv0] with x hx
  obtain ⟨r, hr⟩ := hx
  have heq : (fun n => (winningCell (vSeq n) (bSeq n) i).indicator f x) =ᶠ[atTop]
      (fun _ => (winningCell v b i).indicator f x) := by
    filter_upwards [eventually_winning_memberships vSeq bSeq v b hv hb x r hr] with n hn
    by_cases hi : x ∈ winningCell v b i
    · simp [hi, (hn i).mpr hi]
    · have hin : x ∉ winningCell (vSeq n) (bSeq n) i := fun h => hi ((hn i).mp h)
      simp [hi, hin]
  exact tendsto_const_nhds.congr' heq.symm

/-- Convergence of actual Bochner integrals over the moving winning cells.
Every integrable function is allowed, not just the first moment. -/
theorem tendsto_winning_setIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hv0 : Function.Injective v) (i : Fin k) (f : Space d → E)
    (hf : Integrable f (gaussian d)) :
    Tendsto (fun n => ∫ x in winningCell (vSeq n) (bSeq n) i, f x ∂gaussian d) atTop
      (𝓝 (∫ x in winningCell v b i, f x ∂gaussian d)) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator (measurableSet_winningCell (vSeq n) (bSeq n) i))
    hf.norm
    (fun n => ae_of_all _ fun x => by
      by_cases hx : x ∈ winningCell (vSeq n) (bSeq n) i <;> simp [hx])
    (ae_tendsto_winning_indicator vSeq bSeq v b hv hb hv0 i f)
  simp only [integral_indicator (measurableSet_winningCell _ _ _)] at h
  exact h

/-- Winning-cell probabilities converge even at rank-one and rank-two limits,
provided the limiting inducing vectors are still distinct. -/
theorem tendsto_winning_mass
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hv0 : Function.Injective v) (i : Fin k) :
    Tendsto (fun n => (gaussian d).real (winningCell (vSeq n) (bSeq n) i)) atTop
      (𝓝 ((gaussian d).real (winningCell v b i))) := by
  have h := tendsto_winning_setIntegral vSeq bSeq v b hv hb hv0 i (fun _ => (1 : ℝ))
    (integrable_const 1)
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using h

lemma winningPartition_moment_eq_setIntegral
    (v : Fin k → Space d) (b : Fin k → ℝ) (hv : Function.Injective v) (i : Fin k) :
    (winningPartition v b hv).moment i = ∫ x in winningCell v b i, x ∂gaussian d := by
  rw [← integral_indicator (measurableSet_winningCell v b i)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ winningCell v b i <;> simp [winningPartition, hx]

/-- Actual first moments converge through a possibly singular score limit. -/
theorem tendsto_winning_moment
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hvn : ∀ n, Function.Injective (vSeq n)) (hv0 : Function.Injective v) (i : Fin k) :
    Tendsto (fun n => (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i) atTop
      (𝓝 ((winningPartition v b hv0).moment i)) := by
  simp only [winningPartition_moment_eq_setIntegral]
  exact tendsto_winning_setIntegral vSeq bSeq v b hv hb hv0 i (fun x => x)
    IsGaussian.integrable_id

/-- Prescribed winning masses survive separated score/price limits. -/
theorem balanced_winning_limit
    (vSeq : ℕ → Fin k → Space d) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space d) (b : Fin k → ℝ) (p : Fin k → ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hv0 : Function.Injective v)
    (hbalance : ∀ n i, (gaussian d).real (winningCell (vSeq n) (bSeq n) i) = p i) :
    ∀ i, (gaussian d).real (winningCell v b i) = p i := by
  intro i
  have h := tendsto_winning_mass vSeq bSeq v b hv hb hv0 i
  simp only [hbalance] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end GaussianFourGlobal
