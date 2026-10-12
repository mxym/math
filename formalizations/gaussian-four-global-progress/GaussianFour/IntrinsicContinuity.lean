import GaussianFour.IntrinsicWeights
import GaussianFour.WinningLimits
import Mathlib.Topology.Sequences

/-! Intrinsic coefficients and actual masses through singular limits. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

theorem continuousAt_winningMass
    (v : Fin k → Space d) (b : Fin k → ℝ) (hv : Function.Injective v) (i : Fin k) :
    ContinuousAt (fun z : (Fin k → Space d) × (Fin k → ℝ) => winningMass z.1 z.2 i) (v,b) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro z hz
  exact GaussianFourGlobal.tendsto_winning_mass (fun n => (z n).1) (fun n => (z n).2)
    v b (fun l => (((continuous_apply l).comp continuous_fst).tendsto (v,b)).comp hz)
    (fun l => (((continuous_apply l).comp continuous_snd).tendsto (v,b)).comp hz) hv i

lemma eventually_positive_winning_masses
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian d).real (winningCell v b l)) :
    ∀ᶠ z : (Fin k → Space d) × (Fin k → ℝ) in 𝓝 (v,b),
      ∀ l, 0 < (gaussian d).real (winningCell z.1 z.2 l) := by
  have hv := injective_scores_of_positive_winning_masses v b hmass
  apply eventually_all.mpr
  intro l
  exact continuousAt_const.eventually_lt (continuousAt_winningMass v b hv l) (hmass l)

/-- Joint continuity of coordinate-independent coefficients at every
positive-mass diagram, including rank-deficient configurations. -/
theorem continuousAt_intrinsicPairWeight
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l)) (i j : Fin k) :
    ContinuousAt (fun z : ChartParameters d k => intrinsicPairWeight z.1 z.2 i j) (v,b) := by
  by_cases hij : i = j
  · subst j
    simpa only [intrinsicPairWeight_diagonal] using
      (continuousAt_const : ContinuousAt (fun _ : ChartParameters d k => (0 : ℝ)) (v,b))
  · obtain ⟨T,hp,hc⟩ := exists_continuous_pair_chart_of_positive_masses v b hmass i j hij
    have hd : ContinuousAt (fun z : ChartParameters d k => pairDen (fun l => T (z.1 l)) i j)
        (v,b) := by unfold pairDen; fun_prop
    have he : ∀ᶠ z : ChartParameters d k in 𝓝 (v,b),
        intrinsicPairWeight z.1 z.2 i j = pairChartWeight (fun l => T (z.1 l)) z.2 i j := by
      filter_upwards [eventually_positive_winning_masses v b hmass,
        continuousAt_const.eventually_lt hd hp] with z hz hpos
      exact intrinsicPairWeight_eq_positive_chart z.1 z.2 hz i j hij T hpos
    exact hc.congr_of_eventuallyEq he

/-- Prescribed positive masses and every intrinsic coefficient survive the
same separated score/price limit. No limiting mass is postulated. -/
theorem balanced_intrinsic_weights_limit
    (vSeq : ℕ → Fin k → Space (d+1)) (bSeq : ℕ → Fin k → ℝ)
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i)
    (hv : Tendsto vSeq atTop (𝓝 v)) (hb : Tendsto bSeq atTop (𝓝 b))
    (hv0 : Function.Injective v)
    (hbalance : ∀ n i, (gaussian (d+1)).real (winningCell (vSeq n) (bSeq n) i) = p i) :
    (∀ i, (gaussian (d+1)).real (winningCell v b i) = p i) ∧
      ∀ i j, Tendsto (fun n => intrinsicPairWeight (vSeq n) (bSeq n) i j) atTop
        (𝓝 (intrinsicPairWeight v b i j)) := by
  have hz : Tendsto (fun n => (vSeq n,bSeq n)) atTop (𝓝 (v,b)) := hv.prodMk_nhds hb
  have hm : ∀ i, (gaussian (d+1)).real (winningCell v b i) = p i := by
    intro i
    have h : Tendsto (fun n => winningMass (vSeq n) (bSeq n) i) atTop
        (𝓝 (winningMass v b i)) :=
      Filter.Tendsto.comp (g := fun z : ChartParameters d k => winningMass z.1 z.2 i)
        (f := fun n : ℕ => (vSeq n,bSeq n))
        (continuousAt_winningMass (d := d+1) v b hv0 i).tendsto hz
    change Tendsto (fun n => (gaussian (d+1)).real (winningCell (vSeq n) (bSeq n) i))
      atTop (𝓝 ((gaussian (d+1)).real (winningCell v b i))) at h
    simp only [hbalance] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨hm, ?_⟩
  intro i j
  have hpos (l : Fin k) : 0 < (gaussian (d+1)).real (winningCell v b l) := by
    rw [hm l]; exact hp l
  exact Filter.Tendsto.comp
    (g := fun z : ChartParameters d k => intrinsicPairWeight z.1 z.2 i j)
    (f := fun n : ℕ => (vSeq n,bSeq n))
    (continuousAt_intrinsicPairWeight v b hpos i j).tendsto hz

end GaussianFour
