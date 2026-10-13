import APPTReview.LacunaryProbability
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Portmanteau

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Filter Set
namespace APPTReview

/-- A real-valued, quantitative consequence of the closed-set Portmanteau bound. -/
theorem probability_closed_eventually_lt {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] [OpensMeasurableSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (F : Set X) (hF : IsClosed F)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, (μs n).toMeasure.real F < μ.toMeasure.real F+ε := by
  have hu := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have hp : 0 ≤ μ.toMeasure.real F+ε := by linarith [measureReal_nonneg (μ:=μ.toMeasure) (s:=F)]
  have hr : μ.toMeasure F < ENNReal.ofReal (μ.toMeasure.real F+ε) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hp]
    exact lt_add_of_pos_right _ hε
  have he := Filter.eventually_lt_of_limsup_lt (hu.trans_lt hr)
  filter_upwards [he] with n hn
  have h := (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).mpr hn
  rw [ENNReal.toReal_ofReal hp] at h
  exact h

/-- A closed band, with its width allowed to vary along the sequence. -/
def scaleBand (d t : ℝ) : Set (ℝ≥0 × ℝ≥0) :=
  {p | |(p.1:ℝ)+(p.2:ℝ)-d|≤t}

def markedScaleBand (d : ℝ) : Set ((ℝ≥0 × ℝ≥0) × ℝ) :=
  {p | |(p.1.1:ℝ)+(p.1.2:ℝ)-d|≤p.2}

theorem isClosed_markedScaleBand (d : ℝ) : IsClosed (markedScaleBand d) :=
  isClosed_le (by fun_prop) (by fun_prop)

theorem scaleBand_zero (d : ℝ) : scaleBand d 0=scaleLine d := by
  ext p
  simp [scaleBand,scaleLine,abs_nonpos_iff,sub_eq_zero]

/-- Encode varying widths as Dirac marks, so one fixed closed set suffices. -/
theorem markedScaleBand_mass (μ : ProbabilityMeasure ℝ≥0) (d t : ℝ) :
    ((μ.prod μ).prod (diracProba t)).toMeasure.real (markedScaleBand d)=
      (μ.prod μ).toMeasure.real (scaleBand d t) := by
  change ((μ.toMeasure.prod μ.toMeasure).prod (Measure.dirac t)).real (markedScaleBand d)=_
  rw [Measure.prod_dirac]
  change (Measure.map (fun p : ℝ≥0 × ℝ≥0 => (p,t)) (μ.toMeasure.prod μ.toMeasure)).real
    (markedScaleBand d)=_
  rw [Measure.real,Measure.map_apply (by fun_prop) (isClosed_markedScaleBand d).measurableSet]
  rfl

/-- Moving strips collapse to the exact line in the weak upper bound.
A shared weak limit and the actual vanishing width are proved sufficient; no
closed-set bound for a moving set is silently assumed. -/
theorem moving_scaleBand_eventually_lt (μs : ℕ → ProbabilityMeasure ℝ≥0)
    (μ : ProbabilityMeasure ℝ≥0) (ts : ℕ → ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (ht : Tendsto ts atTop (𝓝 0))
    (d ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, (μs n |>.prod (μs n)).toMeasure.real (scaleBand d (ts n)) <
      (μ.prod μ).toMeasure.real (scaleLine d)+ε := by
  have hprod : Tendsto (fun n => (μs n).prod (μs n)) atTop (𝓝 (μ.prod μ)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hμ.prodMk_nhds hμ)
  have hd : Tendsto (fun n => diracProba (ts n)) atTop (𝓝 (diracProba (0:ℝ))) :=
    continuous_diracProba.continuousAt.tendsto.comp ht
  have hall : Tendsto (fun n => ((μs n).prod (μs n)).prod (diracProba (ts n))) atTop
      (𝓝 ((μ.prod μ).prod (diracProba (0:ℝ)))) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hprod.prodMk_nhds hd)
  have h := probability_closed_eventually_lt _ _ hall (markedScaleBand d)
    (isClosed_markedScaleBand d) ε hε
  simpa only [markedScaleBand_mass,scaleBand_zero] using h

end APPTReview
