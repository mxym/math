import GaussianPriceContinuity

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma eventually_winning_parameters (v : Fin k → Space d) (b : Fin k → ℝ)
    (x : Space d) (r : Fin k) (hr : x ∈ winningCell v b r) :
    ∀ᶠ z : (Fin k → Space d) × (Fin k → ℝ) in 𝓝 (v,b), x ∈ winningCell z.1 z.2 r := by
  apply eventually_all.mpr
  intro j
  by_cases hj : j = r
  · exact Eventually.of_forall fun _ hh => False.elim (hh hj)
  · have hjc : ContinuousAt (fun z : (Fin k → Space d) × (Fin k → ℝ) =>
        ⟪z.1 j, x⟫ - z.2 j) (v,b) := by fun_prop
    have hrc : ContinuousAt (fun z : (Fin k → Space d) × (Fin k → ℝ) =>
        ⟪z.1 r, x⟫ - z.2 r) (v,b) := by fun_prop
    exact (hjc.eventually_lt hrc (hr j hj)).mono fun _ ht _ => ht

noncomputable def rawWinningMoment (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) : Space d :=
  ∫ x, (winningCell v b i).indicator (fun x => x) x ∂gaussian d

lemma rawWinningMoment_eq (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    rawWinningMoment v b i = (winningPartition v b hv).moment i := by
  unfold rawWinningMoment FractionalPartition.moment winningPartition
  congr 1
  funext x
  by_cases hx : x ∈ winningCell v b i <;> simp [hx]

/-- Winning-cell Bochner moments are continuous at distinct score families.
Null ties and dominated convergence prove the result directly. -/
theorem continuousAt_rawWinningMoment (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    ContinuousAt (fun z : (Fin k → Space d) × (Fin k → ℝ) => rawWinningMoment z.1 z.2 i) (v,b) := by
  apply continuousAt_of_dominated (bound := fun x : Space d => ‖x‖)
  · exact Eventually.of_forall fun z =>
      (stronglyMeasurable_id.indicator (measurableSet_winningCell z.1 z.2 i)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => ae_of_all _ fun x => by
      by_cases hx : x ∈ winningCell z.1 z.2 i <;> simp [hx]
  · exact (IsGaussian.integrable_id (μ := gaussian d)).norm
  · filter_upwards [ae_unique_winner v b hv] with x hx
    obtain ⟨r, hr⟩ := hx
    have hevent := eventually_winning_parameters v b x r hr
    have heq : (fun z : (Fin k → Space d) × (Fin k → ℝ) =>
        (winningCell z.1 z.2 i).indicator (fun x => x) x) =ᶠ[𝓝 (v,b)]
        (fun _ => (winningCell v b i).indicator (fun x => x) x) := by
      filter_upwards [hevent] with z hz
      by_cases hir : i = r
      · subst i; simp [hz,hr]
      · have hi : x ∉ winningCell v b i := fun hi =>
          Set.disjoint_left.mp (winningCell_disjoint v b i r hir) hi hr
        have hiz : x ∉ winningCell z.1 z.2 i := fun hi =>
          Set.disjoint_left.mp (winningCell_disjoint z.1 z.2 i r hir) hi hz
        simp [hi,hiz]
    exact continuousAt_const.congr_of_eventuallyEq heq

noncomputable def balancedMoment (v : Fin k → Space d) (i : Fin k) : Space d :=
  rawWinningMoment v (canonicalPrices v) i

theorem continuousAt_balancedMoment (v : Fin k → Space d) (hv : Function.Injective v)
    (i : Fin k) : ContinuousAt (fun w => balancedMoment w i) v := by
  have hp : ContinuousAt (fun w : Fin k → Space d => (w, canonicalPrices w)) v :=
    continuousAt_id.prodMk (continuousAt_canonicalPrices v hv)
  have hf := continuousAt_rawWinningMoment v (canonicalPrices v) hv i
  change Tendsto (fun w : Fin k → Space d => rawWinningMoment w (canonicalPrices w) i)
    (𝓝 v) (𝓝 (rawWinningMoment v (canonicalPrices v) i))
  exact Filter.Tendsto.comp
    (f := fun w : Fin k → Space d => (w, canonicalPrices w))
    (g := fun z : (Fin k → Space d) × (Fin k → ℝ) => rawWinningMoment z.1 z.2 i) hf hp

lemma balancedMoment_value (v : Fin k → Space d) (hv : Function.Injective v) :
    (∑ i, ⟪v i, balancedMoment v i⟫) = equalMassValue v := by
  simp_rw [balancedMoment, rawWinningMoment_eq v (canonicalPrices v) hv]
  rw [winningPartition_dual_attainment]
  simp_rw [winningPartition_mass, canonicalPrices_balanced v hv]
  exact canonicalPrices_value v

lemma balancedMoment_support (v : Fin k → Space d) (hv : Function.Injective v)
    (w : Fin k → Space d) : (∑ i, ⟪w i, balancedMoment v i⟫) ≤ equalMassValue w := by
  simp_rw [balancedMoment, rawWinningMoment_eq v (canonicalPrices v) hv]
  exact partitionValue_le_balancedValue w (uniformMass k) uniformMass_pos sum_uniformMass
    (winningPartition v (canonicalPrices v) hv) (fun i => by
      rw [winningPartition_mass]; exact canonicalPrices_balanced v hv i)

end GaussianMeasureBridge
