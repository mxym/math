import GaussianBVIndicatorContinuity

/-! The total variational Gaussian perimeter of a finite cluster is closed
under cellwise indicator-L1 limits and a uniform perimeter upper bound. This
is proved using independent genuine test fields for each label. It supplies
lower semicontinuity, not the remaining compactness or regularity theorem. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

noncomputable def zeroGaussianTestField (d : ℕ) : GaussianTestField d :=
  { toFun := fun _ => 0
    smooth := contDiff_const
    compact := by simp [HasCompactSupport]
    norm_le := fun _ => by simp }

lemma sum_gaussianBVPerimeter_eq_iSup_tests (S : Fin k → Set (Space d)) :
    (∑ i,gaussianBVPerimeter (S i)) =
      ⨆ X : Fin k → GaussianTestField d,
        ∑ i,ENNReal.ofReal (∫ x in S i,gaussianDivergence (X i) x ∂gaussian d) := by
  classical
  let : Nonempty (GaussianTestField d) := ⟨zeroGaussianTestField d⟩
  let f : Fin k → (Fin k → GaussianTestField d) → ℝ≥0∞ :=
    fun i X => ENNReal.ofReal (∫ x in S i,gaussianDivergence (X i) x ∂gaussian d)
  have hs (i : Fin k) : (⨆ X : Fin k → GaussianTestField d,f i X) = gaussianBVPerimeter (S i) := by
    apply le_antisymm
    · apply iSup_le
      intro X
      exact gaussianBVPerimeter_ge_test (S i) (X i)
    · apply iSup_le
      intro X
      exact le_iSup_of_le (fun _ => X) le_rfl
  have hdir (X Y : Fin k → GaussianTestField d) :
      ∃ Z : Fin k → GaussianTestField d,∀ i,f i X ≤ f i Z ∧ f i Y ≤ f i Z := by
    refine ⟨fun i => if f i X ≤ f i Y then Y i else X i,fun i => ?_⟩
    by_cases hi : f i X ≤ f i Y
    · dsimp only [f] at hi ⊢
      rw [ite_eq_left hi]
      exact ⟨hi,le_rfl⟩
    · dsimp only [f] at hi ⊢
      rw [ite_eq_right hi]
      exact ⟨le_rfl,(le_of_not_ge hi)⟩
  simpa only [hs] using ENNReal.finsetSum_iSup (s := Finset.univ) hdir

theorem gaussian_BV_sum_upper_closed_under_indicatorL1
    (S : Fin k → Set (Space d)) (T : ℕ → Fin k → Set (Space d)) (P : ℝ≥0∞)
    (hS : ∀ i,MeasurableSet (S i)) (hT : ∀ n i,MeasurableSet (T n i))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance (T n i) (S i)) atTop (𝓝 0))
    (hupper : ∀ n,(∑ i,gaussianBVPerimeter (T n i)) ≤ P) :
    (∑ i,gaussianBVPerimeter (S i)) ≤ P := by
  rw [sum_gaussianBVPerimeter_eq_iSup_tests]
  apply iSup_le
  intro X
  have ht := tendsto_finsetSum Finset.univ (fun i _ => ENNReal.tendsto_ofReal
    (gaussian_test_integral_tendsto_of_indicatorL1 (S i) (fun n => T n i)
      (hS i) (fun n => hT n i) (hdist i) (X i)))
  apply le_of_tendsto_of_tendsto ht tendsto_const_nhds
  exact Eventually.of_forall fun n =>
    (Finset.sum_le_sum (fun i _ => gaussianBVPerimeter_ge_test (T n i) (X i))).trans (hupper n)

theorem gaussian_total_BV_upper_closed_under_indicatorL1
    (S : Fin k → Set (Space d)) (T : ℕ → Fin k → Set (Space d)) (P : ℝ≥0∞)
    (hS : ∀ i,MeasurableSet (S i)) (hT : ∀ n i,MeasurableSet (T n i))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance (T n i) (S i)) atTop (𝓝 0))
    (hupper : ∀ n,(∑ i,gaussianBVPerimeter (T n i))/2 ≤ P) :
    (∑ i,gaussianBVPerimeter (S i))/2 ≤ P := by
  have h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := by norm_num
  apply (ENNReal.div_le_iff h2z h2t).mpr
  apply gaussian_BV_sum_upper_closed_under_indicatorL1 S T (P*2) hS hT hdist
  exact fun n => (ENNReal.div_le_iff h2z h2t).mp (hupper n)

end GaussianMeasureBridge
