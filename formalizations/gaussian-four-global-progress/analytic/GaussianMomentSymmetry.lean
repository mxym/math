import GaussianWinningContinuity
import GaussianRegularValue

/-! Equivariance of actual winning-cell moments. This proves symmetry of
integrals, rather than postulating symmetry of their values. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma winningCell_reindex (v : Fin k → Space d) (b : Fin k → ℝ)
    (e : Equiv.Perm (Fin k)) (i : Fin k) :
    winningCell (v ∘ e) (b ∘ e) i = winningCell v b (e i) := by
  ext x
  constructor
  · intro h j hj
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      h (e.symm j) (fun he => hj (by simpa using congrArg e he))
  · intro h j hj
    exact h (e j) (fun he => hj (e.injective he))

lemma rawWinningMoment_reindex (v : Fin k → Space d) (b : Fin k → ℝ)
    (e : Equiv.Perm (Fin k)) (i : Fin k) :
    rawWinningMoment (v ∘ e) (b ∘ e) i = rawWinningMoment v b (e i) := by
  unfold rawWinningMoment
  rw [winningCell_reindex]

lemma winningCell_isometry (v : Fin k → Space d) (b : Fin k → ℝ)
    (T : Space d ≃ₗᵢ[ℝ] Space d) (i : Fin k) (x : Space d) :
    T x ∈ winningCell (fun j => T (v j)) b i ↔ x ∈ winningCell v b i := by
  simp only [winningCell, mem_setOf_eq, T.inner_map_map]

theorem rawWinningMoment_isometry (v : Fin k → Space d) (b : Fin k → ℝ)
    (T : Space d ≃ₗᵢ[ℝ] Space d) (i : Fin k) :
    rawWinningMoment (fun j => T (v j)) b i = T (rawWinningMoment v b i) := by
  have hm : (gaussian d).map T = gaussian d := stdGaussian_map T
  have hmeas : AEStronglyMeasurable
      ((winningCell (fun j => T (v j)) b i).indicator (fun x : Space d => x))
      ((gaussian d).map T) :=
    (stronglyMeasurable_id.indicator (measurableSet_winningCell _ _ _)).aestronglyMeasurable
  unfold rawWinningMoment
  conv_lhs => rw [← hm]
  rw [integral_map T.continuous.measurable.aemeasurable hmeas]
  have hc : (∫ x, T ((winningCell v b i).indicator (fun x => x) x) ∂gaussian d) =
      T (∫ x, (winningCell v b i).indicator (fun x => x) x ∂gaussian d) :=
    T.toLinearIsometry.integral_comp_comm _
  rw [← hc]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ winningCell v b i
    · have ht := (winningCell_isometry v b T i x).mpr hx
      simp [hx,ht]
    · have ht := not_congr (winningCell_isometry v b T i x)
      simp [hx,ht.mpr hx]

noncomputable def standardMoment (k : ℕ) [NeZero k] (i : Fin k) : Space k :=
  rawWinningMoment (standardRows k) 0 i

lemma canonicalPrices_standard : canonicalPrices (standardRows k) = 0 :=
  (canonicalPrices_unique (standardRows k) standardRows_injective 0
    standard_zero_price_minimizer rfl).symm

lemma standardMoment_eq_balanced (i : Fin k) :
    standardMoment k i = balancedMoment (standardRows k) i := by
  simp [standardMoment, balancedMoment, canonicalPrices_standard]

lemma standardMoment_sum : ∑ i : Fin k, standardMoment k i = 0 := by
  simp_rw [standardMoment, rawWinningMoment_eq _ _ standardRows_injective]
  exact (winningPartition (standardRows k) 0 standardRows_injective).sum_moment

lemma standardMoment_trace : (∑ i : Fin k, standardMoment k i i) = expectedGaussianMaximum k := by
  have h := balancedMoment_value (standardRows k) standardRows_injective
  rw [equalMassValue_standardRows] at h
  simp_rw [← standardMoment_eq_balanced] at h
  simpa [standardRows, PiLp.inner_apply] using h

/-- Simultaneous permutation of the label and ambient coordinate leaves each
entry of the moment matrix unchanged. -/
theorem standardMoment_permutation (e : Equiv.Perm (Fin k)) (i j : Fin k) :
    standardMoment k (e i) (e j) = standardMoment k i j := by
  let T : Space k ≃ₗᵢ[ℝ] Space k := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hT : (fun i => T (standardRows k i)) = standardRows k ∘ e := by
    funext i
    simp [T, standardRows, EuclideanSpace.basisFun_apply,
      EuclideanSpace.piLpCongrLeft_single]
  have h := rawWinningMoment_isometry (standardRows k) 0 T i
  rw [hT] at h
  have hr : rawWinningMoment (standardRows k ∘ e) 0 i = standardMoment k (e i) := by
    convert rawWinningMoment_reindex (standardRows k) 0 e i using 1 <;> rfl
  rw [hr] at h
  have hh := congrArg (fun x : Space k => x (e j)) h
  simpa [T, standardMoment, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hh

lemma standardMoment_diagonal (i j : Fin k) :
    standardMoment k i i = standardMoment k j j := by
  simpa using (standardMoment_permutation (Equiv.swap i j) i i).symm

lemma standardMoment_offdiagonal_row (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) :
    standardMoment k i j = standardMoment k i l := by
  have h := standardMoment_permutation (Equiv.swap j l) i j
  simpa [Equiv.swap_apply_of_ne_of_ne hij hil] using h.symm

lemma standardMoment_symmetric (i j : Fin k) :
    standardMoment k i j = standardMoment k j i := by
  simpa using (standardMoment_permutation (Equiv.swap i j) i j).symm

end GaussianMeasureBridge
