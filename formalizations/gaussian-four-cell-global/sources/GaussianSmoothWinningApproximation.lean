import GaussianBVApproximation
import GaussianNoTies
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Explicit smooth scalar approximants to actual strict winning cells.
The sequence stays in [0,1] and converges at every point, including ties.
Convergence of its gradient integrals is a separate remaining obligation. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

noncomputable def smoothWinningApprox (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) (x : Space d) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,Real.smoothTransition (((N : ℝ)+1)*
    (⟪v i-v j,x⟫-(b i-b j)))

lemma smoothWinningApprox_contDiff (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) : ContDiff ℝ ∞ (smoothWinningApprox v b i N) := by
  unfold smoothWinningApprox
  apply contDiff_prod
  intro j _
  apply Real.smoothTransition.contDiff.comp
  have hinner : ContDiff ℝ ∞ (fun x : Space d => ⟪v i-v j,x⟫) :=
    (innerSL ℝ (v i-v j)).contDiff
  fun_prop

lemma smoothWinningApprox_bounds (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (N : ℕ) (x : Space d) :
    0 ≤ smoothWinningApprox v b i N x ∧ smoothWinningApprox v b i N x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun j _ => Real.smoothTransition.nonneg _)
  · exact Finset.prod_le_one₀ (fun j _ => Real.smoothTransition.nonneg _)
      (fun j _ => Real.smoothTransition.le_one _)

lemma smoothTransition_scaled_eventually_one (g : ℝ) (hg : 0 < g) :
    (fun N : ℕ => Real.smoothTransition (((N : ℝ)+1)*g)) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/g)
  have hNg : 1 < (N : ℝ)*g := (div_lt_iff₀ hg).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  apply Real.smoothTransition.one_of_one_le
  have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem smoothWinningApprox_tendsto (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (x : Space d) :
    Tendsto (fun N => smoothWinningApprox v b i N x) atTop
      (𝓝 ((winningCell v b i).indicator (fun _ => (1 : ℝ)) x)) := by
  classical
  by_cases hx : x ∈ winningCell v b i
  · have hj (j : Fin k) (hj : j ∈ Finset.univ.erase i) :
        Tendsto (fun N : ℕ => Real.smoothTransition (((N : ℝ)+1)*
          (⟪v i-v j,x⟫-(b i-b j)))) atTop (𝓝 (1 : ℝ)) := by
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      have hwin := hx j hne
      have hg : 0 < ⟪v i-v j,x⟫-(b i-b j) := by rw [inner_sub_left]; linarith
      exact tendsto_const_nhds.congr' (smoothTransition_scaled_eventually_one _ hg).symm
    have he := tendsto_finsetProd (Finset.univ.erase i) hj
    simpa only [smoothWinningApprox,Finset.prod_const_one,Set.indicator_of_mem hx] using he
  · have hnot : ¬∀ j : Fin k,j ≠ i → ⟪v j,x⟫-b j < ⟪v i,x⟫-b i := hx
    push Not at hnot
    obtain ⟨j,hji,hj⟩ := hnot
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩
    have hg : ⟪v i-v j,x⟫-(b i-b j) ≤ 0 := by rw [inner_sub_left]; linarith
    have hz (N : ℕ) : smoothWinningApprox v b i N x=0 := by
      apply Finset.prod_eq_zero hmem
      apply Real.smoothTransition.zero_of_nonpos
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hg
    simpa only [hz,Set.indicator_of_notMem hx] using (tendsto_const_nhds (x := (0 : ℝ)))

end GaussianMeasureBridge
