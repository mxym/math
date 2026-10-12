import GaussianFour.PairMassDerivative

/-! Coordinate-independent Gaussian facet coefficients from actual mass
variation. No full-rank or simplicial assumption is imposed. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

noncomputable def intrinsicPairWeight (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) : ℝ :=
  if i = j then 0 else deriv (fun t => winningMass v (coordinateShift b j t) i) 0

lemma intrinsicPairWeight_diagonal (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i : Fin k) :
    intrinsicPairWeight v b i i = 0 := by simp [intrinsicPairWeight]

variable [NeZero k]

theorem intrinsicPairWeight_eq_positive_chart
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l))
    (i j : Fin k) (hij : i ≠ j) (T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1))
    (hp : 0 < pairDen (fun l => T (v l)) i j) :
    intrinsicPairWeight v b i j = pairChartWeight (fun l => T (v l)) b i j := by
  have hm (l : Fin k) : 0 < (gaussian (d+1)).real (winningCell (fun l => T (v l)) b l) := by
    change 0 < winningMass (fun l => T (v l)) b l
    rw [winningMass_isometry]
    exact hmass l
  have h : HasDerivAt (fun t => winningMass v (coordinateShift b j t) i)
      (pairChartWeight (fun l => T (v l)) b i j) 0 := by
    simpa only [winningMass_isometry] using
      positive_pairChart_mass_derivative (fun l => T (v l)) b i j hij hp hm
  simp only [intrinsicPairWeight, hij, ↓reduceIte, h.deriv]

/-- Actual price differentiation holds at singular positive-mass diagrams. -/
theorem actual_competitor_price_derivative
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l))
    (i j : Fin k) (hij : i ≠ j) :
    HasDerivAt (fun t => winningMass v (coordinateShift b j t) i)
      (intrinsicPairWeight v b i j) 0 := by
  obtain ⟨T,hp,_⟩ := exists_continuous_pair_chart_of_positive_masses v b hmass i j hij
  rw [intrinsicPairWeight_eq_positive_chart v b hmass i j hij T hp]
  have hm (l : Fin k) : 0 < (gaussian (d+1)).real (winningCell (fun l => T (v l)) b l) := by
    change 0 < winningMass (fun l => T (v l)) b l
    rw [winningMass_isometry]
    exact hmass l
  simpa only [winningMass_isometry] using
    positive_pairChart_mass_derivative (fun l => T (v l)) b i j hij hp hm

/-- Different positive orthogonal charts give exactly equal Gaussian integrals. -/
theorem positive_pair_charts_compatible
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l))
    (i j : Fin k) (hij : i ≠ j) (T U : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1))
    (hT : 0 < pairDen (fun l => T (v l)) i j)
    (hU : 0 < pairDen (fun l => U (v l)) i j) :
    pairChartWeight (fun l => T (v l)) b i j =
      pairChartWeight (fun l => U (v l)) b i j :=
  (intrinsicPairWeight_eq_positive_chart v b hmass i j hij T hT).symm.trans
    (intrinsicPairWeight_eq_positive_chart v b hmass i j hij U hU)

theorem intrinsicPairWeight_nonneg
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l)) (i j : Fin k) :
    0 ≤ intrinsicPairWeight v b i j := by
  by_cases hij : i = j
  · subst j; rw [intrinsicPairWeight_diagonal]
  · obtain ⟨T,hp,_⟩ := exists_continuous_pair_chart_of_positive_masses v b hmass i j hij
    rw [intrinsicPairWeight_eq_positive_chart v b hmass i j hij T hp]
    unfold pairChartWeight pairChartDensity affineDensityIntegral
    exact div_nonneg (integral_nonneg fun y => (standardDensity_pos _).le) (abs_nonneg _)

end GaussianFour
