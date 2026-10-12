import GaussianSimplicialMassFlux

/-! The actual Gaussian mass derivative when every defining hyperplane is
shifted inward at unit normal speed. This connects the constructed density
weights to a genuine boundary variation. -/
open MeasureTheory ProbabilityTheory Set Module Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def simplicialInset (v : Fin (d+2) → Space (d+1))
    (b : Fin (d+2) → ℝ) (t : ℝ) : Set (Space (d+1)) :=
  {x | ∀ i : Fin (d+1), t * ‖v 0 - v i.succ‖ <
    ⟪v 0 - v i.succ,x⟫ - (b 0 - b i.succ)}

noncomputable def inwardPriceVelocity (v : Fin (d+2) → Space (d+1)) : Fin (d+2) → ℝ :=
  Fin.cons 0 (fun i => -‖v 0 - v i.succ‖)

lemma simplicialInset_eq_winningCell (v : Fin (d+2) → Space (d+1))
    (b : Fin (d+2) → ℝ) (t : ℝ) :
    simplicialInset v b t = winningCell v (affinePrices b (inwardPriceVelocity v) t) 0 := by
  ext x
  constructor
  · intro hx j hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ i =>
      have hh := hx i
      simp only [inwardPriceVelocity,Fin.cons_zero,Fin.cons_succ,affinePrices,
        inner_sub_left,mul_zero,add_zero] at *
      linarith
  · intro hx i
    have hh := hx i.succ (Fin.succ_ne_zero i)
    simp only [inwardPriceVelocity,Fin.cons_zero,Fin.cons_succ,affinePrices,
      inner_sub_left,mul_zero,add_zero] at *
    linarith

theorem actual_inward_boundary_mass_derivative
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (w : Fin (d+1) → ℝ)
    (hf : rawWinningMoment v b 0 = ∑ i, w i • (v 0 - v i.succ)) :
    HasDerivAt (fun t => (gaussian (d+1)).real (simplicialInset v b t))
      (-(∑ i, w i * ‖v 0 - v i.succ‖)) 0 := by
  have hh := simplicial_mass_flux_base_derivative v b (inwardPriceVelocity v) B hB w hf
  simpa only [simplicialInset_eq_winningCell,winningMass,inwardPriceVelocity,Fin.cons_zero,
    Fin.cons_succ,sub_zero,mul_neg,Finset.sum_neg_distrib] using hh

end GaussianMeasureBridge
