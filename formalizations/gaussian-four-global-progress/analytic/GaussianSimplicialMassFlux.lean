import GaussianWinningMassDerivative
import GaussianSymmetricFlux

/-! The original cell's mass derivative and moment flux have identical
coefficients. Uniqueness in the actual normal basis removes the coordinate
choice from the price derivative. -/
open MeasureTheory ProbabilityTheory Set Module Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma winningMass_isometry (v : Fin k → Space d) (b : Fin k → ℝ)
    (T : Space d ≃ₗᵢ[ℝ] Space d) (i : Fin k) :
    winningMass (fun j => T (v j)) b i = winningMass v b i := by
  have hm : MeasurePreserving T (gaussian d) (gaussian d) :=
    ⟨T.continuous.measurable,stdGaussian_map T⟩
  have he : T ⁻¹' winningCell (fun j => T (v j)) b i = winningCell v b i := by
    ext x
    exact winningCell_isometry v b T i x
  have hh := hm.measureReal_preimage (measurableSet_winningCell (fun j => T (v j)) b i).nullMeasurableSet
  rw [he] at hh
  exact hh.symm

lemma basis_flux_weights_unique {n : ℕ} (B : Basis (Fin n) ℝ (Space n))
    (a c : Fin n → ℝ) (h : (∑ i, a i • B i) = ∑ i, c i • B i) : a = c := by
  classical
  funext r
  have hh := congrArg (B.coord r) h
  simpa [map_sum,map_smul,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply] using hh

theorem simplicial_mass_flux_base_derivative
    (v : Fin (d+2) → Space (d+1)) (b q : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (w : Fin (d+1) → ℝ)
    (hf : rawWinningMoment v b 0 = ∑ i, w i • (v 0 - v i.succ)) :
    HasDerivAt (fun t => winningMass v (affinePrices b q t) 0)
      (∑ i, w i * (q i.succ - q 0)) 0 := by
  obtain ⟨T,hp,hs⟩ := simplicial_winning_graph_coordinates v B hB
  let u : Fin (d+2) → Space (d+1) := fun i => T (v i)
  let A := B.map T.toLinearEquiv
  have hA (i : Fin (d+1)) : A i = u 0 - u i.succ := by simp [A,u,hB i]
  let c : Fin (d+1) → ℝ := fun i =>
    graphFacetDensity (winningGraphSlopes u) (winningGraphPrices u b) i / inwardCoordinate u i
  have ht : rawWinningMoment u b 0 = ∑ i, w i • (u 0 - u i.succ) := by
    rw [rawWinningMoment_isometry, hf]
    simp only [map_sum,map_smul,map_sub,u]
  have hc : (∑ i, w i • A i) = ∑ i, c i • A i := by
    simp_rw [hA]
    rw [← ht]
    exact gaussian_winning_cell_graph_flux u b hp hs
  have hw := basis_flux_weights_unique A w c hc
  have hd := winningMass_graph_price_derivative u b q hp hs
  convert hd using 1
  · funext t
    exact (winningMass_isometry v (affinePrices b q t) T 0).symm
  · rw [hw]

end GaussianMeasureBridge
