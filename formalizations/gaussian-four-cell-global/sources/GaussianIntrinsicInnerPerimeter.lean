import GaussianCellErosion
import GaussianFluxEnergy

/-! An intrinsic Gaussian boundary functional from closed-ball erosion.
For every actual simplicial winning cell its one-sided mass derivative is
proved to be the facet-flux sum. No perimeter-minimizing theorem is used. -/
open MeasureTheory ProbabilityTheory Set Module Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d e : ℕ}

noncomputable def gaussianErosionMass (S : Set (Space e)) (t : ℝ) : ℝ :=
  (gaussian e).real {x | ∀ y : Space e,dist y x ≤ t → y ∈ S}

noncomputable def gaussianInnerPerimeter (S : Set (Space e)) : ℝ :=
  -derivWithin (gaussianErosionMass S) (Ici 0) 0

theorem simplicial_cell_erosion_derivative
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i,B i=v 0-v i.succ)
    (w : Fin (d+1) → ℝ)
    (hf : rawWinningMoment v b 0 = ∑ i,w i • (v 0-v i.succ)) :
    HasDerivWithinAt (gaussianErosionMass (winningCell v b 0))
      (-(∑ i,w i*‖v 0-v i.succ‖)) (Ici 0) 0 := by
  have hn (i : Fin (d+1)) : v 0-v i.succ ≠ 0 := by
    rw [← hB i]
    exact B.ne_zero i
  apply (actual_inward_boundary_mass_derivative v b B hB w hf).hasDerivWithinAt.congr_of_mem
  · intro t ht
    simp only [gaussianErosionMass,← simplicialInset_eq_closedBall_erosion v b hn t ht]
  · exact self_mem_Ici

theorem actual_simplicial_cell_inner_perimeter
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hf : ∀ i,rawWinningMoment v b i = ∑ j,w i j • (v i-v j)) (i : Fin (d+2)) :
    gaussianInnerPerimeter (winningCell v b i) = ∑ j,w i j*‖v i-v j‖ := by
  classical
  let p : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
  obtain ⟨B,hB⟩ := simplicial_normal_basis (v ∘ p) (hv.comp_embedding p.toEmbedding)
  have hfc : rawWinningMoment (v ∘ p) (b ∘ p) 0 =
      ∑ j : Fin (d+1),w i (p j.succ) • ((v ∘ p) 0-(v ∘ p) j.succ) := by
    rw [rawWinningMoment_reindex]
    simp only [p,Equiv.swap_apply_left,Function.comp_apply]
    rw [hf i]
    calc
      _ = ∑ j,w i (p j) • (v i-v (p j)) := (Equiv.sum_comp p _).symm
      _ = _ := by simp [Fin.sum_univ_succ,p]
  have hd := simplicial_cell_erosion_derivative (v ∘ p) (b ∘ p) B hB
    (fun j => w i (p j.succ)) hfc
  rw [winningCell_reindex] at hd
  simp only [p,Equiv.swap_apply_left] at hd
  rw [gaussianInnerPerimeter,hd.derivWithin (uniqueDiffOn_Ici 0 0 self_mem_Ici),neg_neg]
  calc
    _ = ∑ j,w i (p j)*‖v i-v (p j)‖ := by simp [Fin.sum_univ_succ,p]
    _ = _ := Equiv.sum_comp p (fun j => w i j*‖v i-v j‖)

theorem actual_simplicial_cluster_inner_perimeter
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hf : ∀ i,rawWinningMoment v b i = ∑ j,w i j • (v i-v j)) :
    (∑ i,gaussianInnerPerimeter (winningCell v b i))/2 = fluxPerimeter v w := by
  simp only [actual_simplicial_cell_inner_perimeter v b hv w hf,fluxPerimeter]

end GaussianMeasureBridge
