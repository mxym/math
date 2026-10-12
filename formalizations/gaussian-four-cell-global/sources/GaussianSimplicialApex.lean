import GaussianAllCellsFlux

/-! A full simplicial score-price cluster is a translated conical fan.
Riesz interpolation constructs its common vertex from the actual prices. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem simplicial_common_apex
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃! z : Space (d+1),∀ i,⟪v i,z⟫-b i = ⟪v 0,z⟫-b 0 := by
  obtain ⟨B,hB⟩ := simplicial_normal_basis v hv
  obtain ⟨z,hz⟩ := basis_inner_interpolate B (fun i => b 0-b i.succ)
  have hc : ∀ i,⟪v i,z⟫-b i = ⟪v 0,z⟫-b 0 := by
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    have he := hz j
    rw [hB j,inner_sub_right,real_inner_comm (v 0) z,real_inner_comm (v j.succ) z] at he
    linarith
  refine ⟨z,hc,?_⟩
  intro y hy
  have hi (i : Fin (d+1)) : ⟪B i,y-z⟫ = 0 := by
    have he := hy i.succ
    have hh := hc i.succ
    rw [hB i,inner_sub_left,inner_sub_right,inner_sub_right]
    linarith
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  conv_lhs => lhs; rw [← B.sum_repr (y-z)]
  simp only [sum_inner,real_inner_smul_left,hi,mul_zero,Finset.sum_const_zero]

theorem winningCell_apex_translation
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ) (z : Space (d+1))
    (hz : ∀ i,⟪v i,z⟫-b i = ⟪v 0,z⟫-b 0) (i : Fin (d+2)) :
    winningCell v b i = {x | x-z ∈ winningCell v 0 i} := by
  ext x
  simp only [winningCell,mem_setOf_eq,Pi.zero_apply,sub_zero,inner_sub_right]
  constructor
  · intro hx j hj
    have he := hx j hj
    linarith [hz j,hz i]
  · intro hx j hj
    have he := hx j hj
    linarith [hz j,hz i]

end GaussianMeasureBridge
