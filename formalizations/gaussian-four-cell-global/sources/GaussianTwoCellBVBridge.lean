import GaussianBVComparisonInterface

/-! The simplicial BV/erosion bridge is unconditional for two cells in every
positive ambient dimension, at arbitrary actual score prices. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped Topology ENNReal RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma two_winning_cell_zero_halfspace (v : Fin 2 → Space (d+1)) (b : Fin 2 → ℝ)
    (hv : Function.Injective v) :
    ∃ u : Space (d+1),∃ a : ℝ,‖u‖=1 ∧ winningCell v b 0={x | a < ⟪u,x⟫} := by
  let w := v 0-v 1
  have hw : w ≠ 0 := sub_ne_zero.mpr (fun h => by have hh := hv h; norm_num at hh)
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u := ‖w‖⁻¹ • w
  let a := (b 0-b 1)/‖w‖
  have hu : ‖u‖=1 := by
    simp [u,norm_smul,inv_mul_cancel₀ hn.ne']
  refine ⟨u,a,hu,?_⟩
  ext x
  have he : ⟪u,x⟫=⟪w,x⟫/‖w‖ := by
    change ⟪‖w‖⁻¹ • w,x⟫=⟪w,x⟫/‖w‖
    rw [real_inner_smul_left,div_eq_mul_inv,mul_comm]
  change (∀ j : Fin 2,j ≠ 0 → ⟪v j,x⟫-b j < ⟪v 0,x⟫-b 0) ↔ a < ⟪u,x⟫
  rw [he]
  change _ ↔ (b 0-b 1)/‖w‖ < ⟪w,x⟫/‖w‖
  rw [div_lt_div_iff_of_pos_right hn]
  change _ ↔ b 0-b 1 < ⟪v 0-v 1,x⟫
  rw [inner_sub_left]
  constructor
  · intro hx
    have hh := hx 1 (by norm_num)
    linarith
  · intro hx j hj
    fin_cases j
    · exact (hj rfl).elim
    · change ⟪v 1,x⟫-b 1 < ⟪v 0,x⟫-b 0
      linarith

theorem two_winning_cell_perimeter_bridge (v : Fin 2 → Space (d+1)) (b : Fin 2 → ℝ)
    (hv : Function.Injective v) (i : Fin 2) :
    gaussianBVPerimeter (winningCell v b i) = ENNReal.ofReal (gaussianInnerPerimeter (winningCell v b i)) := by
  let p : Equiv.Perm (Fin 2) := Equiv.swap 0 i
  obtain ⟨u,a,hu,hS⟩ := two_winning_cell_zero_halfspace (v ∘ p) (b ∘ p) (hv.comp p.injective)
  rw [winningCell_reindex] at hS
  simp only [p,Equiv.swap_apply_left] at hS
  rw [hS]
  exact gaussian_unit_halfspace_perimeter_bridge u hu a

theorem simplicial_BV_upper_bound_zero : SimplicialBVUpperBound 0 := by
  intro v hv i
  rw [two_winning_cell_perimeter_bridge v (canonicalPrices v) hv.injective i]

end GaussianMeasureBridge
