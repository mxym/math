import GaussianNormalCoordinates

/-! Positivity of the actual face-density coefficients for a full normal
basis. Prescribed inner products expose one face while keeping the remaining
inequalities strict, giving a nonempty open Gaussian base region. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma isOpen_winningCell (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) :
    IsOpen (winningCell v b i) := by
  unfold winningCell
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem graphFacetDensity_positive (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (hi : (winningCell v b i).Nonempty) : 0 < graphFacetDensity v b i := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun y => (standardDensity_pos (⟪v i,y⟫ - b i)).le)
    (integrable_standardDensity_comp (gaussian d) _ (by fun_prop)).integrableOn).mpr
  have hs : Function.support (fun y : Space d => standardDensity (⟪v i,y⟫ - b i)) = Set.univ := by
    ext y
    simp [Function.support, (standardDensity_pos (⟪v i,y⟫ - b i)).ne']
  rw [hs, Set.univ_inter]
  exact gaussian_open_pos _ (isOpen_winningCell v b i) hi

lemma winning_graph_gap (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (i : Fin k) (hi : 0 < inwardCoordinate v i) (x : Space (d+1)) :
    inwardCoordinate v i *
      (x 0 - (⟪winningGraphSlopes v i, tailCoordinates x⟫ - winningGraphPrices v b i)) =
      ⟪v 0 - v i.succ,x⟫ - (b 0 - b i.succ) := by
  have hx : ⟪v 0 - v i.succ,x⟫ =
      (v 0 0 - v i.succ 0) * x 0 +
        ⟪tailCoordinates (v 0),tailCoordinates x⟫ - ⟪tailCoordinates (v i.succ),tailCoordinates x⟫ := by
    conv_lhs => rw [← joinCoordinate_eta x]
    rw [inner_sub_left, inner_coordinate_split, inner_coordinate_split]
    ring
  rw [hx]
  simp only [winningGraphSlopes, winningGraphPrices, real_inner_smul_left, inner_sub_left]
  have hn : inwardCoordinate v i ≠ 0 := hi.ne'
  field_simp
  unfold inwardCoordinate at *
  ring

theorem winning_graph_cell_nonempty_of_basis
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (B : Basis (Fin k) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (hv : ∀ i, 0 < inwardCoordinate v i) (r : Fin k) :
    (winningCell (winningGraphSlopes v) (winningGraphPrices v b) r).Nonempty := by
  let c : Fin k → ℝ := fun i => b 0 - b i.succ + if i = r then 0 else 1
  -- The interpolation statement works for a basis with any finite index type.
  let L : StrongDual ℝ (Space (d+1)) := (B.constr ℝ c).toContinuousLinearMap
  let x : Space (d+1) := (InnerProductSpace.toDual ℝ (Space (d+1))).symm L
  have hx (i : Fin k) : ⟪v 0 - v i.succ,x⟫ = c i := by
    rw [real_inner_comm, ← hB i]
    exact (InnerProductSpace.toDual_symm_apply).trans (B.constr_basis ℝ c i)
  refine ⟨tailCoordinates x, fun j hj => ?_⟩
  have hgr := winning_graph_gap v b r (hv r) x
  have hgj := winning_graph_gap v b j (hv j) x
  rw [hx r] at hgr
  rw [hx j] at hgj
  simp [c, hj] at hgr hgj
  have hgr' := hgr.resolve_left (hv r).ne'
  have hr : ⟪winningGraphSlopes v r,tailCoordinates x⟫ - winningGraphPrices v b r = x 0 := by
    linarith
  rw [hr]
  nlinarith [hv j]

theorem winning_graph_density_positive_of_basis
    (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (B : Basis (Fin k) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (hv : ∀ i, 0 < inwardCoordinate v i) (i : Fin k) :
    0 < graphFacetDensity (winningGraphSlopes v) (winningGraphPrices v b) i :=
  graphFacetDensity_positive _ _ i (winning_graph_cell_nonempty_of_basis v b B hB hv i)

end GaussianMeasureBridge
