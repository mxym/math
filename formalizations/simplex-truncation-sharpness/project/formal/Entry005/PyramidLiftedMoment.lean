import Entry005.PyramidProjectionVolume
import Entry005.FiniteHalfspaceHorizontalMoment

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005

theorem pyramid_lifted_law_image {ι : Type*} [Fintype ι] {d : ℕ}
    (a h : ι → ℝ) (n : ι → Space d) (M : ℝ) (hh : ∀ i, h i ≠ 0) :
    pyramidLiftCoordinates d '' finiteLiftedLawZonotope (fun i => a i * h i / M)
      (finiteConePoint (fun i j => n i j) h) =
      finiteZonotope (fun i => (a i / M) • WithLp.toLp 2 (n i, h i)) := by
  unfold finiteLiftedLawZonotope finiteLawZonotope
  have hi : pyramidLiftCoordinates d ''
      finiteZonotope (fun i => (a i * h i / M) •
        WithLp.toLp 2 (Fin.cases 1 (finiteConePoint (fun i j => n i j) h i))) =
      finiteZonotope (fun i => pyramidLiftCoordinates d ((a i * h i / M) •
        WithLp.toLp 2 (Fin.cases 1 (finiteConePoint (fun i j => n i j) h i)))) :=
    finite_zonotope_linear_image _ _
  rw [hi]
  congr 1
  funext i
  exact pyramid_lifted_law_generator a h n M hh i

variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

theorem pyramid_side_zonotope_eq_scaled_lifted (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    pyramidSideZonotope n h = ((volume (finiteHalfspaceSet n h)).toReal / 2) •
      (pyramidLiftCoordinates d '' finiteLiftedLawZonotope
        (fun i => finiteHalfspaceFacetArea n h i * h i /
          ((d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal))
        (finiteConePoint (fun i j => n i j) h)) := by
  have hV := finite_halfspace_volume_pos n h hn hh hc
  have hd : (d : ℝ) ≠ 0 := by
    have hdN : 0 < d := by simpa [Space] using (finrank_pos_iff.mpr inferInstance :
      0 < finrank ℝ (Space d))
    exact_mod_cast hdN.ne'
  rw [pyramid_lifted_law_image _ _ _ _ (fun i => (hh i).ne'), ← finite_zonotope_scalar_image]
  unfold pyramidSideZonotope
  congr 1
  funext i
  rw [smul_smul]
  congr 1
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  field_simp [hV.ne', hd]

/-- First affine determinant moment B equals the actual lifted side-zonotope
volume, with the exact Euclidean and factorial normalization. -/
theorem pyramid_side_zonotope_volume_lifted_moment (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume (pyramidSideZonotope n h)).toReal =
      (volume (finiteHalfspaceSet n h)).toReal ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let V := (volume (finiteHalfspaceSet n h)).toReal
  let M := (d : ℝ) * V
  let a := finiteHalfspaceFacetArea n h
  have hd : finrank ℝ (Space d) = d := by simp [Space]
  have hV : 0 < V := finite_halfspace_volume_pos n h hn hh hc
  have hM : 0 < M := by simpa only [M, V, hd] using finite_halfspace_normalization_pos n h hn hh hc
  have hmass : ∑ i, a i * h i = M := by
    simpa only [a, M, V, hd] using finite_halfspace_facet_mass n h hn hh hinj hc
  have hmoment := finite_cone_lifted_zonotope_volume_first_moment a h (fun i j => n i j) M
    (finite_halfspace_facet_area_nonneg n h) hh hM hmass
  rw [pyramid_side_zonotope_eq_scaled_lifted n h hn hh hc,
    real_volume_nonnegative_smul _ _ (by positivity), IntrinsicLinearImageReuse.isometry_volume_image]
  change (V / 2) ^ finrank ℝ (WithLp 2 (Space d × ℝ)) *
    (volume (finiteLiftedLawZonotope (fun i => a i * h i / M)
      (finiteConePoint (fun i j => n i j) h))).toReal = _
  rw [hmoment]
  have hdim : finrank ℝ (WithLp 2 (Space d × ℝ)) = d + 1 := by
    rw [← (pyramidLiftCoordinates d).toLinearEquiv.finrank_eq]
    simp [Space]
  rw [hdim]
  change (V / 2) ^ (d + 1) * (2 ^ (d + 1) / ((d + 1).factorial : ℝ) *
    (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (finiteConeLaw a h (fun i j => n i j) M) (d + 1))) = _
  simp only [finiteHalfspaceConeLaw, hd]
  change (V / 2) ^ (d + 1) * (2 ^ (d + 1) / ((d + 1).factorial : ℝ) * _) = V ^ (d + 1) / _ * _
  dsimp [a, M, V]
  rw [div_pow]
  field_simp

end Entry005
