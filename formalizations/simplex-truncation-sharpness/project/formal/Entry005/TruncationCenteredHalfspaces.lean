import Entry005.TruncationFacetGeometry
import Entry005.TruncationFacetTranslation
import Entry005.TruncationDefinitions

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def truncationCenter (d : ℕ) (t : ℝ) : Space d :=
  WithLp.toLp 2 (fun _ => (1 + t) / (2 * d))

def truncationCenteredHeight (d : ℕ) (t : ℝ) (i : TruncationFacetIndex d) : ℝ :=
  truncationFacetHeight d t i - inner ℝ (truncationFacetNormal d i) (truncationCenter d t)

theorem truncation_center_sum {d : ℕ} (hd : 0 < d) (t : ℝ) :
    (∑ i, truncationCenter d t i) = (1 + t) / 2 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (∑ _i : Fin d, (1 + t) / (2 * (d : ℝ))) = (1 + t) / 2
  simp only [Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem truncation_centered_height_pos {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (i : TruncationFacetIndex d) :
    0 < truncationCenteredHeight d t i := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hinv : 0 < (Real.sqrt (d : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hdR)
  cases i with
  | inl i =>
    simp [truncationCenteredHeight, truncationFacetHeight, truncationFacetNormal,
      truncationVertex, inner_neg_left, EuclideanSpace.inner_single_left, truncationCenter]
    positivity
  | inr i =>
    cases i <;> simp only [truncationCenteredHeight, truncationFacetHeight,
      truncationFacetNormal, inner_neg_left, truncation_unit_diagonal_inner,
      truncation_center_sum hd t, div_eq_mul_inv]
    · nlinarith [mul_pos hinv (by linarith : 0 < 1 - t)]
    · nlinarith [mul_pos hinv (by linarith : 0 < 1 - t)]

theorem truncation_centered_carrier {d : ℕ} (hd : 0 < d) (t : ℝ) :
    finiteHalfspaceSet (truncationFacetNormal d) (truncationCenteredHeight d t) =
      (fun x => x - truncationCenter d t) '' truncationSet d t := by
  change finiteHalfspaceSet (truncationFacetNormal d)
    (fun i => truncationFacetHeight d t i - inner ℝ (truncationFacetNormal d i) (truncationCenter d t)) = _
  rw [finite_halfspace_translate_carrier,
    truncation_halfspace_representation hd t]

theorem truncation_centered_compact {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    IsCompact (finiteHalfspaceSet (truncationFacetNormal d) (truncationCenteredHeight d t)) := by
  rw [truncation_centered_carrier hd t]
  exact (truncationSet_isCompact ht0 ht1).image (continuous_id.sub continuous_const)

theorem truncation_facet_normal_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (truncationFacetNormal d) := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < (Real.sqrt (d : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hdR)
  have hcoord (i : Fin d) : truncationUnitDiagonal d i = (Real.sqrt (d : ℝ))⁻¹ := by
    simp [truncationUnitDiagonal, truncationDiagonal]
  have hsep (i : Fin d) : truncationVertex i ≠ truncationUnitDiagonal d := by
    let j : Fin d := if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · rw [hi]
        exact Fin.ne_of_val_ne (by norm_num)
      · exact hi
    intro he
    have hc := congrArg (fun x : Space d => x j) he
    rw [hcoord] at hc
    rw [truncationVertex_apply, ite_eq_right hij] at hc
    exact (ne_of_gt hs) hc.symm
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hv : truncationVertex i = truncationVertex j := neg_injective he
      exact congrArg Sum.inl ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.injective hv)
    | inr j =>
      cases j
      · have hc := congrArg (fun x : Space d => x i) he
        change -(truncationVertex i i) = truncationUnitDiagonal d i at hc
        rw [hcoord] at hc
        simp [truncationVertex, EuclideanSpace.basisFun_apply] at hc
        linarith
      · exact False.elim (hsep i (neg_injective he))
  | inr i =>
    cases j with
    | inl j =>
      cases i
      · have hc := congrArg (fun x : Space d => x j) he
        change truncationUnitDiagonal d j = -(truncationVertex j j) at hc
        rw [hcoord] at hc
        simp [truncationVertex, EuclideanSpace.basisFun_apply] at hc
        linarith
      · exact False.elim (hsep j (neg_injective he).symm)
    | inr j =>
      cases i <;> cases j
      · rfl
      · have hc := congrArg (fun x : Space d => x ⟨0, by omega⟩) he
        change truncationUnitDiagonal d _ = -truncationUnitDiagonal d _ at hc
        simp only [hcoord] at hc
        linarith
      · have hc := congrArg (fun x : Space d => x ⟨0, by omega⟩) he
        change -truncationUnitDiagonal d _ = truncationUnitDiagonal d _ at hc
        simp only [hcoord] at hc
        linarith
      · rfl

theorem truncation_centered_area_eq {d : ℕ} (hd : 0 < d) (t : ℝ)
    (i : TruncationFacetIndex d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationCenteredHeight d t) i =
      finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i := by
  exact finite_halfspace_facet_area_translation _ _ _ i (truncation_facet_norm hd i)

theorem truncation_centered_entryA {d : ℕ} (hd : 0 < d) (t : ℝ) :
    entryA (finiteHalfspaceSet (truncationFacetNormal d) (truncationCenteredHeight d t)) =
      entryA (truncationSet d t) := by
  rw [truncation_centered_carrier hd t]
  let f : Space d ≃ᵃ[ℝ] Space d := AffineEquiv.constVAdd ℝ (Space d) (-truncationCenter d t)
  have himage : (fun x => x - truncationCenter d t) '' truncationSet d t =
      f '' truncationSet d t := by
    congr 1
    funext x
    change x - truncationCenter d t = -truncationCenter d t + x
    abel
  rw [himage]
  exact entryA_affine_image (by simpa [Space] using (Nat.succ_le_of_lt hd)) f _

theorem truncation_centered_entryDefect {d : ℕ} (hd : 0 < d) (t : ℝ) :
    entryDefect (finiteHalfspaceSet (truncationFacetNormal d) (truncationCenteredHeight d t)) =
      entryDefect (truncationSet d t) := by
  unfold entryDefect
  rw [truncation_centered_entryA hd t]

theorem truncation_centered_volume {d : ℕ} (hd : 0 < d) (t : ℝ) :
    volume (finiteHalfspaceSet (truncationFacetNormal d) (truncationCenteredHeight d t)) =
      volume (truncationSet d t) := by
  rw [truncation_centered_carrier hd t]
  have he : (fun x => x - truncationCenter d t) '' truncationSet d t =
      (fun x : Space d => x + truncationCenter d t) ⁻¹' truncationSet d t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + truncationCenter d t, hx, by simp⟩
  rw [he, measure_preimage_add_right]

end Entry005
