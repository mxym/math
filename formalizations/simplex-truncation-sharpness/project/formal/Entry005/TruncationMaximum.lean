import Entry005.TruncationGeometry
import Entry005.SimplexVolumeInterface
import Mxym.StochasticRigidity
import Mathlib.LinearAlgebra.Multilinear.Basic
import Entry005.TruncationConvexDeterminant

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem truncationSimplexPoints_independent {d : ℕ} (t : ℝ) (i : Fin d)
    (ht : t ≠ 1) : AffineIndependent ℝ (truncationSimplexPoints t i) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at hs
  have hc (j : Fin d) : t * w 0 * (if i = j then 1 else 0) + w j.succ = 0 := by
    have h := congrArg (fun x : Space d => x j) hs
    simp only [Fin.sum_univ_succ, truncationSimplexPoints, Fin.cons_zero,
      Fin.cons_succ, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, truncationVertex_apply, mul_ite, mul_one,
      mul_zero, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.zero_apply,
      mul_comm] at h
    by_cases hij : i = j <;> simpa [hij, mul_comm, mul_left_comm, mul_assoc] using h
  have hsum : t * w 0 + ∑ j : Fin d, w j.succ = 0 := by
    have h := congrArg (fun f : Fin d → ℝ => ∑ j, f j) (funext hc)
    simpa only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero] using h
  rw [Fin.sum_univ_succ] at hw
  have hw0 : w 0 = 0 := by
    have : (t - 1) * w 0 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht)
  intro j
  refine Fin.cases hw0 (fun k => ?_) j
  simpa only [hw0, mul_zero, zero_mul, zero_add] using hc k

/-- The displayed truncation simplex is an actual full-dimensional affine simplex. -/
def truncationSimplex {d : ℕ} (t : ℝ) (i : Fin d) (ht : t ≠ 1) :
    Affine.Simplex ℝ (Space d) d where
  points := truncationSimplexPoints t i
  independent := truncationSimplexPoints_independent t i ht

@[simp] theorem truncationSimplex_points {d : ℕ} (t : ℝ) (i : Fin d) (ht : t ≠ 1) :
    (truncationSimplex t i ht).points = truncationSimplexPoints t i := rfl

theorem truncationSimplex_subset {d : ℕ} (t : ℝ) (i : Fin d) (ht : t ≠ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    simplexSet (truncationSimplex t i ht) ⊆ truncationSet d t := by
  apply convexHull_min
  · rintro x ⟨j, rfl⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · exact truncationVertices_mem ht0 ht1 (Sum.inr i)
    · exact truncationVertices_mem ht0 ht1 (Sum.inl k)
  · exact truncationSet_convex d t

/-- The true homogeneous vertex matrix of the displayed simplex has determinant 1-t. -/
theorem truncationSimplex_augmented_det {d : ℕ} (t : ℝ) (i : Fin d) :
    (augmentedVertices (truncationSimplexPoints t i)).det = 1 - t := by
  classical
  let A := augmentedVertices (truncationSimplexPoints t i)
  let B := A.updateCol 0 (fun k => A k 0 + (-t) * A k i.succ)
  have hdet : B.det = A.det :=
    Matrix.det_updateCol_add_smul_self A (Fin.succ_ne_zero i).symm (-t)
  have hcol (k : Fin (d + 1)) : B k 0 = if k = 0 then 1 - t else 0 := by
    refine Fin.cases ?_ (fun l => ?_) k
    · simp [B, A, augmentedVertices, sub_eq_add_neg]
    · simp [B, A, augmentedVertices, truncationSimplexPoints, PiLp.smul_apply]
  have hminor : B.submatrix Fin.succ Fin.succ = 1 := by
    ext k l
    simp [B, A, augmentedVertices, truncationSimplexPoints, Matrix.one_apply, eq_comm]
  rw [← hdet, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [hcol, ite_true, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [hminor, Matrix.det_one, mul_one]
  · intro k _ hk
    simp [hcol, hk]
  · simp

/-- The actual untruncated coordinate simplex is exactly the literal t=0 inequality set. -/
theorem truncationSimplex_zero_set {d : ℕ} (i : Fin d) :
    simplexSet (truncationSimplex 0 i (by norm_num)) = truncationSet d 0 := by
  classical
  apply Set.Subset.antisymm
  · exact truncationSimplex_subset 0 i (by norm_num) (by norm_num) (by norm_num)
  · intro x hx
    let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ j, x j) (fun j => x j)
    apply mem_convexHull_of_exists_fintype w
      (truncationSimplex 0 i (by norm_num)).points
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact sub_nonneg.mpr hx.2.2
      · exact hx.1 k
    · simp [w, Fin.sum_univ_succ]
    · intro j
      exact ⟨j, rfl⟩
    · ext k
      change (∑ j, w j • truncationSimplexPoints 0 i j) k = x k
      rw [Fin.sum_univ_succ]
      simp only [truncationSimplexPoints, Fin.cons_zero, Fin.cons_succ, zero_smul,
        smul_zero, zero_add, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        w, smul_eq_mul, truncationVertex_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private def ray {d : ℕ} : Fin d ⊕ Fin d → Fin d := Sum.elim id id

private theorem horizontal_column_l1 {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : Fin d ⊕ Fin d) : (∑ k, |truncationVertices t v k|) ≤ 1 := by
  cases v with
  | inl i =>
    simp only [truncationVertices, truncationVertex_apply]
    simp [abs_ite]
  | inr i =>
    simp only [truncationVertices, PiLp.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg ht0, truncationVertex_apply]
    simpa [abs_ite, ← Finset.mul_sum] using ht1

private theorem repeated_ray_bound {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : Fin (d + 1) → Fin d ⊕ Fin d) (a b : Fin (d + 1)) (i : Fin d)
    (hab : b ≠ a) (ha : v a = Sum.inl i) (hb : v b = Sum.inr i) :
    |(augmentedVertices (fun j => truncationVertices t (v j))).det| ≤ 1 - t := by
  classical
  let A := augmentedVertices (fun j => truncationVertices t (v j))
  let B := A.updateCol b (fun k => A k b + (-t) * A k a)
  have hdet : B.det = A.det := Matrix.det_updateCol_add_smul_self A hab (-t)
  have hcol (k : Fin (d + 1)) : B k b = if k = 0 then 1 - t else 0 := by
    refine Fin.cases ?_ (fun l => ?_) k
    · simp [B, A, augmentedVertices, sub_eq_add_neg]
    · simp [B, A, augmentedVertices, ha, hb, truncationVertices, PiLp.smul_apply]
  have hminor : B.submatrix (0 : Fin (d + 1)).succAbove b.succAbove =
      fun k l => truncationVertices t (v (b.succAbove l)) k := by
    ext k l
    simp [B, A, augmentedVertices, Fin.succAbove_zero,
      Fin.succAbove_ne]
  have hminor_bound : |(B.submatrix (0 : Fin (d + 1)).succAbove b.succAbove).det| ≤ 1 := by
    rw [hminor]
    apply (Mxym.StochasticRigidity.abs_det_le_column_l1_product _).trans
    calc
      _ ≤ ∏ _j : Fin d, (1 : ℝ) := Finset.prod_le_prod₀
        (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
        (fun j _ => horizontal_column_l1 ht0 ht1 (v (b.succAbove j)))
      _ = 1 := by simp
  have hexpand : B.det = (-1 : ℝ) ^ (b : ℕ) * (1 - t) *
      (B.submatrix (0 : Fin (d + 1)).succAbove b.succAbove).det := by
    rw [Matrix.det_succ_column B b, Finset.sum_eq_single 0]
    · simp only [hcol, ite_true, Fin.val_zero, zero_add]
    · intro k _ hk
      simp [hcol, hk]
    · simp
  rw [← hdet, hexpand, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (sub_nonneg.mpr ht1)]
  exact mul_le_of_le_one_right (sub_nonneg.mpr ht1) hminor_bound

/-- Every actual vertex tuple, including repetitions, has lifted determinant at most 1-t. -/
theorem truncation_vertex_tuple_determinant_bound {d : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : Fin (d + 1) → Fin d ⊕ Fin d) :
    |(augmentedVertices (fun j => truncationVertices t (v j))).det| ≤ 1 - t := by
  classical
  have hn : ¬ Function.Injective (fun j => ray (v j)) := by
    intro h
    have hc := Fintype.card_le_of_injective _ h
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨a, b, he, hab⟩ := Function.not_injective_iff.mp hn
  cases hva : v a with
  | inl i =>
    cases hvb : v b with
    | inl j =>
      have hij : i = j := by simpa [ray, hva, hvb] using he
      subst j
      have hd : (augmentedVertices (fun j => truncationVertices t (v j))).det = 0 := by
        apply Matrix.det_zero_of_column_eq hab
        intro k
        simp [augmentedVertices, hva, hvb]
      rw [hd, abs_zero]
      exact sub_nonneg.mpr ht1
    | inr j =>
      have hij : i = j := by simpa [ray, hva, hvb] using he
      subst j
      exact repeated_ray_bound ht0 ht1 v a b i hab.symm hva hvb
  | inr i =>
    cases hvb : v b with
    | inl j =>
      have hij : i = j := by simpa [ray, hva, hvb] using he
      subst j
      exact repeated_ray_bound ht0 ht1 v b a i hab hvb hva
    | inr j =>
      have hij : i = j := by simpa [ray, hva, hvb] using he
      subst j
      have hd : (augmentedVertices (fun j => truncationVertices t (v j))).det = 0 := by
        apply Matrix.det_zero_of_column_eq hab
        intro k
        simp [augmentedVertices, hva, hvb]
      rw [hd, abs_zero]
      exact sub_nonneg.mpr ht1

/-- The determinant bound covers arbitrary actual inscribed points, not only polytope vertices. -/
theorem truncation_tuple_determinant_bound {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (z : Fin (d + 1) → Space d) (hz : ∀ j, z j ∈ truncationSet d t) :
    |(augmentedVertices z).det| ≤ 1 - t := by
  apply augmentedVertices_abs_det_le_of_mem_convexHull (truncationVertices t) z (1 - t)
  · exact truncation_vertex_tuple_determinant_bound ht0.le ht1.le
  · intro j
    rw [← truncationSet_eq_convexHull ht0 ht1]
    exact hz j

/-- A genuine global maximum for the literal truncation body and all actual inscribed simplices. -/
theorem truncationSimplex_maximumInscribed {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (i : Fin d) :
    maximumInscribed (truncationBody d t hd ht0 ht1)
      (truncationSimplex t i (ne_of_lt ht1)) := by
  let S := truncationSimplex t i (ne_of_lt ht1)
  let P := truncationSimplex 0 i (by norm_num)
  have hd1 : 1 ≤ d := hd
  have hS : simplexSet S ⊆ truncationSet d t :=
    truncationSimplex_subset t i (ne_of_lt ht1) ht0.le ht1.le
  have hambient : truncationSet d t ⊆ simplexSet P := by
    rw [truncationSimplex_zero_set i]
    exact fun x hx => ⟨hx.1, ht0.le.trans hx.2.1, hx.2.2⟩
  have hSinterface := simplexMatrixVolumeInterface d hd1 P S (hS.trans hambient)
  have hPdet : (augmentedVertices P.points).det = 1 := by
    simpa only [P, truncationSimplex_points, sub_zero] using
      truncationSimplex_augmented_det 0 i
  have hSdet : |(simplexBarycentricMatrix P S).det| = 1 - t := by
    simp only [simplexBarycentricMatrix, Matrix.det_mul, Matrix.det_nonsing_inv,
      hPdet, Ring.inverse_eq_inv, inv_one, one_mul]
    change |(augmentedVertices (truncationSimplexPoints t i)).det| = 1 - t
    rw [truncationSimplex_augmented_det, abs_of_nonneg (sub_nonneg.mpr ht1.le)]
  refine ⟨hS, fun T hT => ?_⟩
  have hTactual : simplexSet T ⊆ truncationSet d t := hT
  have hTinterface := simplexMatrixVolumeInterface d hd1 P T (hTactual.trans hambient)
  have hTdet : |(simplexBarycentricMatrix P T).det| ≤ 1 - t := by
    simp only [simplexBarycentricMatrix, Matrix.det_mul, Matrix.det_nonsing_inv,
      hPdet, Ring.inverse_eq_inv, inv_one, one_mul]
    apply truncation_tuple_determinant_bound ht0 ht1 T.points
    intro j
    exact hTactual (subset_convexHull ℝ _ ⟨j, rfl⟩)
  have hratio : (volume (simplexSet T)).toReal / (volume (simplexSet P)).toReal ≤
      (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal := by
    rw [← hTinterface.2.2.2.2.2.2.2, ← hSinterface.2.2.2.2.2.2.2, hSdet]
    exact hTdet
  have hreal := (div_le_div_iff_of_pos_right hSinterface.2.2.2.1).mp hratio
  exact (ENNReal.toReal_le_toReal hTinterface.2.2.1 hSinterface.2.2.1).mp hreal

end Entry005
