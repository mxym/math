import Entry005.TruncationDefinitions
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators

namespace Entry005

@[simp] theorem truncationVertex_apply {d : ℕ} (i j : Fin d) :
    truncationVertex i j = if i = j then 1 else 0 := by
  simp [truncationVertex, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

@[simp] theorem truncationVertex_sum {d : ℕ} (i : Fin d) :
    (∑ j, truncationVertex i j) = 1 := by
  simp [truncationVertex_apply]

theorem truncationSet_convex (d : ℕ) (t : ℝ) : Convex ℝ (truncationSet d t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hxt, hx1⟩
  rcases hy with ⟨hy0, hyt, hy1⟩
  refine ⟨fun i => ?_, ?_, ?_⟩
  · change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i))
  · change t ≤ ∑ i, (a * x i + b * y i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hxt ha, mul_le_mul_of_nonneg_left hyt hb]
  · change (∑ i, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]

theorem truncationVertices_mem {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : Fin d ⊕ Fin d) : truncationVertices t v ∈ truncationSet d t := by
  cases v with
  | inl i =>
    refine ⟨fun j => ?_, ?_, ?_⟩
    · simp only [truncationVertices, truncationVertex_apply]
      split_ifs <;> norm_num
    · simpa only [truncationVertices, truncationVertex_sum] using ht1
    · simp only [truncationVertices, truncationVertex_sum, le_refl]
  | inr i =>
    refine ⟨fun j => ?_, ?_, ?_⟩
    · change 0 ≤ t * truncationVertex i j
      simp only [truncationVertex_apply]
      split_ifs <;> simp_all
    · change t ≤ ∑ j, t * truncationVertex i j
      simp only [← Finset.mul_sum, truncationVertex_sum, mul_one, le_refl]
    · change (∑ j, t * truncationVertex i j) ≤ 1
      simpa only [← Finset.mul_sum, truncationVertex_sum, mul_one] using ht1

/-- The literal inequality-defined truncation is the convex hull of its actual 2d vertices. -/
theorem truncationSet_eq_convexHull {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    truncationSet d t = convexHull ℝ (Set.range (truncationVertices (d := d) t)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hx0, hxt, hx1⟩
    let s : ℝ := ∑ i, x i
    have hs0 : 0 < s := ht0.trans_le hxt
    have hden : 0 < s * (1 - t) := mul_pos hs0 (sub_pos.mpr ht1)
    let a : ℝ := (s - t) / (s * (1 - t))
    let b : ℝ := (1 - s) / (s * (1 - t))
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hxt) hden.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx1) hden.le
    let w : Fin d ⊕ Fin d → ℝ := Sum.elim (fun i => a * x i) (fun i => b * x i)
    have hw : ∑ v, w v = 1 := by
      simp only [w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        ← Finset.mul_sum]
      change a * s + b * s = 1
      dsimp [a, b]
      field_simp [hs0.ne', (sub_pos.mpr ht1).ne']
      ring
    refine mem_convexHull_of_exists_fintype w (truncationVertices t)
      (fun v => ?_) hw (fun v => ⟨v, rfl⟩) ?_
    · cases v with
      | inl i => exact mul_nonneg ha (hx0 i)
      | inr i => exact mul_nonneg hb (hx0 i)
    · have hab : a + b * t = 1 := by
        dsimp [a, b]
        field_simp [hs0.ne', (sub_pos.mpr ht1).ne']
        ring
      ext j
      change (∑ v, w v • truncationVertices t v) j = x j
      simp only [w, Fintype.sum_sum_type, truncationVertices, Sum.elim_inl, Sum.elim_inr]
      simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        smul_eq_mul, truncationVertex_apply]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      nlinarith [congrArg (fun q : ℝ => q * x j) hab]
  · apply convexHull_min
    · rintro x ⟨v, rfl⟩
      exact truncationVertices_mem ht0.le ht1.le v
    · exact truncationSet_convex d t

theorem truncationSet_isCompact {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsCompact (truncationSet d t) := by
  rw [truncationSet_eq_convexHull ht0 ht1]
  exact (Set.finite_range (truncationVertices (d := d) t)).isCompact_convexHull ℝ

theorem truncationSet_nonempty {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (truncationSet d t).Nonempty := by
  let i : Fin d := ⟨0, hd⟩
  exact ⟨truncationVertex i, truncationVertices_mem ht0 ht1 (Sum.inl i)⟩

/-- The actual compact convex truncation carrier, with no replacement scalar model. -/
def truncationBody (d : ℕ) (t : ℝ) (hd : 0 < d) (ht0 : 0 < t) (ht1 : t < 1) :
    ConvexBody (Space d) where
  carrier := truncationSet d t
  convex' := truncationSet_convex d t
  isCompact' := truncationSet_isCompact ht0 ht1
  nonempty' := truncationSet_nonempty hd ht0.le ht1.le

@[simp] theorem truncationBody_coe (d : ℕ) (t : ℝ) (hd : 0 < d)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (truncationBody d t hd ht0 ht1 : Set (Space d)) = truncationSet d t := rfl

/-- A strict positive-coordinate point between the two parallel slicing hyperplanes. -/
theorem truncationSet_interior_nonempty {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : (interior (truncationSet d t)).Nonempty := by
  let U : Set (Space d) := {x | (∀ i, 0 < x i) ∧ t < ∑ i, x i ∧ (∑ i, x i) < 1}
  have hc : Continuous (fun x : Space d => ∑ i, x i) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).comp (PiLp.continuous_ofLp _ _))
  have hU : IsOpen U := by
    have hcoords : IsOpen {x : Space d | ∀ i, 0 < x i} := by
      simpa only [Set.ofPred_forall, Function.comp_def] using
        isOpen_iInter_of_finite (fun i : Fin d => isOpen_lt continuous_const
          ((continuous_apply i).comp (PiLp.continuous_ofLp _ _)))
    exact hcoords.inter ((isOpen_lt continuous_const hc).inter
      (isOpen_lt hc continuous_const))
  have hsub : U ⊆ truncationSet d t := fun x hx =>
    ⟨fun i => (hx.1 i).le, hx.2.1.le, hx.2.2.le⟩
  let x : Space d := WithLp.toLp 2 (fun _ => (1 + t) / (2 * d))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : (∑ i, x i) = (1 + t) / 2 := by
    change (∑ _i : Fin d, (1 + t) / (2 * (d : ℝ))) = (1 + t) / 2
    simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨x, (hU.subset_interior_iff.mpr hsub) ?_⟩
  refine ⟨fun i => ?_, ?_, ?_⟩
  · change 0 < (1 + t) / (2 * (d : ℝ))
    positivity
  · rw [hsum]
    linarith
  · rw [hsum]
    linarith

end Entry005
