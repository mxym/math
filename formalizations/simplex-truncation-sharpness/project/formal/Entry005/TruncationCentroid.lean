import Entry005.TruncationDefinitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def truncationFullBasis {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) :
    AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  ⟨S.points, S.independent, S.affineSpan_eq_top (by simp [Space])⟩

theorem affine_scalar_homothety_value {d : ℕ} (f : Space d →ᵃ[ℝ] ℝ)
    (c x : Space d) (r : ℝ) :
    f (c + r • (x - c)) = f c + r * (f x - f c) := by
  have hm := f.map_vadd c (r • (x - c))
  change f (r • (x - c) + c) = f.linear (r • (x - c)) + f c at hm
  rw [add_comm] at hm
  rw [hm, map_smul, map_sub]
  have hx := congrFun f.decomp x
  have hc := congrFun f.decomp c
  change f x = f.linear x + f 0 at hx
  change f c = f.linear c + f 0 at hc
  simp only [smul_eq_mul]
  rw [hx, hc]
  ring

theorem full_simplex_centroid_coordinate {d : ℕ}
    (S : Affine.Simplex ℝ (Space d) d) (j : Fin (d + 1)) :
    (truncationFullBasis S).coord j S.centroid = 1 / (d + 1 : ℝ) := by
  change (truncationFullBasis S).coord j
    (Finset.univ.centroid ℝ (truncationFullBasis S)) = _
  simpa only [Finset.card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, one_div] using
    (truncationFullBasis S).coord_apply_centroid (Finset.mem_univ j)

/-- The inequalities describe dilation about this simplex's own centroid. -/
theorem full_simplex_centered_dilation_coordinate_iff {d : ℕ}
    (S : Affine.Simplex ℝ (Space d) d) (ε : ℝ) (hε : 0 ≤ ε) (x : Space d) :
    x ∈ centeredDilation S ε ↔
      ∀ j, -ε / (d + 1 : ℝ) ≤ (truncationFullBasis S).coord j x := by
  let b := truncationFullBasis S
  have hp : 0 < 1 + ε := by linarith
  have hmem (y : Space d) : y ∈ simplexSet S ↔ ∀ j, 0 ≤ b.coord j y := by
    change y ∈ convexHull ℝ (Set.range b) ↔ _
    rw [b.convexHull_eq_nonneg_coord]
    rfl
  have hc (j) : b.coord j S.centroid = 1 / (d + 1 : ℝ) :=
    full_simplex_centroid_coordinate S j
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    change -ε / (d + 1 : ℝ) ≤ b.coord j (S.centroid + (1 + ε) • (y - S.centroid))
    rw [affine_scalar_homothety_value, hc]
    have hn := (hmem y).mp hy j
    simp only [div_eq_mul_inv, one_mul, neg_mul]
    nlinarith [mul_nonneg hp.le hn]
  · intro hx
    let y := S.centroid + (1 + ε)⁻¹ • (x - S.centroid)
    refine ⟨y, (hmem y).mpr ?_, ?_⟩
    · intro j
      change 0 ≤ b.coord j (S.centroid + (1 + ε)⁻¹ • (x - S.centroid))
      rw [affine_scalar_homothety_value, hc]
      have hj := hx j
      change -ε / (d + 1 : ℝ) ≤ b.coord j x at hj
      have he : 1 / (d + 1 : ℝ) + (1 + ε)⁻¹ *
          (b.coord j x - 1 / (d + 1 : ℝ)) =
          ((b.coord j x) + ε / (d + 1 : ℝ)) / (1 + ε) := by
        field_simp
        ring
      rw [he]
      exact div_nonneg (by rw [neg_div] at hj; linarith) hp.le
    · dsimp [y]
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
      simp

/-- Coordinates are derived from the actual simplex reconstruction. -/
theorem truncation_simplex_barycentric {d : ℕ} (t : ℝ) (ht : t < 1) (i : Fin d)
    (S : Affine.Simplex ℝ (Space d) d)
    (hpoints : S.points = truncationSimplexPoints t i) (x : Space d) :
    ∀ j, (truncationFullBasis S).coord j x = truncationBeta t i x j := by
  classical
  let b := truncationFullBasis S
  have hre := b.linear_combination_coord_eq_self x
  have hsum := b.sum_coord_apply_eq_one x
  have hre' : b.coord 0 x • (t • truncationVertex i) +
      (∑ j : Fin d, b.coord j.succ x • truncationVertex j) = x := by
    change (∑ j, b.coord j x • S.points j) = x at hre
    rw [hpoints, Fin.sum_univ_succ] at hre
    simpa only [truncationSimplexPoints, Fin.cons_zero, Fin.cons_succ] using hre
  have hcoords (j : Fin d) :
      x j = t * (if j = i then 1 else 0) * b.coord 0 x + b.coord j.succ x := by
    have he := congrArg (fun y : Space d => y j) hre'
    simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at he
    simp [truncationVertex, EuclideanSpace.basisFun_apply, eq_comm] at he
    by_cases hj : j = i
    · subst j
      simp at he ⊢
      nlinarith
    · simp [hj, Ne.symm hj] at he ⊢
      exact he
  have hsumx : (∑ j, x j) = t * b.coord 0 x + ∑ j : Fin d, b.coord j.succ x := by
    simp_rw [hcoords, Finset.sum_add_distrib]
    simp
  have hzero : b.coord 0 x = truncationBetaZero t x := by
    rw [Fin.sum_univ_succ] at hsum
    unfold truncationBetaZero
    apply (eq_div_iff (by linarith : 1 - t ≠ 0)).mpr
    linarith
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact hzero
  · change b.coord k.succ x = x k - t * (if k = i then 1 else 0) * truncationBetaZero t x
    rw [← hzero]
    linarith [hcoords k]

/-- The actual cut-body inequalities bound its true bottom coordinate. -/
theorem truncation_beta_zero_bounds {d : ℕ} (t : ℝ) (ht : t < 1)
    (x : Space d) (hx : x ∈ truncationSet d t) :
    0 ≤ truncationBetaZero t x ∧ truncationBetaZero t x ≤ 1 := by
  have hp : 0 < 1 - t := by linarith
  refine ⟨div_nonneg (by linarith [hx.2.2]) hp.le, ?_⟩
  unfold truncationBetaZero
  apply (div_le_one hp).mpr
  linarith [hx.2.1]

/-- Every actual barycentric coordinate is at least −t. -/
theorem truncation_beta_lower {d : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (i : Fin d) (x : Space d) (hx : x ∈ truncationSet d t) :
    ∀ k, -t ≤ truncationBeta t i x k := by
  have hb := truncation_beta_zero_bounds t ht1 x hx
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · change -t ≤ truncationBetaZero t x
    linarith [hb.1]
  · change -t ≤ x j - t * (if j = i then 1 else 0) * truncationBetaZero t x
    by_cases hj : j = i
    · simp only [hj, ite_true, mul_one]
      nlinarith [hx.1 i, hb.2]
    · simp only [hj, ite_false, mul_zero, zero_mul, sub_zero]
      linarith [hx.1 j]

/-- A genuine lower vertex on a different ray realizes the minimum −t. -/
theorem truncation_beta_negative_at_lower_vertex {d : ℕ} (t : ℝ) (ht : t < 1)
    (i j : Fin d) (hij : i ≠ j) :
    truncationBeta t i (t • truncationVertex j) i.succ = -t := by
  classical
  have hz : truncationBetaZero t (t • truncationVertex j) = 1 := by
    unfold truncationBetaZero
    have hsum : (∑ k : Fin d, (t • truncationVertex j) k) = t := by
      simp [truncationVertex, EuclideanSpace.basisFun_apply]
    rw [hsum, div_self (by linarith : 1 - t ≠ 0)]
  change (t • truncationVertex j) i - t * (if i = i then 1 else 0) *
    truncationBetaZero t (t • truncationVertex j) = -t
  rw [hz]
  simp [truncationVertex, EuclideanSpace.basisFun_apply, hij]

/-- Exact centroid containment with a supplied actual vertex ordering. No
maximality, cone law, defect identity, or chosen replacement center is assumed. -/
theorem truncation_simplex_centroid_containment_iff {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (i : Fin d)
    (S : Affine.Simplex ℝ (Space d) d)
    (hpoints : S.points = truncationSimplexPoints t i) (ε : ℝ) (hε : 0 ≤ ε) :
    truncationSet d t ⊆ centeredDilation S ε ↔ (d + 1 : ℝ) * t ≤ ε := by
  classical
  have hdp : 0 < (d + 1 : ℝ) := by positivity
  have hcoord (x : Space d) (k) := truncation_simplex_barycentric t ht1 i S hpoints x k
  constructor
  · intro hcontain
    let j : Fin d := if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · rw [hi]
        exact Fin.ne_of_val_ne (by norm_num)
      · exact hi
    have hx : t • truncationVertex j ∈ truncationSet d t := by
      refine ⟨fun k => ?_, ?_, ?_⟩
      · simp [truncationVertex, EuclideanSpace.basisFun_apply]
        split_ifs <;> simp_all
      · simp [truncationVertex, EuclideanSpace.basisFun_apply]
      · simpa [truncationVertex, EuclideanSpace.basisFun_apply] using ht1.le
    have hm := (full_simplex_centered_dilation_coordinate_iff S ε hε _).mp
      (hcontain hx) i.succ
    rw [hcoord, truncation_beta_negative_at_lower_vertex t ht1 i j hij] at hm
    rw [neg_div] at hm
    have h := (le_div_iff₀ hdp).mp (by linarith [hm] : t ≤ ε / (d + 1 : ℝ))
    nlinarith
  · intro ht x hx
    apply (full_simplex_centered_dilation_coordinate_iff S ε hε x).mpr
    intro k
    rw [hcoord]
    have hratio : t ≤ ε / (d + 1 : ℝ) := (le_div_iff₀ hdp).mpr (by nlinarith [ht])
    have hb := truncation_beta_lower t ht0 ht1 i x hx k
    rw [neg_div]
    linarith

/-- The literal sInf-based target excess, about this simplex's own centroid. -/
theorem truncation_simplex_excess_exact {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (i : Fin d)
    (S : Affine.Simplex ℝ (Space d) d)
    (hpoints : S.points = truncationSimplexPoints t i) :
    excess (truncationSet d t) S = (d + 1 : ℝ) * t := by
  unfold excess
  have hnonneg : 0 ≤ (d + 1 : ℝ) * t := by positivity
  have hleast : IsLeast {ε : ℝ | 0 ≤ ε ∧ truncationSet d t ⊆ centeredDilation S ε}
      ((d + 1 : ℝ) * t) := by
    refine ⟨⟨hnonneg, ?_⟩, ?_⟩
    · exact (truncation_simplex_centroid_containment_iff hd t ht0 ht1 i S hpoints _ hnonneg).mpr le_rfl
    · intro ε hε
      exact (truncation_simplex_centroid_containment_iff hd t ht0 ht1 i S hpoints ε hε.1).mp hε.2
  exact hleast.csInf_eq

end Entry005
