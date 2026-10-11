import APPTReview.BaselineGraph
import APPTReview.CenteredVariance

open scoped BigOperators
open Matrix
namespace APPTReview

/-- Removing a common off-diagonal baseline preserves symmetry and row ordering. -/
theorem residual_graph_properties {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (w : ℝ) (hB : B.IsHermitian) (hd : ∀ i, B i i=0)
    (hlow : ∀ i j, i≠j → w≤B i j) (hord : RowMajorAntitone B) :
    let G := B-w • completeAdjacency
    G.IsHermitian ∧ (∀ i, G i i=0) ∧ (∀ i j, 0≤G i j) ∧ RowMajorAntitone G := by
  dsimp only
  refine ⟨hB.sub (completeAdjacency_hermitian.smul (show IsSelfAdjoint w by rfl)), ?_, ?_, ?_⟩
  · intro i; simp [completeAdjacency, hd]
  · intro i j
    by_cases hij : i=j
    · subst j; simp [completeAdjacency, hd]
    · simpa [completeAdjacency, hij] using sub_nonneg.mpr (hlow i j hij)
  · intro i j k l hij hkl hcode
    have h := hord i j k l hij hkl hcode
    simpa [Matrix.sub_apply, Matrix.smul_apply, completeAdjacency,
      ne_of_lt hij, ne_of_lt hkl] using sub_le_sub_right h w

/-- The all-ones physical test bounds the constant off-diagonal component. -/
theorem baseline_all_ones_bound {h : ℕ}
    (G : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) (w c : ℝ)
    (hn : ∀ i j, 0≤G i j)
    (hp : (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-
      (G+w • completeAdjacency)).PosSemidef) : (h : ℝ)*w≤c := by
  have hq := hp.dotProduct_mulVec_nonneg (fun _ : Fin (h+1) => (1 : ℝ))
  have hrow (i : Fin (h+1)) :
      (∑ j, (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-
        (G+w • completeAdjacency) : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) i j) = c-(∑ j, G i j)-(h : ℝ)*w := by
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, completeAdjacency_degree]
    ring
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, one_mul, mul_one] at hq
  simp_rw [hrow] at hq
  have hq' : 0 ≤ ((h+1 : ℕ) : ℝ)*(c-(h : ℝ)*w)-∑ i, ∑ j, G i j := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hq
    nlinarith
  have hs : 0≤∑ i, ∑ j, G i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))
  have hm : (0 : ℝ)<((h+1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Centering and the refined graph budget combine without dropping the cross term early. -/
theorem scalar_baseline_variance_bound (m h D b w T E V : ℝ)
    (hm : 0<m) (hh : 1≤h) (hmh : m=h+1) (hb : 0≤b)
    (hw : 0≤w) (hT : 0≤T) (hcap : h*w≤2*b)
    (hbudget : m*E+4*h*w*T+m*h^2*w^2≤8*m*b^2)
    (hvariance : V≤E+w*T+D/4*w^2) :
    V≤max 8 (4+D/h^2)*b^2 := by
  have hcross : (m-4*h)*w*T≤0 := by
    have hc : m-4*h≤0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hw) hT
  have hpre : V≤8*b^2+(D/4-h^2)*w^2 := by
    have hv := mul_le_mul_of_nonneg_left hvariance hm.le
    have hc : m*V≤m*(8*b^2+(D/4-h^2)*w^2) := by nlinarith
    exact (mul_le_mul_iff_right₀ hm).mp hc
  have hhpos : 0<h := by linarith
  have hh2 : 0<h^2 := sq_pos_of_pos hhpos
  by_cases hc : D/4-h^2≤0
  · have hn := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg w)
    have ht : V≤8*b^2 := by linarith
    exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg b))
  · have hcpos : 0<D/4-h^2 := lt_of_not_ge hc
    have hs : h^2*w^2≤4*b^2 := by nlinarith [mul_nonneg hhpos.le hw]
    have hw2 : w^2≤4*b^2/h^2 := (le_div_iff₀ hh2).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hw2 hcpos.le
    have he : 8*b^2+(D/4-h^2)*(4*b^2/h^2) = (4+D/h^2)*b^2 := by
      field_simp
      ring
    have hv : V≤(4+D/h^2)*b^2 := by rw [← he]; linarith
    exact hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg b))

end APPTReview
