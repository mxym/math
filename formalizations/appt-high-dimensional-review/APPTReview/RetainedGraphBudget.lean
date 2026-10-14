import APPTReview.SpectralBaseline

open scoped BigOperators
open Matrix
namespace APPTReview

/-- The triangular estimate retains the first-row energy rather than replacing
it by the star's four-unit cap. The background cross term is not discarded. -/
theorem baseline_graph_head_budget {h : ℕ}
    (G : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) (w c : ℝ)
    (hw : 0≤w) (hG : G.IsHermitian) (hn : ∀ i j,0≤G i j)
    (hd : ∀ i,G i i=0) (hord : RowMajorAntitone G)
    (hp : (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-(G+w • completeAdjacency)).PosSemidef) :
    ((h+1:ℕ):ℝ)*((∑ i,rowEnergy G i)-rowEnergy G 0)+
      4*(h:ℝ)*w*(∑ p : UpperPair (h+1),G p.val.1 p.val.2)+
      ((h+1:ℕ):ℝ)*(h:ℝ)^2*w^2≤((h+1:ℕ):ℝ)*c^2 := by
  let B := G+w • completeAdjacency
  have hB : B.IsHermitian := hG.add (completeAdjacency_hermitian.smul (show IsSelfAdjoint w by rfl))
  have hb (i j) : 0≤B i j := by
    change 0≤G i j+w*(if i=j then 0 else 1)
    split_ifs <;> nlinarith [hn i j]
  have hsym (i j) : G i j=G j i := by
    have he := congrArg (fun M => M j i) hG.eq
    simpa [Matrix.conjTranspose_apply] using he
  have ht := triangular_degree_square G hn hsym hord
  have hsq := nonnegative_matrix_square_bound B c hB hb hp (fun _ => 1)
  have hs : (∑ i,(∑ j,B i j)^2)≤c^2*((h+1:ℕ):ℝ) := by
    simpa [Matrix.mulVec,dotProduct] using hsq
  dsimp only [B] at hs
  rw [degree_background_identity G hsym hd w] at hs
  rw [Fin.sum_univ_succ]
  nlinarith

/-- Head-retaining centered variance bound, before any entropy approximation. -/
theorem scalar_head_variance_bound (m h D b w T E H V : ℝ)
    (hm : 0<m) (hh : 1≤h) (hmh : m=h+1) (hb : 0≤b)
    (hw : 0≤w) (hT : 0≤T) (hcap : h*w≤2*b)
    (hbudget : m*(E-H)+4*h*w*T+m*h^2*w^2≤4*m*b^2)
    (hv : V≤E+w*T+D/4*w^2) :
    V≤H+max 4 (D/h^2)*b^2 := by
  have hcross : (m-4*h)*w*T≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith : m-4*h≤0) hw) hT
  have hpre : V-H≤4*b^2+(D/4-h^2)*w^2 := by
    have hh' := mul_le_mul_of_nonneg_left hv hm.le
    have ht : m*(V-H)≤m*(4*b^2+(D/4-h^2)*w^2) := by nlinarith
    exact (mul_le_mul_iff_right₀ hm).mp ht
  have hhpos : 0<h := by linarith
  have hh2 : 0<h^2 := sq_pos_of_pos hhpos
  by_cases hc : D/4-h^2≤0
  · have hn := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg w)
    have hm' := mul_le_mul_of_nonneg_right (le_max_left (4:ℝ) (D/h^2)) (sq_nonneg b)
    linarith
  · have hpos : 0<D/4-h^2 := lt_of_not_ge hc
    have hs : h^2*w^2≤4*b^2 := by nlinarith [mul_nonneg hhpos.le hw]
    have hw2 : w^2≤4*b^2/h^2 := (le_div_iff₀ hh2).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hw2 hpos.le
    have he : 4*b^2+(D/4-h^2)*(4*b^2/h^2)=(D/h^2)*b^2 := by field_simp;ring
    have hm' := mul_le_mul_of_nonneg_right (le_max_right (4:ℝ) (D/h^2)) (sq_nonneg b)
    have hbnd : V-H≤4*b^2+(D/4-h^2)*(4*b^2/h^2) := by linarith
    rw [he] at hbnd
    linarith

end APPTReview
