import APPTReview.SpectralGap
open scoped BigOperators
open Matrix
namespace APPTReview

def completeAdjacency {m : ℕ} : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i=j then 0 else 1

theorem completeAdjacency_degree {h : ℕ} (i : Fin (h+1)) :
    (∑ j, completeAdjacency i j) = (h : ℝ) := by
  have hs := sum_except_real i (1 : ℝ)
  simpa [completeAdjacency, eq_comm] using hs

theorem symmetric_degree_mass {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hsym : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0) :
    (∑ i, ∑ j, A i j) = 2*∑ p : UpperPair m, A p.val.1 p.val.2 := by
  have hs := (squareSlotEquiv m).sum_comp (fun p : Fin m × Fin m => A p.1 p.2)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  change (∑ i : Fin m, A i i) +
    ((∑ p : UpperPair m, A p.val.1 p.val.2) +
    (∑ p : UpperPair m, A p.val.2 p.val.1)) =
    ∑ p : Fin m × Fin m, A p.1 p.2 at hs
  have he : (∑ p : UpperPair m, A p.val.2 p.val.1) =
      ∑ p : UpperPair m, A p.val.1 p.val.2 := by
    apply Finset.sum_congr rfl
    intro p _
    exact hsym _ _
  rw [he] at hs
  simp only [hd, Finset.sum_const_zero, zero_add, Fintype.sum_prod_type] at hs
  linarith

theorem completeAdjacency_hermitian {m : ℕ} :
    (completeAdjacency (m:=m)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, completeAdjacency, eq_comm]

theorem degree_background_identity {h : ℕ}
    (G : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hsym : ∀ i j, G i j=G j i) (hd : ∀ i, G i i=0) (w : ℝ) :
    (∑ i, (∑ j, (G+w • completeAdjacency : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) i j)^2) =
      (∑ i, (∑ j, G i j)^2) +
      4*(h : ℝ)*w*(∑ p : UpperPair (h+1), G p.val.1 p.val.2) +
      ((h+1 : ℕ) : ℝ)*(h : ℝ)^2*w^2 := by
  have he (i : Fin (h+1)) : (∑ j, (G+w • completeAdjacency : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) i j) =
      (∑ j, G i j)+(h : ℝ)*w := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, completeAdjacency_degree]
    ring
  simp_rw [he]
  have hsq (i : Fin (h+1)) : ((∑ j, G i j)+(h : ℝ)*w)^2 =
      (∑ j, G i j)^2+2*(h : ℝ)*w*(∑ j, G i j)+(h : ℝ)^2*w^2 := by ring
  simp_rw [hsq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [symmetric_degree_mass G hsym hd]
  ring

theorem baseline_graph_refined_budget {h : ℕ}
    (G : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) (w c : ℝ)
    (hw : 0≤w) (hc : 0<c) (hn : ∀ i j, 0≤G i j)
    (hG : G.IsHermitian) (hd : ∀ i, G i i=0) (hord : RowMajorAntitone G)
    (hp : (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-(G+w • completeAdjacency)).PosSemidef) :
    ((h+1 : ℕ) : ℝ)*(∑ i, rowEnergy G i) +
      4*(h : ℝ)*w*(∑ p : UpperPair (h+1), G p.val.1 p.val.2) +
      ((h+1 : ℕ) : ℝ)*(h : ℝ)^2*w^2 ≤ 2*((h+1 : ℕ) : ℝ)*c^2 := by
  let B : Matrix (Fin (h+1)) (Fin (h+1)) ℝ := G+w • completeAdjacency
  have hB : B.IsHermitian := hG.add (completeAdjacency_hermitian.smul (show IsSelfAdjoint w by rfl))
  have hb (i j : Fin (h+1)) : 0≤B i j := by
    have hi := hn i j
    change 0 ≤ G i j + w*(if i=j then 0 else 1)
    split_ifs <;> nlinarith
  have hz (i : Fin (h+1)) : B i i=0 := by simp [B, completeAdjacency, hd]
  have hs := zero_diagonal_star_bound B c hc hb hz hp
  have hh : rowEnergy G 0 ≤ rowEnergy B 0 := by
    apply Finset.sum_le_sum
    intro j hj
    apply pow_le_pow_left₀ (hn _ _)
    dsimp [B]
    have he : (0:ℝ)≤w*completeAdjacency 0 j := by unfold completeAdjacency; split_ifs <;> positivity
    simpa using (le_add_of_nonneg_right he : G 0 j ≤ G 0 j+w*completeAdjacency 0 j)
  have hsym (i j : Fin (h+1)) : G i j=G j i := by
    have he := congrArg (fun M => M j i) hG.eq
    simpa [Matrix.conjTranspose_apply] using he
  have ht := triangular_degree_square G hn hsym hord
  have hnB := nonnegative_matrix_square_bound B c hB hb hp (fun _ => 1)
  have hnB' : (∑ i, (∑ j, B i j)^2) ≤ c^2*((h+1 : ℕ) : ℝ) := by
    simpa [Matrix.mulVec, dotProduct] using hnB
  dsimp only [B] at hnB'
  rw [degree_background_identity G hsym hd w] at hnB'
  rw [Fin.sum_univ_succ]
  have hm : (0:ℝ)≤((h+1 : ℕ) : ℝ) := by positivity
  have hhead := mul_le_mul_of_nonneg_left (hh.trans hs) hm
  nlinarith

end APPTReview
