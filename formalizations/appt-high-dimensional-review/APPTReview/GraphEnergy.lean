import APPTReview.RowArrangement
import APPTReview.PaperEntropy
open scoped BigOperators
open Matrix
namespace APPTReview

theorem rowEnergy_eq_sum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    rowEnergy A i = ∑ j, if i<j then (A i j)^2 else 0 := by
  have he : (Finset.univ.filter (fun j : Fin m => i<j)) = Finset.Ioi i := by
    ext j; simp
  rw [rowEnergy, ← he, Finset.sum_filter]

theorem rowEnergy_zero {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ) :
    rowEnergy A 0 = ∑ i : Fin h, (A 0 i.succ)^2 := by
  rw [rowEnergy_eq_sum, Fin.sum_univ_succ]
  simp

theorem zero_diagonal_star_bound {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (c : ℝ) (hc : 0<c) (hn : ∀ i j, 0≤A i j) (hd : ∀ i, A i i=0)
    (hp : (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-A).PosSemidef) :
    rowEnergy A 0 ≤ c^2 := by
  let M := c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-A
  have hs := psd_star_bound M hp (fun i : Fin h => A 0 i.succ)
    (fun i => hn _ _) (c/2) (c/2) (by linarith) ?_ ?_ ?_ ?_
  · rw [rowEnergy_zero]
    nlinarith
  · simp [M, hd] <;> linarith
  · intro i; simp [M, hd] <;> linarith
  · intro i; simp [M, Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
  · intro i j hij
    simpa [M, Matrix.one_apply, Fin.succ_inj, hij] using neg_nonpos.mpr (hn i.succ j.succ)

/-- Uniform upper-triangular square budget from two different tests of the same matrix. -/
theorem ordered_graph_energy_bound {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (c : ℝ) (hc : 0<c) (hA : A.IsHermitian) (hn : ∀ i j, 0≤A i j)
    (hd : ∀ i, A i i=0) (hord : RowMajorAntitone A)
    (hp : (c • (1 : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)-A).PosSemidef) :
    (∑ i, rowEnergy A i) ≤ 2*c^2 := by
  have hh := zero_diagonal_star_bound A c hc hn hd hp
  have hsym (i j : Fin (h+1)) : A i j=A j i := by
    have he := congrArg (fun M => M j i) hA.eq
    simpa [Matrix.conjTranspose_apply] using he
  have ht := triangular_degree_square A hn hsym hord
  have hs := nonnegative_matrix_square_bound A c hA hn hp (fun _ => 1)
  have hs' : (∑ i, (∑ j, A i j)^2) ≤ c^2*((h+1 : ℕ) : ℝ) := by
    simpa [Matrix.mulVec, dotProduct] using hs
  have hm : (0:ℝ)<((h+1 : ℕ) : ℝ) := by positivity
  have htail : (∑ i : Fin h, rowEnergy A i.succ) ≤ c^2 := by nlinarith
  rw [Fin.sum_univ_succ]
  linarith

end APPTReview
