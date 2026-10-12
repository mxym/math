import HydrologyTree.WeightedEnergy

/-! Strict positivity of the constructed physical tree energy.
Connectedness is proved from the actual parent inequalities, not assumed. -/
open Matrix
noncomputable section
namespace HydrologyTree

/-- A value constant across every edge and zero at the root vanishes everywhere. -/
theorem zero_of_tree_edge_equalities {n : ℕ} (t : OrderedTree n) (z : VertexValues n)
    (hz0 : z 0 = 0) (hzedge : ∀ e : Fin n, z (t.parent e) = z e.succ) : z = 0 := by
  funext v
  change z v = 0
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hv : v = 0
    · rwa [hv]
    · let e : Fin n := v.pred hv
      have he : e.succ = v := Fin.succ_pred v hv
      have hlt : (t.parent e).val < v.val := by
        rw [← he]
        exact Nat.lt_succ_of_le (t.parent_le e)
      rw [← he, ← hzedge e]
      exact ih (t.parent e) hlt

def groundedTreeEnergy {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ) (ell : ℝ)
    (z : VertexValues n) : ℝ := ell*(z 0)^2 + ∑ e : Fin n, g e*(z (t.parent e)-z e.succ)^2

/-- Exact strict positivity, also including the one-vertex tree. -/
theorem groundedTreeEnergy_pos {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ) (ell : ℝ)
    (hg : ∀ e, 0 < g e) (hell : 0 < ell) (z : VertexValues n) (hz : z ≠ 0) :
    0 < groundedTreeEnergy t g ell z := by
  have hterms (e : Fin n) : 0 ≤ g e*(z (t.parent e)-z e.succ)^2 :=
    mul_nonneg (le_of_lt (hg e)) (sq_nonneg _)
  have hsum : 0 ≤ ∑ e : Fin n, g e*(z (t.parent e)-z e.succ)^2 :=
    Finset.sum_nonneg (fun e _ => hterms e)
  have hroot : 0 ≤ ell*(z 0)^2 := mul_nonneg hell.le (sq_nonneg _)
  by_contra h
  have ht : ell*(z 0)^2 + (∑ e : Fin n, g e*(z (t.parent e)-z e.succ)^2) ≤ 0 :=
    le_of_not_gt h
  have hr0 : ell*(z 0)^2 = 0 := by linarith
  have hz0 : z 0 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hr0).resolve_left (ne_of_gt hell))
  have hs0 : (∑ e : Fin n, g e*(z (t.parent e)-z e.succ)^2) = 0 := by linarith
  apply hz
  apply zero_of_tree_edge_equalities t z hz0
  intro e
  have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterms j)
    (Finset.mem_univ e)
  rw [hs0] at hle
  have he0 := le_antisymm hle (hterms e)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he0).resolve_left (ne_of_gt (hg e))))

/-- A positive-leak, positive-internal-rate physical tree has a positive-definite
weighted negative generator, with the weighting constructed explicitly. -/
theorem weightedNegativeGenerator_posDef {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (hf : ∀ e : Fin n, 0 < x.2 e) : (weightedNegativeGenerator t x).PosDef := by
  have hane : ∀ e : Fin n, x.1 e.succ ≠ 0 := fun e => ne_of_gt (ha e)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (weightedNegativeGenerator_isHermitian t x hane)
  intro z hz
  simp only [star_trivial]
  rw [weightedNegativeGenerator_energy t x hane]
  exact groundedTreeEnergy_pos t (fun e => x.2 e * balanceWeight t x (t.parent e))
    (x.1 0) (fun e => mul_pos (hf e) (balanceWeight_pos t x ha hf _)) hell z hz

end HydrologyTree
