import GaussianGraphVectorFlux
import GaussianMomentSymmetry

/-! A winning cell whose inward normals have positive first coordinate is a
polyhedral epigraph. The full actual Gaussian moment therefore equals a sum
of its score-difference normals with explicit, nonnegative integral weights. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def tailCoordinates (x : Space (d+1)) : Space d :=
  WithLp.toLp 2 (fun j => x j.succ)

lemma joinCoordinate_eta (x : Space (d+1)) : joinCoordinate (x 0) (tailCoordinates x) = x := by
  ext i
  cases i using Fin.cases <;> rfl

lemma inner_coordinate_split (x : Space (d+1)) (t : ℝ) (y : Space d) :
    ⟪x, joinCoordinate t y⟫ = x 0 * t + ⟪tailCoordinates x, y⟫ := by
  conv_lhs => rw [← joinCoordinate_eta x]
  exact inner_joinCoordinate _ _ _ _

noncomputable def inwardCoordinate (v : Fin (k+1) → Space (d+1)) (i : Fin k) : ℝ :=
  v 0 0 - v i.succ 0

noncomputable def winningGraphSlopes (v : Fin (k+1) → Space (d+1)) : Fin k → Space d :=
  fun i => (inwardCoordinate v i)⁻¹ • (tailCoordinates (v i.succ) - tailCoordinates (v 0))

noncomputable def winningGraphPrices (v : Fin (k+1) → Space (d+1))
    (b : Fin (k+1) → ℝ) : Fin k → ℝ := fun i => (b i.succ - b 0) / inwardCoordinate v i

lemma winning_graph_inequality (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (i : Fin k) (hi : 0 < inwardCoordinate v i) (t : ℝ) (y : Space d) :
    (⟪v i.succ, joinCoordinate t y⟫ - b i.succ < ⟪v 0, joinCoordinate t y⟫ - b 0) ↔
      ⟪winningGraphSlopes v i, y⟫ - winningGraphPrices v b i < t := by
  have he : ⟪winningGraphSlopes v i,y⟫ - winningGraphPrices v b i =
      (⟪tailCoordinates (v i.succ), y⟫ - ⟪tailCoordinates (v 0),y⟫ - (b i.succ - b 0)) /
        inwardCoordinate v i := by
    simp only [winningGraphSlopes, winningGraphPrices, real_inner_smul_left, inner_sub_left,
      div_eq_mul_inv]
    ring
  rw [he, div_lt_iff₀ hi, inner_coordinate_split, inner_coordinate_split]
  unfold inwardCoordinate
  constructor <;> intro h <;> nlinarith

theorem winning_cell_as_graph (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hv : ∀ i, 0 < inwardCoordinate v i) :
    winningCell v b 0 = winningCell (graphScores (winningGraphSlopes v))
      (graphPrices (winningGraphPrices v b)) 0 := by
  ext x
  rw [← joinCoordinate_eta x, graph_winning_zero, scoreMax_lt_iff]
  constructor
  · intro hx i
    exact (winning_graph_inequality v b i (hv i) _ _).mp (hx i.succ (Fin.succ_ne_zero i))
  · intro hx j hj
    cases j using Fin.cases with
    | zero => exact False.elim (hj rfl)
    | succ j => exact (winning_graph_inequality v b j (hv j) _ _).mpr (hx j)

lemma winning_graph_normal (v : Fin (k+1) → Space (d+1)) (i : Fin k)
    (hi : 0 < inwardCoordinate v i) :
    joinCoordinate 1 (-winningGraphSlopes v i) =
      (inwardCoordinate v i)⁻¹ • (v 0 - v i.succ) := by
  ext j
  cases j using Fin.cases with
  | zero =>
    change 1 = (inwardCoordinate v i)⁻¹ * (v 0 0 - v i.succ 0)
    exact (inv_mul_cancel₀ hi.ne').symm
  | succ j =>
    simp [winningGraphSlopes, tailCoordinates, sub_eq_add_neg, mul_add]

/-- Actual Bochner moment of the original winning cell. The displayed weights
are finite Gaussian face-density integrals divided by a positive normal
coordinate; no unproved Gaussian flux premise occurs. -/
theorem gaussian_winning_cell_graph_flux (v : Fin (k+1) → Space (d+1)) (b : Fin (k+1) → ℝ)
    (hv : ∀ i, 0 < inwardCoordinate v i) (hs : Function.Injective (winningGraphSlopes v)) :
    rawWinningMoment v b 0 = ∑ i,
      (graphFacetDensity (winningGraphSlopes v) (winningGraphPrices v b) i / inwardCoordinate v i) •
        (v 0 - v i.succ) := by
  have he : rawWinningMoment v b 0 =
      (graphWinningPartition (winningGraphSlopes v) (winningGraphPrices v b) hs).moment 0 := by
    rw [graphWinningPartition, ← rawWinningMoment_eq]
    unfold rawWinningMoment
    rw [winning_cell_as_graph v b hv]
  rw [he, gaussian_polyhedral_graph_vector_flux]
  apply Finset.sum_congr rfl
  intro i _
  rw [winning_graph_normal v i (hv i), smul_smul, div_eq_mul_inv]

end GaussianMeasureBridge
