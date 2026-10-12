import GaussianCoordinateSplit
import GaussianRotationalMomentIdentity
import GaussianPolyhedralGraphFlux

/-! A polyhedral epigraph is one winning cell of an explicitly lifted score
family. The other cells are the exposed base facets capped by a Gaussian
half-line. These identities retain the actual Gaussian product law. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def graphScores (v : Fin k → Space d) : Fin (k+1) → Space (d+1) :=
  Fin.cons (joinCoordinate 1 0) (fun i => joinCoordinate 0 (v i))

noncomputable def graphPrices (b : Fin k → ℝ) : Fin (k+1) → ℝ := Fin.cons 0 b

@[simp] lemma graphScores_zero (v : Fin k → Space d) : graphScores v 0 = joinCoordinate 1 0 := rfl
@[simp] lemma graphScores_succ (v : Fin k → Space d) (i : Fin k) :
    graphScores v i.succ = joinCoordinate 0 (v i) := rfl
@[simp] lemma graphPrices_zero (b : Fin k → ℝ) : graphPrices b 0 = 0 := rfl
@[simp] lemma graphPrices_succ (b : Fin k → ℝ) (i : Fin k) : graphPrices b i.succ = b i := rfl

lemma graphScores_injective (v : Fin k → Space d) (hv : Function.Injective v) :
    Function.Injective (graphScores v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => have h := congrArg (fun x : Space (d+1) => x 0) hij; simp at h
  | succ i =>
    cases j using Fin.cases with
    | zero => have h := congrArg (fun x : Space (d+1) => x 0) hij; simp at h
    | succ j =>
      apply congrArg Fin.succ
      apply hv
      ext l
      exact congrArg (fun x : Space (d+1) => x l.succ) hij

lemma scoreMax_lt_iff (v : Fin k → Space d) (b : Fin k → ℝ) (y : Space d) (t : ℝ) :
    scoreMax v b y < t ↔ ∀ i, ⟪v i, y⟫ - b i < t := by
  simp [scoreMax, Finset.sup'_lt_iff]

theorem graph_winning_zero (v : Fin k → Space d) (b : Fin k → ℝ)
    (y : Space d) (t : ℝ) :
    joinCoordinate t y ∈ winningCell (graphScores v) (graphPrices b) 0 ↔ scoreMax v b y < t := by
  rw [scoreMax_lt_iff]
  constructor
  · intro h i
    have hh := h i.succ (Fin.succ_ne_zero i)
    simpa [inner_joinCoordinate] using hh
  · intro h j hj
    cases j using Fin.cases with
    | zero => exact False.elim (hj rfl)
    | succ j => simpa [inner_joinCoordinate] using h j

theorem graph_winning_succ (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (y : Space d) (t : ℝ) :
    joinCoordinate t y ∈ winningCell (graphScores v) (graphPrices b) i.succ ↔
      y ∈ winningCell v b i ∧ t < ⟪v i, y⟫ - b i := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hh := h j.succ (fun he => hj (Fin.succ_inj.mp he))
      simpa [inner_joinCoordinate] using hh
    · have hh := h 0 (Ne.symm (Fin.succ_ne_zero i))
      simpa [inner_joinCoordinate] using hh
  · rintro ⟨hbase, ht⟩ j hj
    cases j using Fin.cases with
    | zero => simpa [inner_joinCoordinate] using ht
    | succ j =>
      have hh := hbase j (fun he => hj (congrArg Fin.succ he))
      simpa [inner_joinCoordinate] using hh

noncomputable def graphWinningPartition (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) : FractionalPartition (d+1) (k+1) :=
  winningPartition (graphScores v) (graphPrices b) (graphScores_injective v hv)

lemma winning_moment_coordinate {n m : ℕ} [NeZero m] (v : Fin m → Space n)
    (b : Fin m → ℝ) (hv : Function.Injective v) (i : Fin m) (j : Fin n) :
    (winningPartition v b hv).moment i j =
      ∫ x, (winningCell v b i).indicator (fun x : Space n => x j) x ∂gaussian n := by
  have h := (winningPartition v b hv).inner_moment i (EuclideanSpace.basisFun (Fin n) ℝ j)
  simp only [PiLp.inner_apply] at h
  have hi (x : Space n) : ⟪EuclideanSpace.basisFun (Fin n) ℝ j,x⟫ = x j := by simp [PiLp.inner_apply]
  have h' := (winningPartition v b hv).inner_moment i (EuclideanSpace.basisFun (Fin n) ℝ j)
  simp_rw [hi] at h'
  rw [h']
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ winningCell v b i <;> simp [winningPartition,hx]

end GaussianMeasureBridge
