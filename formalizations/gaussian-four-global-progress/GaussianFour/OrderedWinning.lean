import GaussianFour.QuartileIntervals

/-! Four ordered affine scores with actual Gaussian winning cells.
Positive cell masses force strictly ordered adjacent crossing points. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianFour
open GaussianMeasureBridge

noncomputable def scalarScore (a p : Fin 4 → ℝ) (i : Fin 4) (x : ℝ) : ℝ := a i * x - p i

def scalarWinning (a p : Fin 4 → ℝ) (i : Fin 4) : Set ℝ :=
  {x | ∀ j, j ≠ i → scalarScore a p j x < scalarScore a p i x}

noncomputable def adjacentCut (a p : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  (p i.succ - p i.castSucc) / (a i.succ - a i.castSucc)

def openIntervalCells (u v w : ℝ) : Fin 4 → Set ℝ := ![Iio u, Ioo u v, Ioo v w, Ioi w]

lemma openIntervalCells_mass (u v w : ℝ) (i : Fin 4) :
    scalarMass (openIntervalCells u v w i) = scalarMass (intervalCells u v w i) := by
  fin_cases i <;> simp [openIntervalCells, intervalCells, scalarMass_Iio, scalarMass_Ioo]

lemma openIntervalCells_moment (u v w : ℝ) (i : Fin 4) :
    scalarMoment (openIntervalCells u v w i) = scalarMoment (intervalCells u v w i) := by
  fin_cases i <;> simp [openIntervalCells, intervalCells, scalarMoment_Iio, scalarMoment_Ioo]

lemma adjacentCut_lt_iff (a p : Fin 4 → ℝ) (ha : StrictMono a) (i : Fin 3) (x : ℝ) :
    adjacentCut a p i < x ↔ scalarScore a p i.castSucc x < scalarScore a p i.succ x := by
  have hpos : 0 < a i.succ - a i.castSucc := sub_pos.mpr (ha (by change i.val < i.val + 1; omega))
  rw [adjacentCut, div_lt_iff₀ hpos]
  unfold scalarScore
  constructor <;> intro h <;> nlinarith

lemma lt_adjacentCut_iff (a p : Fin 4 → ℝ) (ha : StrictMono a) (i : Fin 3) (x : ℝ) :
    x < adjacentCut a p i ↔ scalarScore a p i.succ x < scalarScore a p i.castSucc x := by
  have hpos : 0 < a i.succ - a i.castSucc := sub_pos.mpr (ha (by change i.val < i.val + 1; omega))
  rw [adjacentCut, lt_div_iff₀ hpos]
  unfold scalarScore
  constructor <;> intro h <;> nlinarith

lemma scalarWinning_nonempty {a p : Fin 4 → ℝ} {i : Fin 4}
    (hm : scalarMass (scalarWinning a p i) = 1 / 4) : (scalarWinning a p i).Nonempty := by
  by_contra hn
  have hs := Set.not_nonempty_iff_eq_empty.mp hn
  rw [hs] at hm
  norm_num [scalarMass] at hm

/-- No absent middle cell can be hidden inside the balanced-price hypothesis. -/
theorem balanced_adjacentCuts_strict {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (hm : ∀ i, scalarMass (scalarWinning a p i) = 1 / 4) :
    adjacentCut a p 0 < adjacentCut a p 1 ∧ adjacentCut a p 1 < adjacentCut a p 2 := by
  obtain ⟨x, hx⟩ := scalarWinning_nonempty (hm 1)
  obtain ⟨y, hy⟩ := scalarWinning_nonempty (hm 2)
  have hx0 := (adjacentCut_lt_iff a p ha 0 x).2 (hx 0 (by decide))
  have hx1 := (lt_adjacentCut_iff a p ha 1 x).2 (hx 2 (by decide))
  have hy1 := (adjacentCut_lt_iff a p ha 1 y).2 (hy 1 (by decide))
  have hy2 := (lt_adjacentCut_iff a p ha 2 y).2 (hy 3 (by decide))
  exact ⟨hx0.trans hx1, hy1.trans hy2⟩

/-- The entire winning cells, not just their masses, are ordered open intervals. -/
theorem scalarWinning_eq_intervals {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (h01 : adjacentCut a p 0 < adjacentCut a p 1)
    (h12 : adjacentCut a p 1 < adjacentCut a p 2) (i : Fin 4) :
    scalarWinning a p i = openIntervalCells (adjacentCut a p 0)
      (adjacentCut a p 1) (adjacentCut a p 2) i := by
  ext x
  have h0 := adjacentCut_lt_iff a p ha 0 x
  have h1 := adjacentCut_lt_iff a p ha 1 x
  have h2 := adjacentCut_lt_iff a p ha 2 x
  have g0 := lt_adjacentCut_iff a p ha 0 x
  have g1 := lt_adjacentCut_iff a p ha 1 x
  have g2 := lt_adjacentCut_iff a p ha 2 x
  fin_cases i
  · change (∀ j, j ≠ 0 → scalarScore a p j x < scalarScore a p 0 x) ↔ x < adjacentCut a p 0
    constructor
    · intro hx; exact g0.2 (hx 1 (by decide))
    · intro hx j hj
      have s0 := g0.1 hx
      have s1 := g1.1 (hx.trans h01)
      have s2 := g2.1 ((hx.trans h01).trans h12)
      fin_cases j <;> simp_all [scalarScore] <;> linarith
  · change (∀ j, j ≠ 1 → scalarScore a p j x < scalarScore a p 1 x) ↔
      adjacentCut a p 0 < x ∧ x < adjacentCut a p 1
    constructor
    · intro hx; exact ⟨h0.2 (hx 0 (by decide)), g1.2 (hx 2 (by decide))⟩
    · rintro ⟨hx0, hx1⟩ j hj
      have s0 := h0.1 hx0
      have s1 := g1.1 hx1
      have s2 := g2.1 (hx1.trans h12)
      fin_cases j <;> simp_all [scalarScore] <;> linarith
  · change (∀ j, j ≠ 2 → scalarScore a p j x < scalarScore a p 2 x) ↔
      adjacentCut a p 1 < x ∧ x < adjacentCut a p 2
    constructor
    · intro hx; exact ⟨h1.2 (hx 1 (by decide)), g2.2 (hx 3 (by decide))⟩
    · rintro ⟨hx1, hx2⟩ j hj
      have s0 := h0.1 (h01.trans hx1)
      have s1 := h1.1 hx1
      have s2 := g2.1 hx2
      fin_cases j <;> simp_all [scalarScore] <;> linarith
  · change (∀ j, j ≠ 3 → scalarScore a p j x < scalarScore a p 3 x) ↔ adjacentCut a p 2 < x
    constructor
    · intro hx; exact h2.2 (hx 2 (by decide))
    · intro hx j hj
      have s0 := h0.1 (h01.trans (h12.trans hx))
      have s1 := h1.1 (h12.trans hx)
      have s2 := h2.1 hx
      fin_cases j <;> simp_all [scalarScore] <;> linarith

/-- The crossing points are forced by actual balance, without assuming any quantiles. -/
theorem balanced_scalar_cut_quartiles {a p : Fin 4 → ℝ} (ha : StrictMono a)
    (hm : ∀ i, scalarMass (scalarWinning a p i) = 1 / 4) :
    adjacentCut a p 0 = -quarterQuantile ∧ adjacentCut a p 1 = 0 ∧
    adjacentCut a p 2 = quarterQuantile := by
  obtain ⟨h01, h12⟩ := balanced_adjacentCuts_strict ha hm
  apply equal_mass_interval_thresholds h01.le
  intro i
  have h := hm i
  rw [scalarWinning_eq_intervals ha h01 h12, openIntervalCells_mass] at h
  exact h

end GaussianFour
