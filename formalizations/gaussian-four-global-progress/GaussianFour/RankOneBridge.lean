import GaussianFour.RankOneReduction
import GaussianFour.PermutationOrder
import GaussianFour.CollinearTransport

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace MatrixOrder Matrix

namespace GaussianFour
open GaussianMeasureBridge

/-- A rank-one family of four injective actual score vectors admits a unit
axis and a permutation with strictly increasing scalar coefficients. -/
theorem exists_unit_strictMono_rankOne_representation {d : ℕ}
    (v : Fin 4 → Space d) (hrank : (scoreGram v).rank ≤ 1)
    (hinj : Function.Injective v) :
    ∃ (u : Space d) (a : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)),
      ‖u‖ = 1 ∧ StrictMono a ∧ ∀ i, v (e i) = a i • u := by
  obtain ⟨u₀, hrep₀⟩ := scoreGram_rank_le_one_collinear v hrank
  let c : Fin 4 → ℝ := fun i => Classical.choose (hrep₀ i)
  have hc : ∀ i, v i = c i • u₀ := by
    intro i
    exact Classical.choose_spec (hrep₀ i)
  have hu₀ : u₀ ≠ 0 := by
    intro hz
    have hall : ∀ i, v i = 0 := by
      intro i
      rw [hc i, hz, smul_zero]
    have : v (0 : Fin 4) = v (1 : Fin 4) := by
      rw [hall, hall]
    exact Fin.zero_ne_one (hinj this)
  have hnorm : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀
  let u : Space d := (‖u₀‖)⁻¹ • u₀
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm]
    exact inv_mul_cancel₀ hnorm.ne'
  let a₀ : Fin 4 → ℝ := fun i => c i * ‖u₀‖
  have hrep : ∀ i, v i = a₀ i • u := by
    intro i
    calc
      v i = c i • u₀ := hc i
      _ = (c i * ‖u₀‖ * (‖u₀‖)⁻¹) • u₀ := by
        rw [mul_assoc, mul_inv_cancel₀ hnorm.ne', mul_one]
      _ = (c i * ‖u₀‖) • ((‖u₀‖)⁻¹ • u₀) := by
        rw [smul_smul]
  have ha₀ : Function.Injective a₀ := by
    intro i j hij
    apply hinj
    calc
      v i = a₀ i • u := hrep i
      _ = a₀ j • u := by rw [hij]
      _ = v j := (hrep j).symm
  obtain ⟨e, he⟩ := exists_perm_strictMono_of_injective a₀ ha₀
  refine ⟨u, a₀ ∘ e, e, hu, he, ?_⟩
  intro i
  simpa [Function.comp_apply] using hrep (e i)

/-- Winning cells are equivariant under a simultaneous relabeling of scores,
prices, and the winning label. -/
lemma winningCell_perm (v : Fin 4 → Space d) (p : Fin 4 → ℝ)
    (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    winningCell (fun j => v (e j)) (fun j => p (e j)) i =
      winningCell v p (e i) := by
  ext x
  constructor
  · intro hx j hj
    have hj' : e.symm j ≠ i := by
      intro h
      apply hj
      exact e.symm.injective (by simpa using h)
    simpa [winningCell] using hx (e.symm j) hj'
  · intro hx j hj
    have hj' : e j ≠ e i := by
      intro h
      exact hj (e.injective h)
    simpa [winningCell] using hx (e j) hj'

/-- The rank-one representation preserves actual balanced masses and
self-moment equations after ordering the labels. The final conjunct is the
already-proved one-dimensional Gaussian spectral obstruction. -/
theorem exists_rankOne_ordered_actual_obstruction {d : ℕ}
    (v : Fin 4 → Space d) (p : Fin 4 → ℝ)
    (hrank : (scoreGram v).rank ≤ 1) (hinj : Function.Injective v)
    (hm : ∀ i, ((gaussian d) (winningCell v p i)).toReal = 1 / 4)
    (hself : ∀ i, v i = ∫ x in winningCell v p i, x ∂gaussian d) :
    ∃ (u : Space d) (a : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)),
      ‖u‖ = 1 ∧ StrictMono a ∧
      (∀ i, ((gaussian d) (winningCell (fun j => a j • u)
        (fun j => p (e j)) i)).toReal = 1 / 4) ∧
      (∀ i, a i • u = ∫ x in winningCell (fun j => a j • u)
        (fun j => p (e j)) i, x ∂gaussian d) ∧
      ¬ (∀ z : Fin 4 → ℝ, (∑ i, z i) = 0 →
        scalarFacetForm a (fun j => p (e j)) z ≤ ∑ i, z i ^ 2) := by
  obtain ⟨u, a, e, hu, ha, hrep⟩ :=
    exists_unit_strictMono_rankOne_representation v hrank hinj
  let v' : Fin 4 → Space d := fun i => v (e i)
  let p' : Fin 4 → ℝ := fun i => p (e i)
  have hrep' : ∀ i, v' i = a i • u := by
    intro i
    simpa [v', p'] using hrep i
  have hcell : ∀ i, winningCell (fun j => a j • u) p' i =
      winningCell v' p' i := by
    intro i
    ext x
    simp only [winningCell, v', p', hrep']
  have hm' : ∀ i, ((gaussian d) (winningCell (fun j => a j • u) p' i)).toReal = 1 / 4 := by
    intro i
    calc
      ((gaussian d) (winningCell (fun j => a j • u) p' i)).toReal =
          ((gaussian d) (winningCell v' p' i)).toReal := by rw [hcell i]
      _ = ((gaussian d) (winningCell v p (e i))).toReal := by
        rw [winningCell_perm v p e i]
      _ = 1 / 4 := hm (e i)
  have hself' : ∀ i, a i • u =
      ∫ x in winningCell (fun j => a j • u) p' i, x ∂gaussian d := by
    intro i
    calc
      a i • u = v' i := (hrep' i).symm
      _ = v (e i) := rfl
      _ = ∫ x in winningCell v p (e i), x ∂gaussian d := hself (e i)
      _ = ∫ x in winningCell v' p' i, x ∂gaussian d := by
        rw [winningCell_perm v p e i]
      _ = ∫ x in winningCell (fun j => a j • u) p' i, x ∂gaussian d := by
        rw [hcell i]
  refine ⟨u, a, e, hu, ha, hm', hself', ?_⟩
  exact no_ordered_collinear_selfMoment_spectral_bound u hu a p' ha hm' hself'

end GaussianFour
