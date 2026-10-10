import GaussianNoTies
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge

namespace GaussianFour

variable {d k : ℕ}

/-- A nonempty strict winning cell whose score vector is strictly between two
others must have strictly smaller price than the corresponding interpolation.
This is a pointwise geometric theorem, not a regularity assumption. -/
theorem interpolated_price_strict_of_winning_nonempty
    (v : Fin k → Space d) (b : Fin k → ℝ) (i j l : Fin k)
    (hil : i ≠ l) (hjl : j ≠ l) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hv : v l = a • v i + (1-a) • v j)
    (hne : (winningCell v b l).Nonempty) :
    b l < a*b i+(1-a)*b j := by
  obtain ⟨x,hx⟩ := hne
  have hi := mul_lt_mul_of_pos_left (hx i hil) ha
  have hj := mul_lt_mul_of_pos_left (hx j hjl) (sub_pos.mpr ha1)
  have hvx : ⟪v l,x⟫ = a*⟪v i,x⟫+(1-a)*⟪v j,x⟫ := by
    rw [hv,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  nlinarith

lemma winning_nonempty_of_mass_pos (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (hp : 0 < (gaussian d).real (winningCell v b i)) :
    (winningCell v b i).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro he
  simpa [he] using hp

/-- Positive actual Gaussian mass excludes the price relation which would
produce a codimension-one triple tie among collinear score vectors. -/
theorem interpolated_price_strict_of_gaussian_mass_pos
    (v : Fin k → Space d) (b : Fin k → ℝ) (i j l : Fin k)
    (hil : i ≠ l) (hjl : j ≠ l) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hv : v l = a • v i + (1-a) • v j)
    (hp : 0 < (gaussian d).real (winningCell v b l)) :
    b l < a*b i+(1-a)*b j :=
  interpolated_price_strict_of_winning_nonempty v b i j l hil hjl a ha ha1 hv
    (winning_nonempty_of_mass_pos v b l hp)

/-- On the equality hyperplane of the two endpoint scores, the middle score
is strictly higher. Thus that hyperplane cannot carry a three-way tie. -/
theorem middle_score_strict_on_endpoint_tie
    (v : Fin k → Space d) (b : Fin k → ℝ) (i j l : Fin k)
    (hil : i ≠ l) (hjl : j ≠ l) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hv : v l = a • v i + (1-a) • v j)
    (hp : 0 < (gaussian d).real (winningCell v b l))
    (x : Space d) (hij : ⟪v i,x⟫-b i = ⟪v j,x⟫-b j) :
    ⟪v i,x⟫-b i < ⟪v l,x⟫-b l := by
  have hprice := interpolated_price_strict_of_gaussian_mass_pos
    v b i j l hil hjl a ha ha1 hv hp
  have hvx : ⟪v l,x⟫ = a*⟪v i,x⟫+(1-a)*⟪v j,x⟫ := by
    rw [hv,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  nlinarith

end GaussianFour
