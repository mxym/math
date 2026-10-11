import GaussianFour.TripleTie

/-! Nonempty strict cells exclude proportional affine score differences. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

theorem no_proportional_differences_of_nonempty
    (v : Fin k → Space d) (b : Fin k → ℝ) (i j l : Fin k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : (winningCell v b i).Nonempty)
    (hj : (winningCell v b j).Nonempty)
    (hl : (winningCell v b l).Nonempty) (r : ℝ) :
    ¬ (∀ x, (⟪v i,x⟫ - b i) - (⟪v l,x⟫ - b l) =
      r * ((⟪v i,x⟫ - b i) - (⟪v j,x⟫ - b j))) := by
  intro h
  obtain ⟨x, hx⟩ := hi
  obtain ⟨y, hy⟩ := hj
  obtain ⟨z, hz⟩ := hl
  have hxi := hx j (Ne.symm hij)
  have hxl := hx l (Ne.symm hil)
  have hyi := hy i hij
  have hyl := hy l (Ne.symm hjl)
  have hzi := hz i hil
  have hzj := hz j hjl
  have hr : 0 < r := by
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (sub_pos.mpr hxi).le
    nlinarith [h x]
  have hr1 : r < 1 := by
    by_contra hn
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
      (sub_pos.mpr hyi).le
    nlinarith [h y]
  have hp := mul_pos hr (sub_pos.mpr hzj)
  have hq := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hzi)
  nlinarith [h z]

/-- All masses here are those of the actual standard Gaussian winning cells. -/
theorem no_proportional_differences_of_positive_masses
    (v : Fin k → Space d) (b : Fin k → ℝ) (i j l : Fin k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hmass : ∀ t, 0 < (gaussian d).real (winningCell v b t)) (r : ℝ) :
    ¬ (∀ x, (⟪v i,x⟫ - b i) - (⟪v l,x⟫ - b l) =
      r * ((⟪v i,x⟫ - b i) - (⟪v j,x⟫ - b j))) :=
  no_proportional_differences_of_nonempty v b i j l hij hil hjl
    (winning_nonempty_of_mass_pos v b i (hmass i))
    (winning_nonempty_of_mass_pos v b j (hmass j))
    (winning_nonempty_of_mass_pos v b l (hmass l)) r

end GaussianFour
