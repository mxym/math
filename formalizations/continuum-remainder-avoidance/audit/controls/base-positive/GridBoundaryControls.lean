import ContinuumGeometric

open ContinuumGeometric

-- A negative dyadic coefficient exponent and an exact ZERO lifted-grid crossing.
example : cutSign (evalCut (gridCrossingCut (1 / 2) (1 / 4) (-1))
    (1, Real.log 1)) = .zero := by
  rw [← power_grid_cut_sign (1 / 2) (1 / 4) 1 1 (-1)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.rpow_one]

-- The left-closed/right-open key convention at, before and after the boundary.
example : periodicGridKey 4 (1 / 4) = 1 := by
  norm_num [periodicGridKey]

example : periodicGridKey 4 (7 / 32) = 0 := by
  norm_num [periodicGridKey]

example : periodicGridKey 4 (9 / 32) = 1 := by
  norm_num [periodicGridKey]

-- The log-grid bridge is exact for the actual dyadic point at exponent endpoint 2.
example : cutSign (evalCut (gridCrossingCut (dyadic 1) (1 / 8) (-1))
    (logPowerParams
      ((⟨2, by norm_num⟩ : Set.Icc (1 : ℝ) 2), (⟨1, by norm_num⟩ : Set.Icc (1 : ℝ) 2)))) = .zero := by
  have h := actual_grid_boundary_sign 1 2 (1 / 8) 1 4 (-1) 1
    (by norm_num)
    ((⟨2, by norm_num⟩ : Set.Icc (1 : ℝ) 2), (⟨1, by norm_num⟩ : Set.Icc (1 : ℝ) 2))
    (by norm_num)
  norm_num [powerPoint, dyadic, Real.rpow_two] at h
  simpa [dyadic, cutSign] using h.symm
