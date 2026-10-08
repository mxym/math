import BapatN200Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Intentionally false: one published b-coordinate has squared norm 421.
example : ∀ i : Fin 200,
    let z := BapatRankTwo.Exact.vectorAt BapatRankTwo.N200.vectors i.val
    z.2.re * z.2.re + z.2.im * z.2.im ≤ (400 : ℤ) := by
  decide +kernel
