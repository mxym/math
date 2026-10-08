import Algebra

-- Must fail: the ordered facet gap has the opposite sign.
example : (1 : ℝ) - 2 > 0 := by
  norm_num
