import EntropyWakhare.Core

namespace EntropyRoot

theorem p1pos : (0 : ℚ) < A (1/5) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
theorem p1bound : B (1/5) < (117/125 : ℚ)*A (1/5) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

theorem p2pos : (0 : ℚ) < A (2/5) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
theorem p2bound : (937/1000 : ℚ)*A (2/5) < B (2/5) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

theorem p3pos : (0 : ℚ) < A (3/5) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
theorem p3bound : B (3/5) < (117/125 : ℚ)*A (3/5) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

theorem p4pos : (0 : ℚ) < A (2/3) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
theorem p4bound : (937/1000 : ℚ)*A (2/3) < B (2/3) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

theorem p5pos : (0 : ℚ) < A (4/5) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
theorem p5bound : B (4/5) < (117/125 : ℚ)*A (4/5) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

end EntropyRoot
