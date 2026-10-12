import ContinuumGeometric
open ContinuumGeometric

-- A negative center can give a strictly positive lifted boundary at integer zero.
example : (0 : ℤ) ∈ liftedBoundaryBatch 4 (-1 / 8) (1 / 2) := by
  rw [mem_liftedBoundaryBatch_iff 4 (by norm_num)]
  norm_num

-- The center boundary has zero offset and is excluded before logarithms.
example : (0 : ℤ) ∉ liftedBoundaryBatch 4 0 (1 / 4) := by
  rw [mem_liftedBoundaryBatch_iff 4 (by norm_num)]
  norm_num

-- Strict active upper range excludes its uppermost lifted boundary too.
example : (1 : ℤ) ∉ liftedBoundaryBatch 4 0 (1 / 4) := by
  rw [mem_liftedBoundaryBatch_iff 4 (by norm_num)]
  norm_num

-- The entropy interface holds at an exact exponent/coefficient endpoint rectangle.
example (x : ℝ) (n u v b : Fin 1 → ℕ) (k : ℤ)
    (hspan : ∀ i, b i + 1 ≤ u i + 2 * 2) :
    ∃ reps : Finset (PowerParams 1 1),
      reps.card ≤ 20 * (1 * (3 + 2 ^ (2 * 2 + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams 1 1, ∃ r ∈ reps,
        localGridVector x n (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) r =
        localGridVector x n (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) p := by
  exact actual_local_representatives_entropy_bound 1 1 x (by norm_num) n u v b k 2 hspan
