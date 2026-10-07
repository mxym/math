import ContinuumGeometric.Planar

open ContinuumGeometric

/-- The statement unfolds to the exact owner interface without added hypotheses. -/
example : ∀ (m : ℕ) (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ),
    lo.1 ≤ hi.1 → lo.2 ≤ hi.2 →
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧
      reps.card ≤ 20 * (m + 5) ^ 2 ∧
      ∀ p : ℝ × ℝ, inRectangle lo hi p →
        ∃ r ∈ reps, ∀ i : Fin m,
          cutSign (evalCut (cuts i) r) = cutSign (evalCut (cuts i) p) :=
  arrangementRepresentativeBound

/-- Arbitrarily many identically zero cuts on a rectangle collapsed to a point. -/
example (m : ℕ) : ∃ reps : Finset (ℝ × ℝ),
    (∀ r ∈ reps, inRectangle (0,0) (0,0) r) ∧ reps.card ≤ 20*(m+5)^2 ∧
    ∀ p : ℝ × ℝ, inRectangle (0,0) (0,0) p →
      ∃ r ∈ reps, ∀ i : Fin m,
        cutSign (evalCut ((fun _ : Fin m => (0,0,0)) i) r) =
        cutSign (evalCut ((fun _ : Fin m => (0,0,0)) i) p) := by
  exact arrangementRepresentativeBound m (fun _ => (0,0,0)) (0,0) (0,0)
    (by norm_num) (by norm_num)

/-- Parallel/coincident cuts, including exact boundary zeros, on a collapsed segment. -/
example : ∃ reps : Finset (ℝ × ℝ),
    (∀ r ∈ reps, inRectangle (0,0) (1,0) r) ∧ reps.card ≤ 20*(3+5)^2 ∧
    ∀ p : ℝ × ℝ, inRectangle (0,0) (1,0) p →
      ∃ r ∈ reps, ∀ i : Fin 3,
        cutSign (evalCut ((fun i : Fin 3 => if i.val < 2 then ((1,0,0) : AffineCut) else (1,0,-1)) i) r) =
        cutSign (evalCut ((fun i : Fin 3 => if i.val < 2 then ((1,0,0) : AffineCut) else (1,0,-1)) i) p) := by
  exact arrangementRepresentativeBound 3 (fun i : Fin 3 => if i.val < 2 then ((1,0,0) : AffineCut) else (1,0,-1))
    (0,0) (1,0) (by norm_num) (by norm_num)

/-- A candidate retaining only a positive representative loses the boundary zero. -/
theorem positive_only_does_not_cover_boundary : ¬ (∀ p : ℝ × ℝ,
    inRectangle (0,0) (1,1) p → ∃ r ∈ ({(1,0)} : Finset (ℝ × ℝ)),
      cutSign (evalCut (1,0,0) r) = cutSign (evalCut (1,0,0) p)) := by
  intro h
  obtain ⟨r, hr, hs⟩ := h (0,0) (by norm_num [inRectangle])
  simp only [Finset.mem_singleton] at hr
  subst r
  norm_num [evalCut, cutSign] at hs

/-- The zero code cannot be identified with positive, even on the boundary. -/
example : cutSign (evalCut (1,0,0) (0,0)) ≠
    cutSign (evalCut (1,0,0) (1,0)) := by
  norm_num [evalCut, cutSign]

#check arrangementRepresentativeBound
#print axioms arrangementRepresentativeBound
#print axioms realizedPlanePatterns_card_le
#print axioms realizedLinePatterns_card_le
#print axioms card_le_oldPatterns_add_two_zeroPatterns
#print axioms positive_only_does_not_cover_boundary
