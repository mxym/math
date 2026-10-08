import Entry005.Handoff
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.Linarith

/-!
A bound on the actual augmented determinant of all vertex tuples extends
to arbitrary tuples in the convex hull. The argument uses separate convexity
in each actual point, not an assumption that a maximum occurs at vertices.
-/

noncomputable section

namespace Entry005

private def truncationAugmentedPoint {d : ℕ} (x : Space d) : Fin (d + 1) → ℝ :=
  Fin.cases 1 (fun k : Fin d => x k)

theorem augmentedVertices_update {d : ℕ} (z : Fin (d + 1) → Space d)
    (j : Fin (d + 1)) (x : Space d) :
    augmentedVertices (Function.update z j x) =
      (augmentedVertices z).updateCol j (Fin.cases 1 (fun k : Fin d => x k)) := by
  classical
  ext i k
  by_cases h : k = j
  · subst k
    simp [augmentedVertices]
  · simp [augmentedVertices, h]

theorem augmentedVertices_update_affine_det {d : ℕ} (z : Fin (d + 1) → Space d)
    (j : Fin (d + 1)) (x y : Space d) (a b : ℝ) (hab : a + b = 1) :
    (augmentedVertices (Function.update z j (a • x + b • y))).det =
      a * (augmentedVertices (Function.update z j x)).det +
      b * (augmentedVertices (Function.update z j y)).det := by
  classical
  have hl : truncationAugmentedPoint (a • x + b • y) =
      a • truncationAugmentedPoint x + b • truncationAugmentedPoint y := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [truncationAugmentedPoint, smul_eq_mul] using hab.symm
    · simp [truncationAugmentedPoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [augmentedVertices_update]
  change ((augmentedVertices z).updateCol j
      (truncationAugmentedPoint (a • x + b • y))).det = _
  rw [hl, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
    Matrix.det_updateCol_smul]
  rfl

theorem convex_augmentedVertices_abs_det_sublevel {d : ℕ}
    (z : Fin (d + 1) → Space d) (j : Fin (d + 1)) (M : ℝ) :
    Convex ℝ {x : Space d | |(augmentedVertices (Function.update z j x)).det| ≤ M} := by
  intro x hx y hy a b ha hb hab
  change |(augmentedVertices (Function.update z j (a • x + b • y))).det| ≤ M
  rw [augmentedVertices_update_affine_det z j x y a b hab]
  calc
    |a * (augmentedVertices (Function.update z j x)).det +
        b * (augmentedVertices (Function.update z j y)).det| ≤
      |a * (augmentedVertices (Function.update z j x)).det| +
        |b * (augmentedVertices (Function.update z j y)).det| := abs_add_le _ _
    _ = a * |(augmentedVertices (Function.update z j x)).det| +
        b * |(augmentedVertices (Function.update z j y)).det| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * M + b * M := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = M := by rw [← add_mul, hab, one_mul]

private theorem augmentedVertices_abs_det_le_on_partial_convexHull {d : ℕ}
    {ι : Type*} (v : ι → Space d) (M : ℝ)
    (hvertex : ∀ b : Fin (d + 1) → ι, |(augmentedVertices (v ∘ b)).det| ≤ M)
    (s : Finset (Fin (d + 1))) :
    ∀ z : Fin (d + 1) → Space d,
      (∀ j ∈ s, z j ∈ convexHull ℝ (Set.range v)) →
      (∀ j ∉ s, z j ∈ Set.range v) → |(augmentedVertices z).det| ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro z _ hout
      have hz : ∀ j, ∃ k, v k = z j := fun j => hout j (Finset.notMem_empty j)
      choose b hb using hz
      have hzb : z = v ∘ b := by
        funext j
        exact (hb j).symm
      rw [hzb]
      exact hvertex b
  | @insert i s hi ih =>
      intro z hin hout
      have hs : Set.range v ⊆
          {x : Space d | |(augmentedVertices (Function.update z i x)).det| ≤ M} := by
        rintro x ⟨k, rfl⟩
        apply ih (Function.update z i (v k))
        · intro j hj
          have hji : j ≠ i := by
            intro h
            subst j
            exact hi hj
          rw [Function.update_of_ne hji]
          exact hin j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simp only [Function.update_self]
            exact Set.mem_range_self k
          · rw [Function.update_of_ne hji]
            exact hout j (by simp [Finset.mem_insert, hji, hj])
      have hz := convexHull_min hs
        (convex_augmentedVertices_abs_det_sublevel z i M)
        (hin i (Finset.mem_insert_self i s))
      change |(augmentedVertices (Function.update z i (z i))).det| ≤ M at hz
      simpa only [Function.update_eq_self] using hz

/-- Every tuple of actual convex-hull points satisfies the vertex-tuple bound.
No finiteness or nonemptiness premise on the generating index type is needed. -/
theorem augmentedVertices_abs_det_le_of_mem_convexHull {d : ℕ} {ι : Type*}
    (v : ι → Space d) (z : Fin (d + 1) → Space d) (M : ℝ)
    (hvertex : ∀ b : Fin (d + 1) → ι, |(augmentedVertices (v ∘ b)).det| ≤ M)
    (hz : ∀ j, z j ∈ convexHull ℝ (Set.range v)) :
    |(augmentedVertices z).det| ≤ M := by
  apply augmentedVertices_abs_det_le_on_partial_convexHull v M hvertex Finset.univ z
  · exact fun j _ => hz j
  · simp

#print axioms augmentedVertices_update
#print axioms augmentedVertices_update_affine_det
#print axioms convex_augmentedVertices_abs_det_sublevel
#print axioms augmentedVertices_abs_det_le_of_mem_convexHull

end Entry005
