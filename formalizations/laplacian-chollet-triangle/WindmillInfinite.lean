import RootTriangle
import RootStrongClosure

namespace Chollet

/-- Nonroot vertices of the windmill with n+1 triangles; each new
triangle contributes two distinct vertices attached to a common root. -/
def windmillPetals : ℕ → Type
  | 0 => Fin 2
  | n+1 => windmillPetals n ⊕ Fin 2

noncomputable instance windmillPetalsFintype (n : ℕ) :
    Fintype (windmillPetals n) := by
  induction n with
  | zero =>
    change Fintype (Fin 2)
    infer_instance
  | succ n ih =>
    change Fintype (windmillPetals n ⊕ Fin 2)
    letI : Fintype (windmillPetals n) := ih
    infer_instance

instance windmillPetalsDecidableEq (n : ℕ) :
    DecidableEq (windmillPetals n) := by
  induction n with
  | zero =>
    change DecidableEq (Fin 2)
    infer_instance
  | succ n ih =>
    change DecidableEq (windmillPetals n ⊕ Fin 2)
    letI : DecidableEq (windmillPetals n) := ih
    infer_instance

/-- Full real Laplacian matrices of the all-triangle rooted windmills,
with n+1 triangles of unit edge weights and a single shared vertex. -/
noncomputable def windmillLaplacian : (n : ℕ) →
    Matrix (Option (windmillPetals n)) (Option (windmillPetals n)) ℝ
  | 0 => rootedStieltjesThree 2 2 2 1 1 1
  | n+1 => onePointSumMatrix (windmillLaplacian n)
      (rootedStieltjesThree 2 2 2 1 1 1)


/-- The rooted 3-cycle of unit edge weights carries every recursive
strong-Chollet and singleton-pivot invariant. -/
private theorem rootUnitTriangleStrong :
    RootStrong (rootedStieltjesThree 2 2 2 1 1 1) := by
  apply RootStrong.of_rootedStieltjesThree 2 2 2 1 1 1
  all_goals norm_num

/-- An infinite family: arbitrarily many complete triangular Laplacian
blocks can meet in one root, and ALL the recursive strong-Chollet/pivot
properties hold, in every dimension 2n+3. -/
theorem windmillRootStrong (n : ℕ) :
    RootStrong (windmillLaplacian n) := by
  induction n with
  | zero =>
    exact rootUnitTriangleStrong
  | succ n ih =>
    change RootStrong (onePointSumMatrix (windmillLaplacian n)
      (rootedStieltjesThree 2 2 2 1 1 1))
    exact RootStrong.onePointSum (windmillLaplacian n)
      (rootedStieltjesThree 2 2 2 1 1 1)
      ih rootUnitTriangleStrong

/-- The genuine Mathlib matrix-permanent strong inequality is verified
for the entire unbounded windmill-Laplacian matrix family. -/
theorem strongChollet_all_windmills (n : ℕ) :
    Matrix.permanent (fun i j =>
        windmillLaplacian n i j * windmillLaplacian n i j) ≤
      Matrix.permanent (windmillLaplacian n) *
        (∏ i, windmillLaplacian n i i) :=
  (windmillRootStrong n).whole

end Chollet

#print axioms Chollet.windmillRootStrong
#print axioms Chollet.strongChollet_all_windmills
