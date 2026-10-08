import RootStrongClosure
import TriangleStieltjes
import PermanentTwo
import Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Chollet

/-- Root reindexing, with the distinguished root at Fin3 index zero. -/
def triangleRootEquiv : Option (Fin 2) ≃ Fin 3 :=
  (finSuccEquiv 2).symm

/-- The general order-three Stieltjes matrix, rooted at its first vertex
so that it may be glued repeatedly by the one-point-sum operation. -/
def rootedStieltjesThree (a b c x y z : ℝ) :
    Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ :=
  fun i j => stieltjesThree a b c x y z
    (triangleRootEquiv i) (triangleRootEquiv j)

private theorem rootedStieltjesThree_minor (a b c x y z : ℝ) :
    (fun i j : Fin 2 => rootedStieltjesThree a b c x y z (some i) (some j)) =
      !![b,-z; -z,c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootedStieltjesThree, triangleRootEquiv,
      finSuccEquiv_symm_some, stieltjesThree]


/-- Every weakly diagonally dominant symmetric three-vertex Z-matrix,
rooted at its first vertex, satisfies the full recursive certificate:
whole strong, deleted strong, root pivot, nonnegative deleted permanent,
and nonnegative diagonals. The parameters are arbitrary real numbers. -/
theorem RootStrong.of_rootedStieltjesThree
    (a b c x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : x+y ≤ a) (hb : x+z ≤ b) (hc : y+z ≤ c) :
    RootStrong (rootedStieltjesThree a b c x y z) := by
  classical
  let A := rootedStieltjesThree a b c x y z
  let B : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => A (some i) (some j)
  have hm : B = !![b,-z;-z,c] :=
    rootedStieltjesThree_minor a b c x y z
  have hroot : A none none = a := by
    simp [A, rootedStieltjesThree, triangleRootEquiv,
      finSuccEquiv_symm_none, stieltjesThree]
  have hR : Matrix.permanent B = b*c+z^2 := by
    rw [hm, permanent_two_formula]
    ring
  have hQminor :
      (fun i j : Fin 2 => B i j * B i j) =
      !![b^2,z^2;z^2,c^2] := by
    ext i j
    rw [hm]
    fin_cases i <;> fin_cases j <;> norm_num <;> ring
  have hT : Matrix.permanent (fun i j => B i j * B i j) =
      b^2*c^2+z^4 := by
    rw [hQminor, permanent_two_formula]
    ring
  have hprodB : (∏ i : Fin 2, B i i) = b*c := by
    rw [hm]
    norm_num [Fin.prod_univ_succ]
  have hprodA : (∏ i : Option (Fin 2), A i i) = a*b*c := by
    rw [Fintype.prod_option, hroot, hprodB]
    ring
  have hbpos : 0 ≤ b := by linarith
  have hcpos : 0 ≤ c := by linarith
  have hap : 0 ≤ a := by linarith
  have hbz : 0 ≤ b-z := by linarith
  have hcz : 0 ≤ c-z := by linarith
  have hbc : 0 ≤ b*c-z^2 := by
    have hident : b*c-z^2 =
      (b-z)*(c-z)+z*(b-z)+z*(c-z) := by ring
    rw [hident]
    positivity
  have hdiag : ∀ i : Option (Fin 2), 0 ≤ A i i := by
    intro i
    cases i with
    | none => simpa [hroot] using hap
    | some i =>
      fin_cases i
      · change 0 ≤ B (0 : Fin 2) 0
        simpa [hm] using hbpos
      · change 0 ≤ B (1 : Fin 2) 1
        simpa [hm] using hcpos
  have hdeleted :
      Matrix.permanent (fun i j => B i j * B i j) ≤
        Matrix.permanent B * (∏ i, B i i) := by
    rw [hT, hR, hprodB]
    have hp : 0 ≤ z^2*(b*c-z^2) :=
      mul_nonneg (sq_nonneg z) hbc
    nlinarith
  have hnonneg : 0 ≤ Matrix.permanent B := by
    rw [hR]
    exact add_nonneg (mul_nonneg hbpos hcpos) (sq_nonneg z)
  have hPerm :
      Matrix.permanent A =
        a*b*c+a*z^2+b*y^2+c*x^2-2*x*y*z := by
    calc
      Matrix.permanent A =
        Matrix.permanent (stieltjesThree a b c x y z) :=
          permanent_reindex_equiv (stieltjesThree a b c x y z)
            triangleRootEquiv
      _ = triP a b c x y z :=
        permanent_stieltjesThree a b c x y z
      _ = _ := rfl
  have hpivot : A none none * Matrix.permanent B ≤
      Matrix.permanent A := by
    rw [hroot, hR, hPerm]
    have hp :
        0 ≤ (b-z)*y^2+(c-z)*x^2+z*(x-y)^2 := by positivity
    nlinarith [hp]
  have hwhole :
      Matrix.permanent (fun i j => A i j*A i j) ≤
        Matrix.permanent A * (∏ i, A i i) := by
    have hsq :
        Matrix.permanent (fun i j => A i j*A i j) =
        Matrix.permanent
          (fun i j : Fin 3 =>
             stieltjesThree a b c x y z i j *
             stieltjesThree a b c x y z i j) :=
      permanent_reindex_equiv
        (fun i j : Fin 3 =>
          stieltjesThree a b c x y z i j *
          stieltjesThree a b c x y z i j) triangleRootEquiv
    have hp :
        Matrix.permanent A =
          Matrix.permanent (stieltjesThree a b c x y z) :=
      permanent_reindex_equiv (stieltjesThree a b c x y z)
        triangleRootEquiv
    calc
      Matrix.permanent (fun i j => A i j*A i j) =
        Matrix.permanent (fun i j : Fin 3 =>
          stieltjesThree a b c x y z i j *
          stieltjesThree a b c x y z i j) := hsq
      _ ≤ Matrix.permanent (stieltjesThree a b c x y z) *
        (a*b*c) :=
        strong_chollet_stieltjes_three a b c x y z hx hy hz ha hb hc
      _ = Matrix.permanent A * (∏ i, A i i) := by
        rw [hp, hprodA]
  exact ⟨hdiag, hwhole, hdeleted, hpivot, hnonneg⟩

end Chollet

#print axioms Chollet.RootStrong.of_rootedStieltjesThree
