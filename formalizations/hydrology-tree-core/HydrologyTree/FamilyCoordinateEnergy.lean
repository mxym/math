import HydrologyTree.BranchStep
import HydrologyTree.CoordinateEnergy

/-! Exact coefficient-dot preservation for all family charts. This rules out
unproved, size-dependent scale factors when global Jacobians are transported. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

lemma basisDot_reindex {E I J : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] [Fintype J] (b : Basis I ℝ E) (e : I ≃ J) (x y : E) :
    basisDot (b.reindex e) x y = basisDot b x y := by
  simp only [basisDot, Basis.repr_reindex_apply]
  exact e.symm.sum_comp (fun i => b.repr x i * b.repr y i)

lemma basisDot_prod {E F I J : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype I] [Fintype J]
    (b : Basis I ℝ E) (c : Basis J ℝ F) (x y : E × F) :
    basisDot (b.prod c) x y = basisDot b x.1 y.1 + basisDot c x.2 y.2 := by
  simp [basisDot]

lemma basisDot_degreeLT (n : ℕ) (p q : Coeff n) :
    basisDot (degreeLT.basis ℝ n) p q = coefficientDot n p q := by
  simp [basisDot, coefficientDot, Polynomial.degreeLT.basis_repr]

lemma basisDot_equiv {E F I : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype I]
    (b : Basis I ℝ E) (c : Basis I ℝ F) (x y : E) :
    basisDot c (b.equiv c (Equiv.refl I) x) (b.equiv c (Equiv.refl I) y) = basisDot b x y := by
  simp [basisDot, Basis.equiv]

@[reducible] def familyCoordinateDot : (ms : List ℕ) → ProductInput ms → ProductInput ms → ℝ
  | [], _, _ => 0
  | m :: ms, x, y => coefficientDot m x.1 y.1 + familyCoordinateDot ms x.2 y.2

lemma familyBasis_dot (ms : List ℕ) (x y : ProductInput ms) :
    basisDot (familyBasis ms) x y = familyCoordinateDot ms x y := by
  induction ms with
  | nil =>
    change basisDot (degreeLT.basis ℝ 0) x y = 0
    simp [basisDot]
  | cons m ms ih =>
    change basisDot (((degreeLT.basis ℝ m).prod (familyBasis ms)).reindex
      (finSumFinEquiv : (Fin m ⊕ Fin ms.sum) ≃ Fin (m+ms.sum))) x y =
        coefficientDot m x.1 y.1 + familyCoordinateDot ms x.2 y.2
    rw [basisDot_reindex, basisDot_prod, basisDot_degreeLT, ih]

lemma familyPairEquiv_dot (ms : List ℕ) (x y : FamilyPairs ms) :
    coefficientDot ms.sum (familyPairEquiv ms x).1 (familyPairEquiv ms y).1 +
      coefficientDot ms.sum (familyPairEquiv ms x).2 (familyPairEquiv ms y).2 =
      familyCoordinateDot ms x.1 y.1 + familyCoordinateDot ms x.2 y.2 := by
  have h := basisDot_equiv ((familyBasis ms).prod (familyBasis ms))
    ((degreeLT.basis ℝ ms.sum).prod (degreeLT.basis ℝ ms.sum)) x y
  simpa only [familyPairEquiv, basisDot_prod, basisDot_degreeLT, familyBasis_dot] using h

lemma leadingEquiv_dot (n : ℕ) (x y : ℝ × Coeff n) :
    coefficientDot (n+1) (leadingEquiv n x) (leadingEquiv n y) =
      x.1*y.1 + coefficientDot n x.2 y.2 := by
  rw [coefficientDot_succ]
  have hx := split_joinLeading x
  have hy := split_joinLeading y
  rw [splitLeadingLM_apply] at hx hy
  rw [show ((leadingEquiv n x : Coeff (n+1)) : ℝ[X]).coeff n = x.1 from congrArg Prod.fst hx,
    show ((leadingEquiv n y : Coeff (n+1)) : ℝ[X]).coeff n = y.1 from congrArg Prod.fst hy,
    show cut n (leadingEquiv n x : ℝ[X]) = x.2 from congrArg Prod.snd hx,
    show cut n (leadingEquiv n y : ℝ[X]) = y.2 from congrArg Prod.snd hy]

lemma branchCoefficientEquiv_apply (ms : List ℕ)
    (p : Coeff ((ChildFactorDegrees ms).sum+1) × Coeff (ChildFactorDegrees ms).sum) :
    branchCoefficientEquiv ms p =
      ((familyPairEquiv (ChildFactorDegrees ms)).symm
        (p.2, cut (ChildFactorDegrees ms).sum (p.1 : ℝ[X])),
          (p.1 : ℝ[X]).coeff (ChildFactorDegrees ms).sum) := rfl

/-- Both gluing coordinate blocks and the root coordinate are pure coefficient
reorderings; no determinant magnitude is inferred numerically. -/
lemma branchCoefficientEquiv_dot (ms : List ℕ)
    (p q : Coeff ((ChildFactorDegrees ms).sum+1) × Coeff (ChildFactorDegrees ms).sum) :
    familyCoordinateDot (ChildFactorDegrees ms) (branchCoefficientEquiv ms p).1.1
        (branchCoefficientEquiv ms q).1.1 +
      familyCoordinateDot (ChildFactorDegrees ms) (branchCoefficientEquiv ms p).1.2
        (branchCoefficientEquiv ms q).1.2 +
      (branchCoefficientEquiv ms p).2 * (branchCoefficientEquiv ms q).2 =
      pathCoefficientDot (ChildFactorDegrees ms).sum p q := by
  let N := (ChildFactorDegrees ms).sum
  have hp : leadingEquiv N ((p.1 : ℝ[X]).coeff N, cut N (p.1 : ℝ[X])) = p.1 := join_splitLeading p.1
  have hq : leadingEquiv N ((q.1 : ℝ[X]).coeff N, cut N (q.1 : ℝ[X])) = q.1 := join_splitLeading q.1
  have h := familyPairEquiv_dot (ChildFactorDegrees ms)
    ((familyPairEquiv (ChildFactorDegrees ms)).symm (p.2,cut N (p.1 : ℝ[X])))
    ((familyPairEquiv (ChildFactorDegrees ms)).symm (q.2,cut N (q.1 : ℝ[X])))
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at h
  rw [branchCoefficientEquiv_apply,branchCoefficientEquiv_apply]
  change _ + (p.1 : ℝ[X]).coeff N * (q.1 : ℝ[X]).coeff N = _
  rw [← h]
  unfold pathCoefficientDot
  rw [coefficientDot_succ N]
  ring

end HydrologyTree
