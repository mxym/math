import GaussianAllCellsFlux
import GaussianCenteredCovarianceBlock
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Gram equality gives an actual linear isometry between centered simplex
realizations. The construction extends the normal basis, so it also applies
when the target has one redundant Gaussian coordinate. -/
open Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d m : ℕ}

lemma basis_constr_inner (B : Basis (Fin (d+1)) ℝ (Space (d+1)))
    (u : Fin (d+1) → Space m)
    (hu : ∀ i j, ⟪u i,u j⟫ = ⟪B i,B j⟫) (x y : Space (d+1)) :
    ⟪B.constr ℝ u x,B.constr ℝ u y⟫ = ⟪x,y⟫ := by
  rw [B.constr_apply_fintype ℝ,B.constr_apply_fintype ℝ]
  conv_rhs => rw [← B.sum_repr x,← B.sum_repr y]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  simp only [hu,Basis.equivFun_apply]

lemma centered_normal_sum {n e : ℕ} (v : Fin (n+1) → Space e)
    (hz : ∑ i,v i = 0) :
    (∑ i : Fin n, (v 0-v i.succ)) = ((n:ℝ)+1) • v 0 := by
  have hs : (∑ i : Fin n,v i.succ) = -v 0 := by
    rw [Fin.sum_univ_succ] at hz
    exact eq_neg_of_add_eq_zero_right hz
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hs]
  module

theorem centered_gram_linearIsometry
    (v : Fin (d+2) → Space (d+1)) (u : Fin (d+2) → Space m)
    (hv : AffineIndependent ℝ v) (hzv : ∑ i,v i = 0) (hzu : ∑ i,u i = 0)
    (hg : scoreGram v = scoreGram u) :
    ∃ T : Space (d+1) →ₗᵢ[ℝ] Space m, ∀ i,T (v i) = u i := by
  classical
  obtain ⟨B,hB⟩ := simplicial_normal_basis v hv
  let a : Fin (d+1) → Space m := fun i => u 0-u i.succ
  have hi (i j : Fin (d+1)) : ⟪a i,a j⟫ = ⟪B i,B j⟫ := by
    rw [hB i,hB j]
    simp only [a,inner_sub_left,inner_sub_right]
    have he (p q : Fin (d+2)) : ⟪v p,v q⟫ = ⟪u p,u q⟫ :=
      congrFun (congrFun hg p) q
    simp_rw [he]
  let T := (B.constr ℝ a).isometryOfInner (basis_constr_inner B a hi)
  have hn (i : Fin (d+1)) : T (v 0-v i.succ) = u 0-u i.succ := by
    rw [← hB i]
    exact B.constr_basis ℝ a i
  have h0 : T (v 0) = u 0 := by
    have he : ((d+1:ℕ):ℝ)+1 ≠ 0 := by positivity
    apply smul_right_injective _ he
    calc
      (((d+1:ℕ):ℝ)+1) • T (v 0) = T (∑ i : Fin (d+1), (v 0-v i.succ)) := by
        rw [centered_normal_sum v hzv,map_smul]
      _ = ∑ i : Fin (d+1), (u 0-u i.succ) := by rw [map_sum]; simp_rw [hn]
      _ = (((d+1:ℕ):ℝ)+1) • u 0 := centered_normal_sum u hzu
  refine ⟨T,fun i => ?_⟩
  refine Fin.cases h0 (fun j => ?_) i
  have he := hn j
  rw [map_sub,h0] at he
  exact sub_right_injective he

end GaussianMeasureBridge
