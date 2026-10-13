import HydrologyTree.ScaledSerialization
import HydrologyTree.CoprimeBranchRecovery

/-! The serialized all-child numerator is the actual finite sum over original
child indices, including zero factors. No cancellation or divisions are used. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma product_erase_eq_product_ite {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → ℝ[X]) (i : I) :
    (∏ j ∈ Finset.univ.erase i, P j) = ∏ j : I, if j=i then 1 else P j := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j=i then 1 else P j) (Finset.mem_univ i)]
  simp only [ite_true,one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  exact (if_neg (Finset.mem_erase.mp hj).1).symm

lemma branchNumeratorSum_ite {I : Type*} [Fintype I] [DecidableEq I]
    (P R : I → ℝ[X]) :
    branchNumeratorSum P R = ∑ i : I, R i * ∏ j : I, if j=i then 1 else P j := by
  simp only [branchNumeratorSum, product_erase_eq_product_ite]

lemma product_erase_fin_zero {k : ℕ} (P : Fin (k+1) → ℝ[X]) :
    (∏ j ∈ Finset.univ.erase (0 : Fin (k+1)), P j) = ∏ i : Fin k, P i.succ := by
  rw [product_erase_eq_product_ite,Fin.prod_univ_succ]
  simp only [ite_true,Fin.succ_ne_zero,ite_false,one_mul]

lemma product_erase_fin_succ {k : ℕ} (P : Fin (k+1) → ℝ[X]) (i : Fin k) :
    (∏ j ∈ Finset.univ.erase i.succ, P j) =
      P 0 * ∏ j ∈ Finset.univ.erase i, P j.succ := by
  rw [product_erase_eq_product_ite,Fin.prod_univ_succ,
    product_erase_eq_product_ite]
  have hz : (0 : Fin (k+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
  simp only [hz,ite_false,Fin.succ_inj]

lemma branchNumeratorSum_fin_succ {k : ℕ} (P R : Fin (k+1) → ℝ[X]) :
    branchNumeratorSum P R = R 0 * (∏ i : Fin k, P i.succ) +
      P 0 * branchNumeratorSum (fun i : Fin k => P i.succ) (fun i : Fin k => R i.succ) := by
  rw [branchNumeratorSum,Fin.sum_univ_succ,product_erase_fin_zero]
  congr 1
  rw [branchNumeratorSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [product_erase_fin_succ]
  ring

lemma serializedFinNumerator {k : ℕ} (m : Fin k → ℕ)
    (p r : (i : Fin k) → Coeff (m i+1)) :
    familyNumerator (ChildFactorDegrees (finDegreeList m))
      (piScaledFinEquiv m p) (piScaledFinEquiv m r) =
      branchNumeratorSum (fun i => (monicPoly (p i) : ℝ[X])) (fun i => (r i : ℝ[X])) := by
  induction k with
  | zero =>
    change (0 : ℝ[X]) = ∑ i : Fin 0, _
    simp
  | succ k ih =>
    rw [branchNumeratorSum_fin_succ]
    change (r 0 : ℝ[X]) *
      (monicPoly (familyProduct (ChildFactorDegrees (finDegreeList (fun i : Fin k => m i.succ)))
        (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ))) : ℝ[X]) +
      (monicPoly (p 0) : ℝ[X]) *
        familyNumerator (ChildFactorDegrees (finDegreeList (fun i : Fin k => m i.succ)))
          (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => p i.succ))
          (piScaledFinEquiv (fun i : Fin k => m i.succ) (fun i : Fin k => r i.succ)) = _
    rw [ih,familyProduct_reconstruct,piScaledFin_polynomials,List.prod_ofFn]

lemma branchNumeratorSum_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (P R : J → ℝ[X]) :
    branchNumeratorSum (fun i => P (e i)) (fun i => R (e i)) = branchNumeratorSum P R := by
  rw [branchNumeratorSum_ite,branchNumeratorSum_ite]
  rw [← e.sum_comp (fun j => R j * ∏ k : J, if k=j then 1 else P k)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← e.prod_comp (fun k => if k=e i then 1 else P k)]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Equiv.apply_eq_iff_eq]

/-- No original child is lost, repeated or assigned a spurious numerator. -/
theorem serializedNumerator {I : Type*} [Fintype I] [DecidableEq I]
    (m : I → ℕ) (p r : (i : I) → Coeff (m i+1)) :
    familyNumerator (ChildFactorDegrees (degreeSequence m)) (piScaledEquiv m p) (piScaledEquiv m r) =
      branchNumeratorSum (fun i => (monicPoly (p i) : ℝ[X])) (fun i => (r i : ℝ[X])) := by
  change familyNumerator (ChildFactorDegrees (finDegreeList _))
    (piScaledFinEquiv (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i))
      (fun i : Fin (Fintype.card I) => p ((Fintype.equivFin I).symm i)))
    (piScaledFinEquiv (fun i : Fin (Fintype.card I) => m ((Fintype.equivFin I).symm i))
      (fun i : Fin (Fintype.card I) => r ((Fintype.equivFin I).symm i))) = _
  rw [serializedFinNumerator]
  exact branchNumeratorSum_equiv (Fintype.equivFin I).symm
    (fun i : I => (monicPoly (p i) : ℝ[X])) (fun i : I => (r i : ℝ[X]))

end HydrologyTree
