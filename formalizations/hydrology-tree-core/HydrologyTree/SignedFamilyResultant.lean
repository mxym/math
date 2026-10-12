import HydrologyTree.MonicResultantAlgebra
import HydrologyTree.FamilyResultants

/-! Exact signed resultant of an arbitrary denominator/numerator family.
The sign depends only on degrees, not roots, numerators, or parameter values. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Degree-only sign from swapping the sibling resultants. -/
def resultantPairSign : List ℕ → ℝ
  | [] => 1
  | m :: ms => (-1 : ℝ)^(m*ms.sum) * resultantPairSign ms

lemma resultantPairSign_sq (ms : List ℕ) : resultantPairSign ms ^ 2 = 1 := by
  induction ms with
  | nil => norm_num [resultantPairSign]
  | cons m ms ih =>
    rw [resultantPairSign,mul_pow,ih,mul_one,← pow_mul,Nat.mul_comm (m*ms.sum) 2,pow_mul]
    norm_num

/-- The actual numerator sum, in recursive product form with no divisions. -/
def resultantFamilyNumerator : List (ℝ[X] × ℝ[X]) → ℝ[X]
  | [] => 0
  | q :: qs => q.2 * (qs.map Prod.fst).prod + q.1 * resultantFamilyNumerator qs

lemma monic_pair_factors (qs : List (ℝ[X] × ℝ[X])) (h : ∀ q ∈ qs, q.1.Monic) :
    ∀ p ∈ qs.map Prod.fst, p.Monic := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact h q hq

/-- Full signed product identity at every coefficient vector. Singular and
zero-numerator specializations are included; no root distinctness is needed. -/
theorem resultant_family_factorization (qs : List (ℝ[X] × ℝ[X]))
    (h : ∀ q ∈ qs, q.1.Monic) :
    (qs.map Prod.fst).prod.resultant (resultantFamilyNumerator qs) =
      resultantPairSign (qs.map fun q => q.1.natDegree) *
        (qs.map fun q => q.1.resultant q.2).prod *
        pairwiseResultants (qs.map Prod.fst)^2 := by
  induction qs with
  | nil => simp [resultantFamilyNumerator,resultantPairSign,pairwiseResultants]
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht : ∀ r ∈ qs, r.1.Monic := fun r hr => h r (by simp [hr])
    have hm := monic_pair_factors qs ht
    rw [List.map_cons,List.prod_cons,resultantFamilyNumerator,
      monic_resultant_glue q.1 (qs.map Prod.fst).prod q.2
        (resultantFamilyNumerator qs) hq (monic_list_prod _ hm),
      ih ht,resultant_list_prod q.1 _ hm,natDegree_monic_list_prod _ hm]
    simp only [List.map_cons,List.prod_cons,List.map_map,Function.comp_def,
      resultantPairSign,pairwiseResultants]
    ring

/-- Exact local root update: the consecutive characteristic/cofactor degrees
eliminate the swap sign, while the minus-numerator contributes (-1)^n. -/
theorem resultant_root_update (f N P : ℝ[X]) (hf : f.Monic) (d : ℝ)
    (hP : P = (X+C d)*f-N) (hdeg : P.natDegree = f.natDegree+1) :
    P.resultant f = (-1 : ℝ)^f.natDegree * f.resultant N := by
  have hs : (-1 : ℝ)^(P.natDegree*f.natDegree) = 1 := by
    rw [hdeg,Nat.mul_comm (f.natDegree+1) f.natDegree]
    exact (Nat.even_mul_succ_self f.natDegree).neg_one_pow
  have he : (X+C d)*f-N = (C (-1)*N)+f*(X+C d) := by
    simp only [map_neg,map_one]
    ring
  calc
    P.resultant f = f.resultant P := by
      rw [Polynomial.resultant_comm P f,hs,one_mul]
    _ = f.resultant (C (-1)*N) := by
      rw [hP,he,monic_resultant_add_multiple f (C (-1)*N) (X+C d) hf]
    _ = _ := monic_resultant_scale f N hf (-1)

end HydrologyTree
