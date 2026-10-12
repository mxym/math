import APPTReview.CutSimplex

open scoped BigOperators
namespace APPTReview

/-- Every feasible simplex combination lies in any convex set containing all
surviving vertices and all crossing-edge intersections. The split by sign is
constructed here, rather than supplied as part of the desired conclusion. -/
theorem convex_mem_of_cut_simplex {ι ν : Type*} [Fintype ι]
    (S : Set (ν → ℝ)) (hS : Convex ℝ S) (x g : ι → ℝ) (u : ι → ν → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i)=1) (hg : (∑ i, x i*g i) ≤ 0)
    (hv : ∀ j, g j ≤ 0 → u j ∈ S)
    (he : ∀ i j, 0 < g i → g j ≤ 0 → cutPair (g i) (-g j) (u i) (u j) ∈ S) :
    (∑ i, x i • u i) ∈ S := by
  classical
  let P := {i : ι // 0 < g i}
  let N := {i : ι // ¬ 0 < g i}
  have hsum' : (∑ i : P, x i)+(∑ j : N, x j)=1 := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun i => 0 < g i)]
    exact hsum
  have hbalance : (∑ i : P, x i*g i) ≤ ∑ j : N, x j*(-g j) := by
    have heq := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < g i) (fun i => x i*g i)
    have hb : (∑ j : N, x j*(-g j))= -(∑ j : N, x j*g j) := by
      simp only [mul_neg,Finset.sum_neg_distrib]
    rw [hb]
    linarith
  have hmem := convex_mem_of_signed_balance S hS
    (fun i : P => x i) (fun i : P => g i)
    (fun j : N => x j) (fun j : N => -g j)
    (fun i : P => u i) (fun j : N => u j)
    (fun i => hx i) (fun j => hx j) (fun i => i.property)
    (fun j => neg_nonneg.mpr (le_of_not_gt j.property)) hsum' hbalance
    (fun j => hv j (le_of_not_gt j.property))
    (fun i j => he i j i.property (le_of_not_gt j.property))
  rwa [Fintype.sum_subtype_add_sum_subtype (fun i => 0 < g i) (fun i => x i • u i)] at hmem

noncomputable def spectralSquares {ν : Type*} [Fintype ν] (f : ν → ℝ) : ℝ :=
  ∑ i, (f i)^2

/-- Exact Jensen defect for the squared Euclidean objective. -/
theorem spectralSquares_mixture {ν : Type*} [Fintype ν]
    (x y : ν → ℝ) (a b : ℝ) (hab : a+b=1) :
    a*spectralSquares x+b*spectralSquares y-spectralSquares (a • x+b • y)=
      a*b*∑ i, (x i-y i)^2 := by
  have he (i : ν) : a*(x i)^2+b*(y i)^2-(a*x i+b*y i)^2=a*b*(x i-y i)^2 := by
    have hb : b=1-a := by linarith
    rw [hb]
    ring
  unfold spectralSquares
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => he i)

/-- The relevant quadratic sublevel is convex in the original spectrum coordinates. -/
theorem convex_spectralSquares_sublevel {ν : Type*} [Fintype ν] (C : ℝ) :
    Convex ℝ {f : ν → ℝ | spectralSquares f ≤ C} := by
  intro x hx y hy a b ha hb hab
  have hid := spectralSquares_mixture x y a b hab
  have hd : 0 ≤ a*b*∑ i, (x i-y i)^2 := by positivity
  have hx' := mul_le_mul_of_nonneg_left hx ha
  have hy' := mul_le_mul_of_nonneg_left hy hb
  have hCeq : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  change spectralSquares (a • x+b • y) ≤ C
  linarith

/-- A complete cut-simplex upper-bound reduction, valid in every finite dimension. -/
theorem spectralSquares_cut_bound {ι ν : Type*} [Fintype ι] [Fintype ν]
    (x g : ι → ℝ) (u : ι → ν → ℝ) (C : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i)=1) (hg : (∑ i, x i*g i) ≤ 0)
    (hv : ∀ j, g j ≤ 0 → spectralSquares (u j) ≤ C)
    (he : ∀ i j, 0 < g i → g j ≤ 0 →
      spectralSquares (cutPair (g i) (-g j) (u i) (u j)) ≤ C) :
    spectralSquares (∑ i, x i • u i) ≤ C :=
  convex_mem_of_cut_simplex _ (convex_spectralSquares_sublevel C) x g u hx hsum hg hv he

end APPTReview
