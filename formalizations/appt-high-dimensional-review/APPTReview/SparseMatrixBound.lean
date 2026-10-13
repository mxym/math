import APPTReview.NonnegativeRayleigh
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open Matrix
namespace APPTReview

theorem sparseScaleRank_log (M d : ℝ) (hM : 0<M) :
    sparseScaleRank (Real.log M) d=M^(2-d) := by
  unfold sparseScaleRank
  rw [Real.rpow_def_of_pos hM]
  congr 1
  ring

theorem sparseScaleCoefficient_log (M d e : ℝ) (hM : 0<M) :
    sparseScaleCoefficient (Real.log M) d e=Real.sqrt e*M^(d/2-1) := by
  unfold sparseScaleCoefficient
  rw [Real.rpow_def_of_pos hM]
  congr 2
  ring

/-- The actual finite real matrix, with fractional symmetric edges permitted. -/
noncomputable def lacunarySparseMatrix (m : ℕ) (ds : List ℝ) (e : ℝ → ℝ)
    (w : ℝ → Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => ∑ d∈ds.toFinset,Real.sqrt (e d)*(m:ℝ)^(d/2-1)*w d (i,j)

theorem lacunarySparseMatrix_rayleigh (m : ℕ) (ds : List ℝ) (e : ℝ → ℝ)
    (w : ℝ → Fin m × Fin m → ℝ) (s : Fin m → ℝ) :
    realRayleigh (lacunarySparseMatrix m ds e w) s=
      ∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(∑ z,w d z*(s z.1*s z.2)) := by
  unfold realRayleigh lacunarySparseMatrix
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Complete uniform finite-matrix form of the lacunary graph estimate.
One M works for every larger dimension and EVERY symmetric fractional family.
The original operator-square conclusion is derived from actual PSD matrices. -/
theorem lacunary_sparse_matrix_bound (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B) (he : ∀ d∈ds,0≤e d)
    (heB : ∀ d∈ds,e d≤B) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ m : ℕ, M≤m →
      ∀ (w : ℝ → Fin m × Fin m → ℝ),
      (∀ d∈ds,∀ z,0≤w d z) → (∀ d∈ds,∀ z,w d z≤1) →
      (∀ d∈ds,(∑ z,w d z)≤2*(m:ℝ)^(2-d)) →
      (∀ d∈ds,∀ i j,w d (i,j)=w d (j,i)) →
      let A := lacunarySparseMatrix m ds e w
      let C := scaleEnergyBound ds e B+ε
      (C • (1 : Matrix (Fin m) (Fin m) ℝ)-A).PosSemidef ∧
      ∀ x : Fin m → ℝ,(∑ i,(A*ᵥx) i^2)≤C^2*(∑ i,(x i)^2) := by
  obtain ⟨M,hM⟩ := lacunary_fractional_graph_limit ds hds e B hB he heB ε hε
  refine ⟨max M 2,?_⟩
  intro m hm w hw hw1 hwr hsym
  dsimp only
  have hm2 : 2≤m := (le_max_right _ _).trans hm
  have hmP : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hmw : ∀ d∈ds,(∑ z,w d z)≤2*sparseScaleRank (Real.log m) d := by
    intro d hd
    rw [sparseScaleRank_log _ _ hmP]
    exact hwr d hd
  have hA : ∀ i j,0≤lacunarySparseMatrix m ds e w i j := by
    intro i j
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hmP _).le)
      (hw d (List.mem_toFinset.mp hd) _)
  have hHerm : (lacunarySparseMatrix m ds e w).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,lacunarySparseMatrix]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hsym d (List.mem_toFinset.mp hd) j i]
  have hunit (s : Fin m → ℝ) (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) :
      realRayleigh (lacunarySparseMatrix m ds e w) s≤scaleEnergyBound ds e B+ε := by
    rw [lacunarySparseMatrix_rayleigh]
    have h := hM m ((le_max_left _ _).trans hm) s hs0 hs w hw hw1 hmw
    simpa only [sparseScaleCoefficient_log _ _ _ hmP] using h
  have hcap := matrix_cap_of_nonnegative_unit _ hHerm hA _ hunit
  exact ⟨hcap,fun x => nonnegative_matrix_square_bound _ _ hHerm hA hcap x⟩

end APPTReview
