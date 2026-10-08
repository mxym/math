import GaussianAllCellsFlux
import GaussianFluxCoefficientSymmetry

/-! The positive coefficients obtained from actual cell integrals agree
across each shared face. Rotation invariance forces symmetry away from the
base label; conservation of total Gaussian moment forces the remaining
entries. Thus the genuine moments have a symmetric positive Laplacian. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma basis_flux_coordinate
    (v : Fin (d+2) → Space (d+1)) (m : Fin (d+2) → Space (d+1))
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1)))
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) (i : Fin (d+2)) (q : Fin (d+1)) :
    B.repr (m i) q = ∑ j, w i j * B.repr (v i - v j) q := by
  change B.coord q (m i) = ∑ j, w i j * B.coord q (v i - v j)
  rw [hf]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma normal_basis_flux_offdiagonal
    (v : Fin (d+2) → Space (d+1)) (m : Fin (d+2) → Space (d+1))
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j))
    (p q : Fin (d+1)) (hpq : p ≠ q) : B.repr (m p.succ) q = w p.succ q.succ := by
  classical
  have hn (i : Fin (d+1)) : B.repr (v 0 - v i.succ) q = if i = q then 1 else 0 := by
    rw [← hB i]
    simp only [Basis.repr_self,Finsupp.single_apply]
  have hp : B.repr (v 0 - v p.succ) q = 0 := by rw [hn,if_neg hpq]
  have hr (j : Fin (d+2)) : B.repr (v p.succ - v j) q = B.repr (v 0 - v j) q := by
    rw [show v p.succ - v j = (v 0 - v j) - (v 0 - v p.succ) by abel, map_sub]
    rw [Finsupp.sub_apply,hp,sub_zero]
  rw [basis_flux_coordinate v m w B hf]
  simp_rw [hr]
  rw [Fin.sum_univ_succ]
  simp only [sub_self,map_zero,Finsupp.zero_apply,mul_zero,zero_add,hn]
  simp

lemma normal_basis_flux_base
    (v : Fin (d+2) → Space (d+1)) (m : Fin (d+2) → Space (d+1))
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) (q : Fin (d+1)) :
    B.repr (m 0) q = w 0 q.succ := by
  classical
  have hn (i : Fin (d+1)) : B.repr (v 0 - v i.succ) q = if i = q then 1 else 0 := by
    rw [← hB i]
    simp only [Basis.repr_self,Finsupp.single_apply]
  rw [basis_flux_coordinate v m w B hf]
  rw [Fin.sum_univ_succ]
  simp only [sub_self,map_zero,Finsupp.zero_apply,mul_zero,zero_add,hn]
  simp

lemma normal_basis_flux_row_sum
    (v : Fin (d+2) → Space (d+1)) (m : Fin (d+2) → Space (d+1))
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ i, B i = v 0 - v i.succ)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) (p : Fin (d+1)) :
    (∑ q : Fin (d+1), B.repr (m p.succ) q) = -w p.succ 0 := by
  classical
  have hn (i : Fin (d+1)) : (∑ q : Fin (d+1), B.repr (v 0 - v i.succ) q) = 1 := by
    rw [← hB i]
    simp only [Basis.repr_self,Finsupp.single_apply]
    simp
  have hr (j : Fin (d+2)) :
      (∑ q : Fin (d+1), B.repr (v p.succ - v j) q) =
        (∑ q : Fin (d+1), B.repr (v 0 - v j) q) - 1 := by
    simp_rw [show v p.succ - v j = (v 0 - v j) - (v 0 - v p.succ) by abel]
    rw [map_sub]
    simp only [Finsupp.sub_apply,Finset.sum_sub_distrib]
    rw [hn]
  simp_rw [basis_flux_coordinate v m w B hf]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hr]
  rw [Fin.sum_univ_succ]
  simp only [sub_self,map_zero,Finsupp.zero_apply,mul_zero,zero_add,hn]
  simp

theorem gaussian_symmetric_positive_flux
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      ∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i - v j) := by
  classical
  obtain ⟨w,hd,hp,hf⟩ := gaussian_all_cells_positive_flux v b hv
  obtain ⟨B,hB⟩ := simplicial_normal_basis v hv
  have hs (p q : Fin (d+1)) : B.repr (rawWinningMoment v b p.succ) q =
      B.repr (rawWinningMoment v b q.succ) p :=
    gaussian_normal_coefficients_symmetric v b hv.injective B hB p q
  have hnonbase (p q : Fin (d+1)) : w p.succ q.succ = w q.succ p.succ := by
    by_cases he : p = q
    · simp [he]
    · rw [← normal_basis_flux_offdiagonal v _ w B hB hf p q he,
        hs, normal_basis_flux_offdiagonal v _ w B hB hf q p (Ne.symm he)]
  have hbase (p : Fin (d+1)) : w 0 p.succ = w p.succ 0 := by
    have hz : (∑ i : Fin (d+2), B.repr (rawWinningMoment v b i) p) = 0 := by
      have hm : (∑ i : Fin (d+2), rawWinningMoment v b i) = 0 := by
        simp_rw [rawWinningMoment_eq _ _ hv.injective]
        exact (winningPartition v b hv.injective).sum_moment
      have hh := congrArg (fun z : Space (d+1) => B.repr z p) hm
      simpa [map_sum,Finset.sum_apply] using hh
    rw [Fin.sum_univ_succ,normal_basis_flux_base v _ w B hB hf p] at hz
    simp_rw [← hs] at hz
    rw [normal_basis_flux_row_sum v _ w B hB hf p] at hz
    linarith
  refine ⟨w,hd,hp,?_,hf⟩
  intro i j
  refine Fin.cases ?_ (fun p => ?_) i
  · exact Fin.cases rfl (fun q => hbase q) j
  · exact Fin.cases (hbase p).symm (fun q => hnonbase p q) j

end GaussianMeasureBridge
