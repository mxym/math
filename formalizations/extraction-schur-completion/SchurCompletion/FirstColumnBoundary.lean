import SchurCompletion.AlternatingHaarBlock

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem repeated_factor_rank_le_pred (D k : ℕ) (z : Fin k → Fin D → ℂ)
    (i j : Fin k) (hij : i ≠ j) (hz : z i = z j) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ k-1 := by
  have hn : ¬ LinearIndependent ℂ z := fun h => hij (h.injective hz)
  have hr : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) < k := by
    by_contra h
    apply hn
    apply (linearIndependent_iff_card_le_finrank_span).mpr
    simpa only [Fintype.card_fin,Set.finrank] using Nat.le_of_not_gt h
  omega

def boundaryQuotientAlternating (D k : ℕ) :
    (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ]
      ((Word D k → ℂ) ⧸ rankBudgetSpace D k (k-1)) where
  toMultilinearMap := (rankBudgetSpace D k (k-1)).mkQ.compMultilinearMap
    (productTensorMultilinear D k)
  map_eq_zero_of_eq' z i j hz hij := by
    change (rankBudgetSpace D k (k-1)).mkQ (productVector D k z) = 0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨z,repeated_factor_rank_le_pred D k z i j hij hz,rfl⟩

def boundaryExteriorDesc (D k : ℕ) : CoordinateExteriorPower D k →ₗ[ℂ]
    ((Word D k → ℂ) ⧸ rankBudgetSpace D k (k-1)) :=
  exteriorPower.alternatingMapLinearEquiv (boundaryQuotientAlternating D k)

theorem boundaryExteriorDesc_coordinateWedgeMap (D k : ℕ) :
    (boundaryExteriorDesc D k).comp (coordinateWedgeMap D k) =
      (rankBudgetSpace D k (k-1)).mkQ := by
  apply (Pi.basisFun ℂ (Word D k)).ext
  intro w
  rw [Pi.basisFun_apply]
  change boundaryExteriorDesc D k (coordinateWedgeMap D k (Pi.single w 1)) = _
  rw [coordinateWedgeMap_single]
  rw [boundaryExteriorDesc,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (rankBudgetSpace D k (k-1)).mkQ (productVector D k (fun j => Pi.single (w j) 1)) =
    (rankBudgetSpace D k (k-1)).mkQ (Pi.single w 1)
  rw [productVector_basis]

/-- At the first excluded column length the alternating condition is complete:
 the actual intrinsic support is exactly the kernel of exterior contraction.
 This follows from the exterior universal property, not a dimension hypothesis. -/
theorem rankBudgetSpace_pred_eq_wedge_kernel (D k : ℕ) (hk : 0 < k) :
    rankBudgetSpace D k (k-1) = LinearMap.ker (coordinateWedgeMap D k) := by
  apply le_antisymm
  · intro v hv
    have h := tensorAntisymmetrizer_annihilates_rankBudgetSpace D k (k-1) (by omega) v hv
    have hew := DFunLike.congr_fun (exteriorTensorEmbedding_coordinateWedgeMap D k) v
    change exteriorTensorEmbedding D k (coordinateWedgeMap D k v) =
      tensorAntisymmetrizer D k *ᵥ v at hew
    rw [h] at hew
    apply LinearMap.mem_ker.mpr
    apply exteriorTensorEmbedding_injective D k
    simpa only [map_zero] using hew
  · intro v hv
    rw [← Submodule.Quotient.mk_eq_zero]
    change (rankBudgetSpace D k (k-1)).mkQ v = 0
    have h := DFunLike.congr_fun (boundaryExteriorDesc_coordinateWedgeMap D k) v
    change boundaryExteriorDesc D k (coordinateWedgeMap D k v) =
      (rankBudgetSpace D k (k-1)).mkQ v at h
    rw [LinearMap.mem_ker.mp hv,map_zero] at h
    exact h.symm

/-- Exact first nontrivial rank-budget dimension for every ambient D: at
 blocklength s+1 the missing subspace is the actual exterior power. -/
theorem rankBudgetProjector_boundary_rank (D s : ℕ) :
    (rankBudgetProjector D (s+1) s).rank = D^(s+1) - D.choose (s+1) := by
  have hr := (coordinateWedgeMap D (s+1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (coordinateWedgeMap_surjective D (s+1)),
    finrank_top] at hr
  have he : Module.finrank ℂ (CoordinateExteriorPower D (s+1)) = D.choose (s+1) := by
    simp [CoordinateExteriorPower]
  rw [he] at hr
  rw [rankBudgetProjector_rank]
  have hk := rankBudgetSpace_pred_eq_wedge_kernel D (s+1) (by omega)
  simp only [Nat.add_sub_cancel] at hk
  rw [hk]
  have hdim : Module.finrank ℂ (Word D (s+1) → ℂ) = D^(s+1) := by
    simp only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,smul_eq_mul,mul_one]
  rw [hdim] at hr
  omega

end
end ExtractionSchur
