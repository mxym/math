import SchurCompletion.SymmetricHaarBlock
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

abbrev CoordinateExteriorPower (D k : ℕ) := ⋀[ℂ]^k (Fin D → ℂ)

def exteriorTensorEmbedding (D k : ℕ) : CoordinateExteriorPower D k →ₗ[ℂ] (Word D k → ℂ) :=
  exteriorPower.alternatingMapLinearEquiv (alternatingTensorMap D k)

theorem exteriorTensorEmbedding_wedge (D k : ℕ) (z : Fin k → Fin D → ℂ) :
    exteriorTensorEmbedding D k (exteriorPower.ιMulti ℂ k z) = alternatingTensorMap D k z :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

def coordinateWedgeMap (D k : ℕ) : (Word D k → ℂ) →ₗ[ℂ] CoordinateExteriorPower D k where
  toFun v := ∑ w, v w • exteriorPower.ιMulti ℂ k (fun j => Pi.single (w j) 1)
  map_add' v u := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

theorem coordinateWedgeMap_single (D k : ℕ) (w : Word D k) :
    coordinateWedgeMap D k (Pi.single w 1) =
      exteriorPower.ιMulti ℂ k (fun j => Pi.single (w j) 1) := by
  simp [coordinateWedgeMap]

theorem productVector_basis (D k : ℕ) (w : Word D k) :
    productVector D k (fun j => Pi.single (w j) 1) = Pi.single w 1 := by
  ext v
  by_cases hv : v = w
  · subst v
    simp [productVector]
  · have hi : ∃ i, v i ≠ w i := Function.ne_iff.mp hv
    obtain ⟨i,hi⟩ := hi
    rw [Pi.single_apply,if_neg hv]
    change (∏ j : Fin k, ((Pi.single (w j) (1 : ℂ) : Fin D → ℂ) (v j))) = (0 : ℂ)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Pi.single_apply,hi]

/-- The actual coordinate tensor contracts to the ordinary exterior product. -/
theorem coordinateWedgeMap_productVector (D k : ℕ) (z : Fin k → Fin D → ℂ) :
    coordinateWedgeMap D k (productVector D k z) = exteriorPower.ιMulti ℂ k z := by
  have h : (coordinateWedgeMap D k).compMultilinearMap (productTensorMultilinear D k) =
      (exteriorPower.ιMulti ℂ k).toMultilinearMap := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin D))
    intro w
    simp only [Pi.basisFun_apply]
    change coordinateWedgeMap D k (productVector D k (fun j => Pi.single (w j) 1)) = _
    rw [productVector_basis,coordinateWedgeMap_single]
    rfl
  exact DFunLike.congr_fun h z

/-- The actual antisymmetrizer factors through the standard exterior power. -/
theorem exteriorTensorEmbedding_coordinateWedgeMap (D k : ℕ) :
    (exteriorTensorEmbedding D k).comp (coordinateWedgeMap D k) =
      (tensorAntisymmetrizer D k).mulVecLin := by
  apply (Pi.basisFun ℂ (Word D k)).ext
  intro w
  rw [Pi.basisFun_apply]
  change exteriorTensorEmbedding D k (coordinateWedgeMap D k (Pi.single w 1)) =
    tensorAntisymmetrizer D k *ᵥ Pi.single w 1
  rw [coordinateWedgeMap_single,exteriorTensorEmbedding_wedge,← productVector_basis D k w,
    tensorAntisymmetrizer_productVector]

/-- No characteristic-zero injectivity certificate is assumed: the left inverse
 is proved by alternating the actual exterior product. -/
theorem coordinateWedgeMap_exteriorTensorEmbedding (D k : ℕ) :
    (coordinateWedgeMap D k).comp (exteriorTensorEmbedding D k) =
      (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro z
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.comp_apply,
    exteriorTensorEmbedding_wedge,alternatingTensorMap,
    MultilinearMap.alternatization_apply,map_sum,Units.smul_def,map_zsmul,
    MultilinearMap.domDomCongr_apply,productTensorMultilinear_apply,
    coordinateWedgeMap_productVector]
  have h (σ : Equiv.Perm (Fin k)) :
      (Equiv.Perm.sign σ : ℤ) • exteriorPower.ιMulti ℂ k (z ∘ σ) =
        exteriorPower.ιMulti ℂ k z := by
    simpa only [Units.smul_def] using
      ((exteriorPower.ιMulti ℂ k (M := Fin D → ℂ)).map_congr_perm (v := z) σ).symm
  change (∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) •
    exteriorPower.ιMulti ℂ k (z ∘ σ)) =
      (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • exteriorPower.ιMulti ℂ k z
  simp_rw [h]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ]

theorem exteriorTensorEmbedding_injective (D k : ℕ) :
    Function.Injective (exteriorTensorEmbedding D k) := by
  intro x y hxy
  have h := congrArg (coordinateWedgeMap D k) hxy
  have hc : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ((coordinateWedgeMap D k).comp (exteriorTensorEmbedding D k)) x =
    ((coordinateWedgeMap D k).comp (exteriorTensorEmbedding D k)) y at h
  rw [coordinateWedgeMap_exteriorTensorEmbedding] at h
  exact (smul_right_injective _ hc) h

theorem coordinateWedgeMap_surjective (D k : ℕ) :
    Function.Surjective (coordinateWedgeMap D k) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← exteriorPower.ιMulti_span ℂ k (Fin D → ℂ)]
  apply Submodule.span_le.mpr
  rintro _ ⟨z,rfl⟩
  exact ⟨productVector D k z,coordinateWedgeMap_productVector D k z⟩

/-- Exact binomial rank of the original alternating tensor matrix, via the
 standard exterior power and actual coordinate maps in both directions. -/
theorem tensorAntisymmetrizer_rank_choose (D k : ℕ) :
    (tensorAntisymmetrizer D k).rank = D.choose k := by
  have hr : LinearMap.range (tensorAntisymmetrizer D k).mulVecLin =
      LinearMap.range (exteriorTensorEmbedding D k) := by
    rw [← exteriorTensorEmbedding_coordinateWedgeMap,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
        (coordinateWedgeMap_surjective D k))]
  change Module.finrank ℂ (LinearMap.range (tensorAntisymmetrizer D k).mulVecLin) = _
  rw [hr,LinearMap.finrank_range_of_inj (exteriorTensorEmbedding_injective D k)]
  simp [CoordinateExteriorPower]

end
end ExtractionSchur
