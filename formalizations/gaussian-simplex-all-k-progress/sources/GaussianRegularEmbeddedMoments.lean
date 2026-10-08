import GaussianGramMomentTransport
import GaussianRegularFlux
import GaussianGramPrices
import GaussianMomentEqualityReduction

/-! Exact regular moments and attained energy in every ambient embedding.
These statements require no unproved perimeter comparison. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e : ℕ}

theorem balancedMoment_regular_embedding
    (u : Fin (d+2) → Space e) (hg : scoreGram u = regularCovariance (d+2)) :
    ∀ i,balancedMoment u i = simplexConstant (d+2) • u i := by
  let v := minimalCovarianceRows (regularCovariance (d+2))
  have hR := regularCovariance_normalized (k := d+2) (by omega)
  have hv : AffineIndependent ℝ v := minimalCovarianceRows_affineIndependent _ regular_principal_posDef
  have hzv : ∑ i,v i = 0 := minimalCovarianceRows_sum _
  have hgv : scoreGram v = regularCovariance (d+2) := scoreGram_minimalCovarianceRows _ hR.1 hR.2.1
  have hzu : ∑ i,u i = 0 := sum_rows_zero_of_gram_centered _ (by simpa only [hg] using hR.2.1)
  obtain ⟨T,hT,hB⟩ := balancedMoment_gram_embedding v u hv hzv hzu (hgv.trans hg.symm)
  intro i
  rw [← hB i,balancedMoment_regular_gram v hv hzv hgv i,map_smul,hT i]

theorem regular_embedding_injective
    (u : Fin (d+2) → Space e) (hg : scoreGram u = regularCovariance (d+2)) :
    Function.Injective u := by
  apply scaled_regular_gram_injective (by omega : 2 ≤ d+2) u 1 (by norm_num)
  simpa only [one_smul] using hg

theorem regular_embedding_zero_prices
    (u : Fin (d+2) → Space e) (hg : scoreGram u = regularCovariance (d+2)) :
    canonicalPrices u = 0 := by
  apply canonicalPrices_scaled_regular_gram (by omega : 2 ≤ d+2) u
    (regular_embedding_injective u hg) 1 (by norm_num)
  simpa only [one_pow,one_smul] using hg

theorem regular_embedding_winning_moment
    (u : Fin (d+2) → Space e) (hg : scoreGram u = regularCovariance (d+2))
    (i : Fin (d+2)) :
    (winningPartition u 0 (regular_embedding_injective u hg)).moment i =
      simplexConstant (d+2) • u i := by
  rw [← rawWinningMoment_eq]
  have h := balancedMoment_regular_embedding u hg i
  simpa only [balancedMoment,regular_embedding_zero_prices u hg] using h

theorem regular_embedding_winning_energy
    (u : Fin (d+2) → Space e) (hg : scoreGram u = regularCovariance (d+2)) :
    (winningPartition u 0 (regular_embedding_injective u hg)).momentEnergy = simplexConstant (d+2)^2 := by
  rw [← FractionalPartition.trace_scoreGram_moment]
  have hm : (winningPartition u 0 (regular_embedding_injective u hg)).moment =
      simplexConstant (d+2) • u := by funext i; exact regular_embedding_winning_moment u hg i
  rw [hm,scoreGram_smul,Matrix.trace_smul,hg,(regularCovariance_normalized (by omega)).2.2]
  simp

end GaussianMeasureBridge
