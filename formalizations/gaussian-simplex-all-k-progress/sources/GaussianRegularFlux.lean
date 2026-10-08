import GaussianRegularGramMoments
import GaussianIntrinsicInnerPerimeter
import GaussianPrincipalNondegeneracy
import GaussianRegularPrincipal

/-! Unique normal-basis coefficients identify every regular facet weight.
Their proved strict positivity also proves positivity of the sharp constant.
All statements here are unconditional. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e k : ℕ} [NeZero k]

lemma centered_uniform_flux (v : Fin k → Space e) (hz : ∑ i,v i = 0)
    (c : ℝ) (i : Fin k) : c • v i = ∑ j,(c/(k:ℝ)) • (v i-v j) := by
  have hk : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  rw [← Finset.smul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,hz,sub_zero]
  simp only [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [div_mul_cancel₀ _ hk]

theorem simplicial_flux_coefficients_unique
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (a c : Fin (d+2) → Fin (d+2) → ℝ)
    (he : ∀ i,(∑ j,a i j • (v i-v j)) = ∑ j,c i j • (v i-v j)) :
    ∀ i j,i ≠ j → a i j = c i j := by
  classical
  intro i j hij
  let p : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
  obtain ⟨B,hB⟩ := simplicial_normal_basis (v ∘ p) (hv.comp_embedding p.toEmbedding)
  have hsum (f : Fin (d+2) → ℝ) :
      (∑ r : Fin (d+1),f (p r.succ) • B r) = ∑ r,f r • (v i-v r) := by
    calc
      _ = ∑ r,f (p r) • (v i-v (p r)) := by simp [hB,Fin.sum_univ_succ,p]
      _ = _ := Equiv.sum_comp p (fun r => f r • (v i-v r))
  have hc := basis_flux_weights_unique B (fun r => a i (p r.succ)) (fun r => c i (p r.succ))
    (by rw [hsum,hsum]; exact he i)
  have hj : p j ≠ 0 := by
    intro hj
    have hh := congrArg p hj
    simp [p] at hh
    exact hij hh.symm
  rcases Fin.eq_zero_or_eq_succ (p j) with h0 | ⟨r,hr⟩
  · exact (hj h0).elim
  · have hh := congrFun hc r
    have hpr : p r.succ = j := by
      have heq := congrArg p hr
      simpa [p] using heq.symm
    simpa only [hpr] using hh

theorem regular_gram_flux_weights
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i = 0) (hg : scoreGram v = regularCovariance (d+2))
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hf : ∀ i,balancedMoment v i = ∑ j,w i j • (v i-v j)) :
    ∀ i j,i ≠ j → w i j = simplexConstant (d+2)/(d+2:ℕ) := by
  apply simplicial_flux_coefficients_unique v hv w
    (fun _ _ => simplexConstant (d+2)/(d+2:ℕ))
  intro i
  rw [← hf i,balancedMoment_regular_gram v hv hz hg i]
  exact centered_uniform_flux v hz _ i

theorem simplexConstant_positive : 0 < simplexConstant (d+2) := by
  let v := minimalCovarianceRows (regularCovariance (d+2))
  have hR := regularCovariance_normalized (k := d+2) (by omega)
  have hv : AffineIndependent ℝ v := minimalCovarianceRows_affineIndependent _ regular_principal_posDef
  have hz : ∑ i,v i = 0 := minimalCovarianceRows_sum _
  have hg : scoreGram v = regularCovariance (d+2) := scoreGram_minimalCovarianceRows _ hR.1 hR.2.1
  obtain ⟨w,hw,hp,hs,hf,hc⟩ := actual_balanced_flux_energy v hv
  have h01 : (0:Fin (d+2)) ≠ 1 := by
    simp [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<d+2)]
  have he := regular_gram_flux_weights v hv hz hg w hf 0 1 h01
  have hh := hp 0 1 h01
  rw [he] at hh
  exact (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < (d+2:ℕ))).mp hh

end GaussianMeasureBridge
