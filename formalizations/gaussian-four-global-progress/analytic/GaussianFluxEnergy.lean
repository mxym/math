import GaussianSymmetricFlux
import GaussianSimplexAlgebra

/-! Energy and Cauchy identities for the symmetric coefficients already
constructed from actual Gaussian winning integrals. No perimeter comparison
is assumed in these identities. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def fluxPerimeter (v : Fin k → Space d) (w : Fin k → Fin k → ℝ) : ℝ :=
  (∑ i, ∑ j, w i j * ‖v i - v j‖) / 2

noncomputable def fluxTrace (w : Fin k → Fin k → ℝ) : ℝ := ∑ i, ∑ j, w i j

lemma symmetric_flux_energy (v m : Fin k → Space d) (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) :
    (∑ i, ⟪v i,m i⟫) = (∑ i, ∑ j, w i j * ‖v i - v j‖^2) / 2 := by
  have hn (i j : Fin k) : ‖v i - v j‖^2 =
      ⟪v i,v i - v j⟫ + ⟪v j,v j - v i⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right]
    ring
  have he : (∑ i, ⟪v i,m i⟫) = ∑ i, ∑ j, w i j * ⟪v i,v i - v j⟫ := by
    simp only [hf,inner_sum,real_inner_smul_right]
  have hswap : (∑ i, ∑ j, w i j * ⟪v j,v j - v i⟫) =
      ∑ i, ∑ j, w i j * ⟪v i,v i - v j⟫ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  simp_rw [hn,mul_add]
  simp_rw [Finset.sum_add_distrib]
  rw [hswap,he]
  ring

theorem actual_balanced_flux_energy
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment v i = ∑ j, w i j • (v i - v j)) ∧
      equalMassValue v = (∑ i, ∑ j, w i j * ‖v i - v j‖^2) / 2 := by
  obtain ⟨w,hd,hp,hs,hf⟩ := gaussian_symmetric_positive_flux v (canonicalPrices v) hv
  have hb (i : Fin (d+2)) : balancedMoment v i = ∑ j, w i j • (v i - v j) := hf i
  refine ⟨w,hd,hp,hs,hb,?_⟩
  rw [← balancedMoment_value v hv.injective]
  exact symmetric_flux_energy v _ w hs hb

theorem actual_flux_cauchy (v : Fin k → Space d) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) :
    (fluxPerimeter v w)^2 ≤ fluxTrace w *
      ((∑ i, ∑ j, w i j * ‖v i - v j‖^2) / 2) / 2 := by
  have hc := GaussianSimplexAlgebra.weighted_cauchy
    (Finset.univ : Finset (Fin k × Fin k)) (fun z => w z.1 z.2)
    (fun z => ‖v z.1 - v z.2‖) (fun z _ => hw z.1 z.2)
  simp only [Fintype.sum_prod_type] at hc
  unfold fluxPerimeter fluxTrace
  nlinarith

end GaussianMeasureBridge
