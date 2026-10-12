import Entry005.ActualSupportFirstVariationTest

/-! An explicitly open, literal finite-body Minkowski obligation and its
conditional passage to the same actual compact law and assignment. This module
proves no Minkowski theorem and adds no axiom. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Entry005

/-- The classical finite-Q first Minkowski inequality, stated with actual
supporting halfspaces, actual facet areas and actual ambient volume. It is a
proposition to be proved, never an axiom or a constructed witness. -/
def FiniteSupportMinkowskiObligation (d : ℕ) : Prop :=
  ∀ (ι : Type) (_ : Fintype ι) (n : ι → Space d) (h : ι → ℝ),
    (∀ i, ‖n i‖ = 1) → (∀ i, 0 < h i) → Function.Injective n →
    IsCompact (finiteHalfspaceSet n h) →
    closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h →
    ∀ (P : Set (Space d)), IsCompact P → Convex ℝ P → P.Nonempty →
      (volume P).toReal / (volume (finiteHalfspaceSet n h)).toReal ≤
        ((∑ i, finiteHalfspaceFacetArea n h i * compactSupportHeight P (n i)) /
          ((d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal)) ^ d

section ActualScaleGate

variable {d : ℕ} [Nontrivial (Space d)]

/-- Conditional only on the explicitly named finite Minkowski obligation:
actual volume convergence and exact facet-test convergence pass the finite
inequality to the same supplied μ and subsequence. -/
theorem actual_body_volume_ratio_le_support_test_pow_of_finite_minkowski
    (hMinkowski : FiniteSupportMinkowskiObligation d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hconvP : Convex ℝ P) (hneP : P.Nonempty) :
    (volume P).toReal / (volume K).toReal ≤
      (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ^ d := by
  have hvol := (halfspace_approximation_volume_tendsto K hc hconv hb).comp hφ.tendsto_atTop
  have hratio := (tendsto_const_nhds (x := (volume P).toReal) (f := atTop)).div hvol
    (compact_body_volume_pos_of_unit_ball K hc hb).ne'
  have htest := (actual_body_support_height_facet_sum_tendsto
    K hc hconv hb μ φ hlim P hcP hneP).pow d
  apply le_of_tendsto_of_tendsto' hratio htest
  intro k
  exact hMinkowski _ inferInstance _ _
    (halfspace_approximation_normals_unit K hc hconv hb (φ k))
    (halfspace_approximation_heights_pos K hc hconv hb (φ k))
    (halfspace_approximation_normals_injective K hc hconv hb (φ k))
    (halfspace_approximation_body_compact K hc hconv hb (φ k))
    (halfspace_approximation_body_contains_unit_ball K hc hconv hb (φ k))
    P hcP hconvP hneP

/-- The explicit finite obligation, plus the same actual assignment test,
gives the actual hscale needed by the parent scale/cap assembly. -/
theorem actual_body_assignment_volume_scale_of_finite_minkowski {n : ℕ}
    (hMinkowski : FiniteSupportMinkowskiObligation d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hconvP : Convex ℝ P) (hKP : K ⊆ P)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    (volume P).toReal / (volume K).toReal ≤
      (1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ^ d := by
  obtain ⟨_hi, _he, hlo, hup⟩ :=
    actual_body_enclosing_support_height_assignment_test_bounds K hc hconv hb μ φ hlim
      P hcP hKP M hM hbound w hw r hr
  exact (actual_body_volume_ratio_le_support_test_pow_of_finite_minkowski hMinkowski
    K hc hconv hb μ φ hφ hlim P hcP hconvP ⟨0, hKP (hb (by simp))⟩).trans
    (pow_le_pow_left₀ (le_trans (by norm_num) hlo) hup d)

end ActualScaleGate
end Entry005
