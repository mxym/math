import ErdosSimilarityGrowingGaps.VariableProviderAssembly
import ErdosSimilarityGrowingGaps.SelectorEndpointBounds
import ErdosSimilarityGrowingGaps.CanonicalEndpointBounds

namespace ErdosSimilarityGrowingGaps

/-! Certificate assembly with an independent local spacing parameter `σ`.
The schedule (`M,d,gap,rate`) is built from `σ`; the final density parameter
used by `FiniteSequenceBlockerSpec` is therefore absent from this constructor.
Taking `σ = 3K` is the canonical choice. -/
noncomputable def finiteSequenceRoutingCertificate_of_local_sigma_uniform_budget
    {Z : LogScale} {K : ℕ} {k : ℤ} {p σ D : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (c : RoutingTemplate M d)
    (hσ : 0 < σ) (hD : 0 ≤ D)
    (hM : M = lateBranching K p σ D)
    (hd : d = lateDepth K p σ D)
    (hgap : c.gap = lateStableGapExplicit K p σ D)
    (horigin : 4 ≤ c.origin) (hlength : 0 < c.baseLength)
    (hgap_guard : c.gap + 1 ≤ c.origin)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    (hcoeff : |(k : ℝ)| ≤ c.origin)
    (hentropy :
      46080 * (M : ℝ) ^ 2 * ((c.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * lateActivationRate K σ D * ((M : ℝ) - 1) / 2 -
          4 * Real.log 2) * (c.baseLength : ℝ)) ≤ p)
    (U R : ℝ) (hfill : FillsAnnulus Z U R D)
    (horigin_real : (c.origin : ℝ) = U)
    (hinput : ∀ v : InternalNode M d,
      VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D σ)
    (hDorigin : D ≤ (c.origin : ℝ))
    (hσK : 3 * (K : ℝ) ≤ σ) :
    FiniteSequenceRoutingCertificate Z K k p := by
  let T : ℝ := (c.origin : ℝ) +
    (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| + 2
  have hupper : ∀ v : InternalNode M d, ∀ child,
      (hinput v).u child + (hinput v).ell + (k : ℝ) ≤ T := by
    intro v child
    have hspanR : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ U := by
      have hspanR0 : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤
          (c.origin : ℝ) := by exact_mod_cast hspan
      simpa [horigin_real] using hspanR0
    have hh := canonical_selector_window_upper_exact c v
      (by rw [hM]; have hh := lateBranching_ge_two K p σ D; omega)
      hlength U k horigin_real hspanR
    dsimp [T]
    have hchild := hh child
    have hwin := (hinput v).hwindow child
    have hleft :
        (hinput v).u child + (hinput v).ell + (k : ℝ) =
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
            (vertexWindowLength c v : ℝ) + (k : ℝ) := by
      rw [← hwin.1, (hinput v).ell_eq]
    calc
      (hinput v).u child + (hinput v).ell + (k : ℝ) =
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
            (vertexWindowLength c v : ℝ) + (k : ℝ) := hleft
      _ ≤ U + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| :=
        hchild
      _ ≤ (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) +
          |(k : ℝ)| + 2 := by rw [horigin_real]; linarith
  have hQcandidate : (((M - 1) *
      (variableNodeUniformBudget K T D σ + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * ((c.origin : ℝ) +
        (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| + 2) := by
    dsimp [T]
    exact variable_uniform_candidate_count_of_template hK c σ D hσK hD
      horigin (by exact_mod_cast hspan) hcoeff hDorigin
  exact finiteSequenceRoutingCertificate_of_template_uniform_budget
    hK hp hp₁ c σ D hσ hD hM hd hgap horigin hlength
    hgap_guard hspan hcoeff hentropy U R hfill (hinput) T hupper hQcandidate

end ErdosSimilarityGrowingGaps
