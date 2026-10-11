import ErdosSimilarityGrowingGaps.VariableLocalSigmaBridge

namespace ErdosSimilarityGrowingGaps

/-! A certificate constructor with the rate and schedule obligations exposed as
arguments.  The older constructor specializes these fields to
`lateActivationRate K δ D`; a separated local spacing needs the same data with
`δ` replaced by `σ` throughout the routing schedule. -/
noncomputable def finiteSequenceRoutingCertificate_of_rate_data
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hbranch : 2 ≤ M) (hdepth : 0 < d)
    (c : RoutingTemplate M d) (η : ℝ)
    (horigin : 4 ≤ c.origin) (hlength : 0 < c.baseLength)
    (hgap_guard : c.gap + 1 ≤ c.origin)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    (hcoeff : |(k : ℝ)| ≤ c.origin)
    (hdecay : 0 < p * η * ((M : ℝ) - 1) / 2 - 4 * Real.log 2)
    (hdefault : (1 - (2 : ℝ) ^ (1 - (M : ℝ))) ^ d ≤ p)
    (hstable : (Fintype.card (RoutingEdge M d) : ℝ) *
      (2 : ℝ) ^ (3 - (c.gap : ℝ)) ≤ p)
    (hentropy :
      46080 * (M : ℝ) ^ 2 * ((c.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * η * ((M : ℝ) - 1) / 2 - 4 * Real.log 2) *
          (c.baseLength : ℝ)) ≤ p)
    (witness : ∀ v : InternalNode M d,
      VariableRateNodeWitness (Z := Z) (K := K) (k := k) (p := p)
        c v η (vertexWindowLength c v))
    (hcandidate : ∀ v : InternalNode M d,
      (((M - 1) * ((witness v).B + 1) : ℕ) : ℝ) ≤
        (M : ℝ) * ((c.origin : ℝ) + RoutingTemplate.span M c.gap
          c.baseLength d + |(k : ℝ)| + 2)) :
    FiniteSequenceRoutingCertificate Z K k p := by
  let count : ∀ v : InternalNode M d, ℕ :=
    fun v => (M - 1) * ((witness v).B + 1)
  have hactive : ∀ (v : InternalNode M d)
      (r : PowerParams (1 / (K : ℝ)) K),
      η * ((M : ℝ) - 1) * (vertexWindowLength c v : ℝ) ≤
        (sequenceActiveLocalCandidates Z c v
          (fun i => (witness v).children i)
          (fun i => (witness v).indices i) k r).card := by
    intro v r
    exact (witness v).active_count r
  refine {
    branching := M
    depth := d
    template := c
    branching_ge_two := hbranch
    depth_pos := hdepth
    length_pos := hlength
    origin_guard := horigin
    gap_guard := hgap_guard
    span_fits := hspan
    coefficient_guard := hcoeff
    rate := η
    decay_pos := hdecay
    no_default_small := hdefault
    stable_boundary_small := hstable
    continuum_entropy_small := hentropy
    count := count
    children := fun v => (witness v).children
    indices := fun v => (witness v).indices
    index_injective := fun v => (witness v).index_injective
    logarithmic_gap := fun v => (witness v).logarithmic_gap
    active_count := by simpa [count] using hactive
    candidate_count := by
      intro v
      exact hcandidate v
  }

/-! A provider whose routing template is scheduled from the local spacing
`σ`.  The final density `δ` remains available for the outer blocker budget,
while all schedule fields (`M,d,g,rate`) are synchronized with `σ`. -/
structure WindowFillingLocalSigmaSequenceProvider (Z : LogScale) : Prop where
  build : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ)
    (p α q δ σ : ℝ),
    0 < p → 0 < α → 0 ≤ q → 0 < δ → δ < 1 → 6 * p < δ →
    0 < σ → 3 ≤ (1 / (K : ℝ)) * σ →
    ∀ (U : ℕ) (R D : ℝ),
      FillsAnnulus Z (U : ℝ) R D →
      ∃ c : FiniteSequenceRoutingCertificate Z K k p,
        c.template.origin = U ∧
        c.branching = lateBranching K p σ D ∧
        c.depth = lateDepth K p σ D ∧
        c.template.gap = lateStableGapExplicit K p σ D ∧
        c.rate = lateActivationRate K σ D ∧
        (∀ n ∈ finiteSequenceRoutingTests c, N ≤ n) ∧
        (∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
          n ∈ finiteSequenceRoutingTests c →
          r ∈ sequenceWindowActivations Z n k
            (globalRoutingWindows c.template) →
          q * (input Z n) ^ (r.1.1 + α) <
            routingBufferRadius c.template p)

theorem finiteSequenceBlockerSpec_of_windowFilling_local_sigma_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingLocalSigmaSequenceProvider Z) :
    FiniteSequenceBlockerSpec Z := by
  refine ⟨?_⟩
  intro K hK k N α q δ hα hq hδ hδ₁
  let p : ℝ := δ / 12
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hpδ : 6 * p < δ := by
    dsimp [p]
    nlinarith
  let σ : ℝ := 3 * (K : ℝ)
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  have hσsep : 3 ≤ (1 / (K : ℝ)) * σ := by
    dsimp [σ]
    have hKne : (K : ℝ) ≠ 0 := by
      exact_mod_cast (show K ≠ 0 by omega)
    field_simp [hKne]
    norm_num
  obtain ⟨U, D, hUN, hlog, hfill, _hratio⟩ :=
    WindowFilling.exists_late_annulus hW (4 * K) (by omega)
      (max (N : ℝ) 1) (K : ℝ) (by positivity)
      (by exact_mod_cast (show 0 < K by omega))
  have hD : 0 ≤ D := by
    linarith [hfill.2.2.1]
  have hfill' : FillsAnnulus Z (U : ℝ) (4 * (K : ℝ)) D := by
    simpa using hfill
  obtain ⟨c, horigin, hbranch, hdepth, hgap, hrate, htail, herror⟩ :=
    hP.build K hK k N p α q δ σ hp hα hq hδ hδ₁ hpδ hσ hσsep
      U (4 * (K : ℝ)) D hfill'
  refine ⟨p, hp, hpδ, c, hK, ?_⟩
  intro n hn
  exact ⟨htail n hn, fun r => herror r n⟩

end ErdosSimilarityGrowingGaps
