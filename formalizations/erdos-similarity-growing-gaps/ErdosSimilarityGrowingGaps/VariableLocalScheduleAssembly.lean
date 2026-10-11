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

/-! The bounded form is convenient when the separated-`σ` endpoint estimate
supplies one common natural budget `Q`. -/
noncomputable def finiteSequenceRoutingCertificate_of_rate_bounded_data
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
    (Q : ℕ)
    (witness : ∀ v : InternalNode M d,
      VariableRateNodeWitnessBounded (Z := Z) (K := K) (k := k) (p := p)
        c v η (vertexWindowLength c v) Q)
    (hcandidate : (((M - 1) * (Q + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * ((c.origin : ℝ) + RoutingTemplate.span M c.gap
        c.baseLength d + |(k : ℝ)| + 2)) :
    FiniteSequenceRoutingCertificate Z K k p := by
  let witness' : ∀ v : InternalNode M d,
      VariableRateNodeWitness (Z := Z) (K := K) (k := k) (p := p)
        c v η (vertexWindowLength c v) := fun v => {
    B := (witness v).B
    children := (witness v).children
    indices := (witness v).indices
    active_count := (witness v).active_count
    index_injective := (witness v).index_injective
    logarithmic_gap := (witness v).logarithmic_gap
  }
  apply finiteSequenceRoutingCertificate_of_rate_data hbranch hdepth c η
    horigin hlength hgap_guard hspan hcoeff hdecay hdefault hstable hentropy
    witness'
  intro v
  have hB := (witness v).B_le
  have hadd : (witness v).B + 1 ≤ Q + 1 := Nat.add_le_add_right hB 1
  have hmul : (M - 1) * ((witness v).B + 1) ≤ (M - 1) * (Q + 1) :=
    Nat.mul_le_mul_left _ hadd
  have hmul' : (((M - 1) * ((witness v).B + 1) : ℕ) : ℝ) ≤
      (((M - 1) * (Q + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmul
  exact hmul'.trans hcandidate

/-! Assemble the local bounded greedy witnesses from per-node inputs.  This
is the direct all-node bridge; callers still provide the explicit geometric
guards recorded by `VariableRateNodeInput`. -/
noncomputable def variableRateBoundedWitness_of_local_inputs
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (c : RoutingTemplate M d) (U R D σ η : ℝ)
    (hfill : FillsAnnulus Z U R D) (hM : 2 ≤ M)
    (hσ : 0 < σ) (hD : 0 ≤ D)
    (hη : ∀ v : InternalNode M d,
      η * (vertexWindowLength c v : ℝ) ≤
        (vertexWindowLength c v : ℝ) /
          (2 * ((K : ℝ) * (σ + D))))
    (hinput : ∀ v : InternalNode M d,
      VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D σ)
    (Q : ℕ)
    (hQ : ∀ v : InternalNode M d, ∀ child,
      max ((((hinput v).u child + (hinput v).ell + (k : ℝ)) /
        (1 / (K : ℝ)) -
        (((hinput v).u child + (k : ℝ)) / (K : ℝ) - D)) / σ) 0 + 1 ≤
          (Q : ℝ)) :
    ∀ v : InternalNode M d,
      VariableRateNodeWitnessBounded (Z := Z) (K := K) (k := k) (p := p)
        c v η (vertexWindowLength c v) Q := by
  intro v
  let hv := variableRateNodeWitness_of_local_input_bounded
    (p := p) hK c v U R D σ η hfill hM hσ hD (hη v)
    (hinput v) Q (hQ v)
  have hv' : Nonempty (VariableRateNodeWitnessBounded (Z := Z) (K := K)
      (k := k) (p := p) c v η (vertexWindowLength c v) Q) := by
    simpa only [(hinput v).ell_eq] using hv
  exact Classical.choice hv'

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
