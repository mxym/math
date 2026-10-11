import ErdosSimilarityGrowingGaps.SequenceFiniteAssembly
import ErdosSimilarityGrowingGaps.SequenceSignatures
import ErdosSimilarityGrowingGaps.GlobalGreedyTests
import ErdosSimilarityGrowingGaps.SequenceTransferFill
import ErdosSimilarityGrowingGaps.SequenceGreedyFamily
import ErdosSimilarityGrowingGaps.VariableRateSchedule

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open Filter Topology Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The finite hypotheses of the sequence blocker lemma.  The branching,
depth, activation rate, and candidate lists are arbitrary finite data.  In
particular they can vary together with the width of the supplied annulus. -/
structure FiniteSequenceRoutingCertificate
    (Z : LogScale) (K : ℕ) (k : ℤ) (p : ℝ) where
  branching : ℕ
  depth : ℕ
  template : RoutingTemplate branching depth
  branching_ge_two : 2 ≤ branching
  depth_pos : 0 < depth
  length_pos : 0 < template.baseLength
  origin_guard : 4 ≤ template.origin
  gap_guard : template.gap + 1 ≤ template.origin
  span_fits : RoutingTemplate.span branching template.gap template.baseLength depth ≤
    template.origin
  coefficient_guard : |(k : ℝ)| ≤ template.origin
  rate : ℝ
  decay_pos : 0 < p * rate * ((branching : ℝ) - 1) / 2 - 4 * Real.log 2
  no_default_small : (1 - (2 : ℝ) ^ (1 - (branching : ℝ))) ^ depth ≤ p
  stable_boundary_small : (Fintype.card (RoutingEdge branching depth) : ℝ) *
    (2 : ℝ) ^ (3 - (template.gap : ℝ)) ≤ p
  continuum_entropy_small :
    46080 * (branching : ℝ) ^ 2 * ((template.origin : ℝ) + 1) ^ 2 *
      Real.exp (-(p * rate * ((branching : ℝ) - 1) / 2 -
        4 * Real.log 2) * (template.baseLength : ℝ)) ≤ p
  count : InternalNode branching depth → ℕ
  children : ∀ v, Fin (count v) → Fin (branching - 1)
  indices : ∀ v, Fin (count v) → ℕ
  index_injective : ∀ v, Function.Injective (fun i => (children v i, indices v i))
  logarithmic_gap : ∀ v i j, i ≠ j → children v i = children v j →
    3 ≤ (1 / (K : ℝ)) * |Z.z (indices v j) - Z.z (indices v i)|
  active_count : ∀ v (r : PowerParams (1 / (K : ℝ)) K),
    rate * ((branching : ℝ) - 1) * (vertexWindowLength template v : ℝ) ≤
      (sequenceActiveLocalCandidates Z template v (children v) (indices v) k r).card
  candidate_count : ∀ v, (count v : ℝ) ≤ (branching : ℝ) *
    ((template.origin : ℝ) + RoutingTemplate.span branching template.gap
      template.baseLength depth + |(k : ℝ)| + 2)

/-! The next two structures isolate the genuinely combinatorial part of a
variable-rate schedule.  A node input records the hypotheses needed by the
common greedy-family lemma; its output has exactly the dependent finite types
used by the certificate.  Keeping these as data makes the remaining bridge
from a filled annulus auditable: no existential choice is hidden in a
probability or asymptotic theorem. -/

structure VariableRateNodeInput
    {Z : LogScale} {K : ℕ} {k : ℤ} {M d : ℕ}
    (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D δ : ℝ) where
  u : Fin (M - 1) → ℝ
  ell : ℝ
  ha : ∀ child, U / R ≤ (u child + (k : ℝ)) / (K : ℝ) - D
  ha_hi : ∀ child, (u child + (k : ℝ)) / (K : ℝ) ≤ R * U
  hnum : ∀ child, 0 ≤ u child + ell + (k : ℝ)
  huk : ∀ child, 0 ≤ u child + (k : ℝ)
  ell_eq : ell = vertexWindowLength c v
  hwindow : ∀ child,
    c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) = u child ∧
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
      c.edgeLength (RoutingTemplate.selectorRoutingEdge
        ⟨v, child⟩) = u child + ell
  hell : 2 * ((K : ℝ) * (δ + D)) ≤ ell
  hannulus : ∀ child,
    (u child + ell + (k : ℝ)) / (1 / (K : ℝ)) + δ + D ≤ R * U
  hsep : 3 ≤ (1 / (K : ℝ)) * δ

structure VariableRateNodeWitness
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (c : RoutingTemplate M d) (v : InternalNode M d)
    (η ell : ℝ) where
  B : ℕ
  children : Fin ((M - 1) * (B + 1)) → Fin (M - 1)
  indices : Fin ((M - 1) * (B + 1)) → ℕ
  active_count : ∀ r : PowerParams (1 / (K : ℝ)) K,
    η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k r).card
  index_injective : Function.Injective (fun i => (children i, indices i))
  logarithmic_gap : ∀ i j, i ≠ j → children i = children j →
    3 ≤ (1 / (K : ℝ)) * |Z.z (indices j) - Z.z (indices i)|

structure VariableRateNodeWitnessBounded
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (c : RoutingTemplate M d) (v : InternalNode M d)
    (η ell : ℝ) (Q : ℕ) where
  B : ℕ
  children : Fin ((M - 1) * (B + 1)) → Fin (M - 1)
  indices : Fin ((M - 1) * (B + 1)) → ℕ
  active_count : ∀ r : PowerParams (1 / (K : ℝ)) K,
    η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k r).card
  index_injective : Function.Injective (fun i => (children i, indices i))
  logarithmic_gap : ∀ i j, i ≠ j → children i = children j →
    3 ≤ (1 / (K : ℝ)) * |Z.z (indices j) - Z.z (indices i)|
  B_le : B ≤ Q

/-! Any eventual little-o span estimate yields the exact integer-origin guard
  needed by the certificate.  This isolates the remaining asymptotic task from
  the finite tree construction. -/
theorem eventually_real_span_le_origin
    {ι : Type*} {l : Filter ι} {span origin : ι → ℝ}
    (hspan : span =o[l] origin)
    (horigin : ∀ᶠ i in l, 0 < origin i) :
    ∀ᶠ i in l, span i ≤ origin i := by
  have hbound := hspan.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, horigin] with i hi hOi
  have hnormO : ‖origin i‖ = origin i := by
    rw [Real.norm_eq_abs, abs_of_pos hOi]
  have hnormS : ‖span i‖ = |span i| := Real.norm_eq_abs _
  rw [hnormS, hnormO] at hi
  exact (le_abs_self (span i)).trans (by simpa using hi)

theorem eventually_nat_span_le_origin
    {ι : Type*} {l : Filter ι} {span origin : ι → ℕ}
    (hspan : (fun i => (span i : ℝ)) =o[l]
      (fun i => (origin i : ℝ)))
    (horigin : ∀ᶠ i in l, 0 < origin i) :
    ∀ᶠ i in l, span i ≤ origin i := by
  have hpos : ∀ᶠ i in l, 0 < (origin i : ℝ) := by
    filter_upwards [horigin] with i hi
    exact_mod_cast hi
  have hreal := eventually_real_span_le_origin hspan hpos
  filter_upwards [hreal] with i hi
  exact_mod_cast hi

theorem littleO_of_eventually_nonneg_le
    {ι : Type*} {l : Filter ι} {f g h U : ι → ℝ}
    (hfg : (fun i => f i + g i) =o[l] U)
    (hU : ∀ᶠ i in l, 0 ≤ U i)
    (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hbound : ∀ᶠ i in l, h i ≤ f i + g i) :
    h =o[l] U := by
  apply IsLittleO.of_bound
  intro c hc
  have hfgc := hfg.bound hc
  filter_upwards [hfgc, hU, hh, hbound] with i hi hUi hhi hbi
  have hsum : 0 ≤ f i + g i := hhi.trans hbi
  have hUi' : ‖U i‖ = U i := by
    rw [Real.norm_eq_abs, abs_of_nonneg hUi]
  have hhi' : ‖h i‖ = h i := by
    rw [Real.norm_eq_abs, abs_of_nonneg hhi]
  have hi' : f i + g i ≤ c * U i := by
    have hsum' : ‖f i + g i‖ = f i + g i := by
      rw [Real.norm_eq_abs, abs_of_nonneg hsum]
    rw [hsum', hUi'] at hi
    exact hi
  rw [hhi', hUi']
  exact hbi.trans hi'

/-! The common greedy-family construction now feeds the dependent witness
  directly.  This is the first concrete bridge from an annulus to certificate
  lists: all choices are made by the existing finite supremum construction,
  and the only rate arithmetic is the explicit late-rate fill inequality. -/
theorem variableRateNodeWitness_of_input
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D δ : ℝ) (hfill : FillsAnnulus Z U R D)
    (hM : 2 ≤ M) (hδ : 0 < δ) (hD : 0 ≤ D)
    (hnode : VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D δ) :
    Nonempty (VariableRateNodeWitness (Z := Z) (K := K) (k := k) (p := p) c v
      (lateActivationRate K δ D) hnode.ell) := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hs₀ : 0 < (1 / (K : ℝ)) := by positivity
  have hs₁ : 0 < (K : ℝ) := hKpos
  have hell_nonneg : 0 ≤ hnode.ell := by
    have hKD : 0 < (K : ℝ) * (δ + D) := by positivity
    nlinarith [hnode.hell]
  have hη := lateActivationRate_fill_bound K hK δ D hnode.ell
    hδ hD hell_nonneg
  obtain ⟨B, children, indices, hactive, hinj, hlog⟩ :=
    exists_common_greedy_family (s₀ := 1 / (K : ℝ)) (s₁ := (K : ℝ))
      Z c v k hnode.u hnode.ell D δ (lateActivationRate K δ D)
      (U := U) (R := R) hfill hM hs₀ hs₁ hδ
      hnode.ha hnode.ha_hi hnode.hnum hnode.huk hnode.hwindow hnode.hell
      hnode.hannulus (by simpa using hη) hnode.hsep
  exact ⟨{
    B := B
    children := children
    indices := indices
    active_count := hactive
    index_injective := hinj
    logarithmic_gap := hlog
  }⟩

theorem variableRateNodeWitness_of_input_bounded
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D δ : ℝ) (hfill : FillsAnnulus Z U R D)
    (hM : 2 ≤ M) (hδ : 0 < δ) (hD : 0 ≤ D)
    (hnode : VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D δ)
    (Q : ℕ)
    (hQ : ∀ child, max (((hnode.u child + hnode.ell + (k : ℝ)) /
      (1 / (K : ℝ)) -
      ((hnode.u child + (k : ℝ)) / (K : ℝ) - D)) / δ) 0 + 1 ≤ (Q : ℝ)) :
    Nonempty (VariableRateNodeWitnessBounded (Z := Z) (K := K) (k := k)
      (p := p) c v (lateActivationRate K δ D) hnode.ell Q) := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hs₀ : 0 < (1 / (K : ℝ)) := by positivity
  have hs₁ : 0 < (K : ℝ) := hKpos
  have hell_nonneg : 0 ≤ hnode.ell := by
    have hKD : 0 < (K : ℝ) * (δ + D) := by positivity
    nlinarith [hnode.hell]
  have hη := lateActivationRate_fill_bound K hK δ D hnode.ell
    hδ hD hell_nonneg
  obtain ⟨B, children, indices, hactive, hinj, hlog, hBQ⟩ :=
    exists_common_greedy_family_bounded (s₀ := 1 / (K : ℝ))
      (s₁ := (K : ℝ)) Z c v k hnode.u hnode.ell D δ
      (lateActivationRate K δ D) (U := U) (R := R) hfill hM hs₀ hs₁ hδ
      hnode.ha hnode.ha_hi hnode.hnum hnode.huk hnode.hwindow hnode.hell
      hnode.hannulus (by simpa using hη) hnode.hsep Q (by
        intro child
        simpa using hQ child)
  exact ⟨{
    B := B
    children := children
    indices := indices
    active_count := hactive
    index_injective := hinj
    logarithmic_gap := hlog
    B_le := hBQ
  }⟩

/-! Assemble all node witnesses into the finite certificate.  The hypotheses
  named `hspan`, `hentropy`, and `hcandidate` are the remaining geometric
  envelopes; the scalar late schedule obligations are discharged here from
  `VariableRateSchedule`. -/
noncomputable def finiteSequenceRoutingCertificate_of_variable_rate_data
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (c : RoutingTemplate M d) (δ D : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hM : M = lateBranching K p δ D)
    (hd : d = lateDepth K p δ D)
    (hgap : c.gap = lateStableGapExplicit K p δ D)
    (horigin : 4 ≤ c.origin)
    (hlength : 0 < c.baseLength)
    (hgap_guard : c.gap + 1 ≤ c.origin)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    (hcoeff : |(k : ℝ)| ≤ c.origin)
    (hentropy :
      46080 * (M : ℝ) ^ 2 * ((c.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * lateActivationRate K δ D * ((M : ℝ) - 1) / 2 -
          4 * Real.log 2) * (c.baseLength : ℝ)) ≤ p)
    (witness : ∀ v : InternalNode M d,
      VariableRateNodeWitness (Z := Z) (K := K) (k := k) (p := p)
        c v (lateActivationRate K δ D) (vertexWindowLength c v))
    (hcandidate : ∀ v : InternalNode M d,
      (((M - 1) * ((witness v).B + 1) : ℕ) : ℝ) ≤
        (M : ℝ) * ((c.origin : ℝ) + RoutingTemplate.span M c.gap
          c.baseLength d + |(k : ℝ)| + 2)) :
    FiniteSequenceRoutingCertificate Z K k p := by
  let η : ℝ := lateActivationRate K δ D
  have hbranch : 2 ≤ M := by
    rw [hM]
    exact lateBranching_ge_two K p δ D
  have hdepth : 0 < d := by
    rw [hd]
    exact lateDepth_pos K hK p δ D hp hp₁ hδ hD
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
  have hstable :
      (Fintype.card (RoutingEdge M d) : ℝ) *
        (2 : ℝ) ^ (3 - (c.gap : ℝ)) ≤ p := by
    have hg := lateStableGapExplicit_spec K p δ D hp
    simpa [hM, hd, hgap] using hg.le
  have hdefault := lateDepth_default_budget K hK p δ D hp hp₁ hδ hD
  have hdecay := lateBranching_decay_pos K hK p δ D hp hδ hD
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
    decay_pos := by simpa [η, hM] using hdecay
    no_default_small := by simpa [hM, hd] using hdefault
    stable_boundary_small := hstable
    continuum_entropy_small := by simpa [η] using hentropy
    count := count
    children := fun v => (witness v).children
    indices := fun v => (witness v).indices
    index_injective := fun v => (witness v).index_injective
    logarithmic_gap := fun v => (witness v).logarithmic_gap
    active_count := by simpa [η] using hactive
    candidate_count := by
      intro v
      exact hcandidate v
  }

noncomputable def finiteSequenceRoutingCertificate_of_variable_rate_bounded_data
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (c : RoutingTemplate M d) (δ D : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hM : M = lateBranching K p δ D)
    (hd : d = lateDepth K p δ D)
    (hgap : c.gap = lateStableGapExplicit K p δ D)
    (horigin : 4 ≤ c.origin)
    (hlength : 0 < c.baseLength)
    (hgap_guard : c.gap + 1 ≤ c.origin)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    (hcoeff : |(k : ℝ)| ≤ c.origin)
    (hentropy :
      46080 * (M : ℝ) ^ 2 * ((c.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * lateActivationRate K δ D * ((M : ℝ) - 1) / 2 -
          4 * Real.log 2) * (c.baseLength : ℝ)) ≤ p)
    (Q : ℕ)
    (witness : ∀ v : InternalNode M d,
      VariableRateNodeWitnessBounded (Z := Z) (K := K) (k := k) (p := p)
        c v (lateActivationRate K δ D) (vertexWindowLength c v) Q)
    (hQcandidate : (((M - 1) * (Q + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * ((c.origin : ℝ) + RoutingTemplate.span M c.gap
        c.baseLength d + |(k : ℝ)| + 2)) :
    FiniteSequenceRoutingCertificate Z K k p := by
  let witness' : ∀ v : InternalNode M d,
      VariableRateNodeWitness (Z := Z) (K := K) (k := k) (p := p)
        c v (lateActivationRate K δ D) (vertexWindowLength c v) := fun v => {
    B := (witness v).B
    children := (witness v).children
    indices := (witness v).indices
    active_count := (witness v).active_count
    index_injective := (witness v).index_injective
    logarithmic_gap := (witness v).logarithmic_gap
  }
  apply finiteSequenceRoutingCertificate_of_variable_rate_data hK hp hp₁ c δ D
    hδ hD hM hd hgap horigin hlength hgap_guard hspan hcoeff hentropy witness'
  intro v
  have hB := (witness v).B_le
  have hadd : (witness v).B + 1 ≤ Q + 1 := Nat.add_le_add_right hB 1
  have hmul : (M - 1) * ((witness v).B + 1) ≤ (M - 1) * (Q + 1) :=
    Nat.mul_le_mul_left _ hadd
  have hmul' : (((M - 1) * ((witness v).B + 1) : ℕ) : ℝ) ≤
      (((M - 1) * (Q + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmul
  exact hmul'.trans hQcandidate

/-- The one common finite test set contains each vertex's own finite list. -/
noncomputable def finiteSequenceRoutingTests
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p) : Finset ℕ :=
  Finset.univ.biUnion (fun v : InternalNode s.branching s.depth =>
    (Finset.univ : Finset (Fin (s.count v))).image (s.indices v))

theorem mem_finiteSequenceRoutingTests
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p)
    (v : InternalNode s.branching s.depth) (i : Fin (s.count v)) :
    s.indices v i ∈ finiteSequenceRoutingTests s := by
  apply Finset.mem_biUnion.mpr
  refine ⟨v, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem finiteSequenceRoutingTests_card_le
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p) :
    (finiteSequenceRoutingTests s).card ≤ ∑ v, s.count v := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro v hv
  exact Finset.card_image_le.trans_eq (by simp)

/-- A missed center forces the actual finite sequence miss event at the
default vertex, using that vertex's own candidate list. -/
theorem sequence_certificate_missed_center_forces_vertex_miss
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p) (hp : 0 < p)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template)
    (bits : SelectorEdge s.branching s.depth → Bool)
    (ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos))
    (hσ : centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors)
    (v : InternalNode s.branching s.depth)
    (hprefix : (List.ofFn v.2).IsPrefix (List.ofFn
      (routeLeaf s.template (by have := s.branching_ge_two; omega) ω.selectors x)))
    (hdefault : ∀ i : Fin (s.branching - 1), bits ⟨v, i⟩ = false)
    (hmiss : x ∈ sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (finiteSequenceRoutingTests s) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) :
    ∃ r : PowerParams (1 / (K : ℝ)) K,
      sequenceLocalAllMiss Z s.template
        (by have := s.branching_ge_two; omega) s.depth_pos
        (1 / (K : ℝ)) K x k (fun i => ⟨v, s.children v i⟩) (s.indices v) r ω := by
  obtain ⟨r, hr⟩ := (mem_missedCenters_iff _ _ _ x).1 hmiss
  refine ⟨r, ?_⟩
  intro i hi hsuccess
  let e : RoutingEdge s.branching s.depth :=
    RoutingTemplate.selectorRoutingEdge ⟨v, s.children v i⟩
  have hactive : r ∈ sequenceWindowActivations Z (s.indices v i) k
      (globalRoutingWindows s.template) := by
    apply Set.mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration s.branching s.depth).symm e, ?_⟩
    dsimp [e]
    simp only [globalRoutingWindows, Equiv.apply_symm_apply]
    exact hi
  apply hr ⟨s.indices v i, mem_finiteSequenceRoutingTests s v i⟩ hactive
  apply Metric.self_subset_thickening (routingBufferRadius_pos s.template p hp)
  exact sequence_stable_local_success_mem_routedSet Z s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos s.gap_guard
    (1 / (K : ℝ)) K x (s.indices v i) k r ω bits hσ v (s.children v i)
    hprefix hdefault hx hi hsuccess

/-- The numerical guards in the certificate discharge the full continuum
union bound for each vertex, including all parameter boundary strata. -/
theorem sequence_certificate_vertex_probability_le
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p)
    (hK : 2 ≤ K) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : ℝ) (bits : SelectorEdge s.branching s.depth → Bool)
    (v : InternalNode s.branching s.depth) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
      ∃ r : PowerParams (1 / (K : ℝ)) K,
        sequenceLocalAllMiss Z s.template
          (by have := s.branching_ge_two; omega) s.depth_pos
          (1 / (K : ℝ)) K x k (fun i => ⟨v, s.children v i⟩) (s.indices v) r ω) ≤
      tableProbability (T := TerminalAddress s.template s.depth_pos) p
        (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p := by
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hs : 1 / (K : ℝ) ≤ (K : ℝ) := by
    have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    apply (div_le_iff₀ hK₀).2
    nlinarith
  have hb := sequence_continuum_joint_miss_bound_of_lower_gap Z s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos s.origin_guard
    p (1 / (K : ℝ)) K x s.rate hp₀ hp₁ hs k bits v
    (s.children v) (s.indices v) (vertexWindowLength s.template v)
    (fun _ => rfl) (s.index_injective v) (s.logarithmic_gap v) (s.active_count v)
  have hbase : s.template.baseLength ≤ vertexWindowLength s.template v :=
    RoutingTemplate.base_le_length _ _ _ _ (by have := s.branching_ge_two; omega)
  have he := (signature_entropy_position_bound s.branching (s.count v)
    s.template.origin
    (RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth)
    (vertexWindowLength s.template v) s.template.baseLength (k : ℝ)
    (p * s.rate * ((s.branching : ℝ) - 1) / 2)
    (by have := s.branching_ge_two; omega) s.span_fits s.coefficient_guard
    (s.candidate_count v) hbase s.decay_pos).trans s.continuum_entropy_small
  have ha := tableProbability_nonneg (T := TerminalAddress s.template s.depth_pos)
    p hp₀ hp₁
    (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors)
  apply hb.trans
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
    mul_le_mul_of_nonneg_left he ha

/-- Summing center exposure atoms and the no-default event gives the global
missed-center bound.  Candidate lengths may depend on the default vertex. -/
theorem sequence_certificate_stable_probability_le
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p)
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template) :
    tableProbability p (fun ω => x ∈ sequenceMissedCenters
      (s₀ := 1 / (K : ℝ)) (s₁ := K) Z (finiteSequenceRoutingTests s) k
      (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) ≤ 2 * p := by
  let hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let E := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    x ∈ sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (finiteSequenceRoutingTests s) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template hM s.depth_pos p ω)
  let D := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    routeHasNoDefault s.template hM ω.selectors x
  have hD : tableProbability p D ≤ p := by
    rw [actual_routeHasNoDefault_probability_rpow s.template hM s.depth_pos p x]
    exact s.no_default_small
  have hdefault : tableProbability p (fun ω => E ω ∧ ¬ D ω) ≤ p := by
    rw [actual_center_atom_partition s.template s.depth_pos p x]
    have hbits (bits : SelectorEdge s.branching s.depth → Bool) :
        tableProbability p (fun ω =>
          centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
          (E ω ∧ ¬D ω)) ≤
        tableProbability (T := TerminalAddress s.template s.depth_pos) p
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p := by
      by_cases hd : routeHasNoDefault s.template hM
          (centerTableAssignment s.template bits) x
      · have heq : tableProbability p (fun ω =>
            centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω)) = 0 := by
          apply (tableProbability_congr p _ (fun _ => False) ?_).trans
            (tableProbability_false p)
          intro ω
          constructor
          · rintro ⟨ha, _, hn⟩
            apply hn
            exact (center_atom_noDefault_iff s.template hM x bits ω.selectors
              (centerTableAssignment s.template bits)
              ha (centerTableAssignment_satisfies_atom s.template x bits)).2 hd
          · exact False.elim
        rw [heq]
        exact mul_nonneg (tableProbability_nonneg p hp.le hp₁ _) hp.le
      · obtain ⟨v, hv, hprefix⟩ := center_atom_default_vertex_exists
          s.template hM x bits hd
        have hmono := tableProbability_mono p hp.le hp₁
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω)) (fun ω =>
            centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            ∃ r : PowerParams (1 / (K : ℝ)) K,
              sequenceLocalAllMiss Z s.template hM s.depth_pos
                (1 / (K : ℝ)) K x k (fun i => ⟨v, s.children v i⟩) (s.indices v) r ω) (by
              intro ω hω
              exact ⟨hω.1, sequence_certificate_missed_center_forces_vertex_miss
                s hp x hx bits ω hω.1 v
                (hprefix ω.selectors hω.1) hv hω.2.1⟩)
        exact hmono.trans (sequence_certificate_vertex_probability_le
          s hK hp.le hp₁ x bits v)
    calc
      _ ≤ ∑ bits : SelectorEdge s.branching s.depth → Bool,
          tableProbability (T := TerminalAddress s.template s.depth_pos) p
            (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p :=
        Finset.sum_le_sum fun bits _ => hbits bits
      _ = p := by
        rw [← Finset.sum_mul, actual_center_atoms_sum_one s.template s.depth_pos p x,
          one_mul]
  have hcover := tableProbability_two_event_cover p hp.le hp₁ E D
    (fun ω => E ω ∧ ¬ D ω) (by
      intro ω hω
      by_cases hd : D ω
      · exact Or.inl hd
      · exact Or.inr ⟨hω, hd⟩)
  exact hcover.trans (by linarith)

/-- The complete finite sequence blocker: actual routing, continuum parameters,
Lebesgue integration, an open periodic repair, and arbitrary bounded remainder
errors.  Every assumption is finite candidate or numerical data; no local
probability or measurability assumption remains. -/
theorem finite_sequence_routing_blocker
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p)
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (N : ℕ) (htail : ∀ n ∈ finiteSequenceRoutingTests s, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      n ∈ finiteSequenceRoutingTests s →
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows s.template) →
        q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius s.template p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧
      CompactRobustHits Z H K k N α q := by
  have hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let c := s.template
  let B₁ := routingInnerBuffer c hM s.depth_pos p
  let B₂ := routingOuterBuffer c hM s.depth_pos p
  let w := finiteRoutingWeight (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hw := finiteRoutingWeight_nonneg (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p hp.le hp₁
  have hnorm := finiteRoutingWeight_sum (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p) := by
    have he := expectedUnitDensity_enlargement_le w hw hnorm
      (routedSet c hM s.depth_pos) B₂ (ENNReal.ofReal p)
      (routingOuterBuffer_density_le c hM s.depth_pos s.length_pos p hp)
    apply he.trans
    rw [actual_routedSet_expected_density c hM s.depth_pos p hp.le hp₁
      (measurableSet_actual_routedSet_of_template c hM s.depth_pos s.length_pos)]
    rw [← ENNReal.ofReal_add hp.le hp.le]
    rw [show p + p = 2 * p by ring]
  have hbad : unitDensity (actualStableCenters c)ᶜ ≤ ENNReal.ofReal p := by
    apply (unitDensity_actualStable_compl_le c).trans
    apply ENNReal.ofReal_le_ofReal
    rw [dyadic_integer_gap_rpow]
    exact s.stable_boundary_small
  obtain ⟨ω, houtcome⟩ := exists_sequenceRouting_outcome_density_add_le_of_stable
    Z w hw hnorm (1 / (K : ℝ)) K (finiteSequenceRoutingTests s) k
    (globalRoutingWindows c) B₁ B₂ (fun _ => Metric.isOpen_thickening) p hp.le hB₂
    (actualStableCenters c)ᶜ (measurableSet_actualStableCenters c).compl hbad (by
      intro x hx hxbad
      rw [← tableProbability_eq_finiteOutcomeProbability]
      exact sequence_certificate_stable_probability_le s hK hp hp₁ x
        (by simpa only [Set.mem_compl_iff, not_not] using hxbad))
  have hperiod := onePeriodic_actual_routedSet_of_template c hM s.depth_pos
    s.length_pos ω
  apply periodic_sequence_outcome_repair hK (finiteSequenceRoutingTests s) k
    (globalRoutingWindows c) (routedSet c hM s.depth_pos ω) hperiod
    (routingBufferRadius c p) (routingBufferRadius_pos c p hp)
    N htail α q hα hq herror p hp
  simpa [B₁, B₂, routingInnerBuffer, routingOuterBuffer] using houtcome

/-! The remaining global quantifiers are now a single explicit finite-data
interface.  This is useful both for the completion proof and for auditing:
the interface contains no probability or measure axiom, only a certificate
whose fields are checked by the preceding theorem. -/

structure FiniteSequenceBlockerSpec (Z : LogScale) : Prop where
  data : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (α q δ : ℝ),
    0 < α → 0 ≤ q → 0 < δ → δ < 1 →
    ∃ p : ℝ, 0 < p ∧ 6 * p < δ ∧
      ∃ s : FiniteSequenceRoutingCertificate Z K k p,
        ∃ hK : 2 ≤ K, ∀ n ∈ finiteSequenceRoutingTests s, N ≤ n ∧
          (∀ r : PowerParams (1 / (K : ℝ)) K,
            n ∈ finiteSequenceRoutingTests s →
            r ∈ sequenceWindowActivations Z n k (globalRoutingWindows s.template) →
              q * (input Z n) ^ (r.1.1 + α) <
                routingBufferRadius s.template p)

theorem compactRobustSpec_of_finiteSequenceBlockerSpec
    {Z : LogScale} (hB : FiniteSequenceBlockerSpec Z) :
    CompactRobustSpec Z := by
  intro K hK k N α q hα hq δ hδ hδ₁
  obtain ⟨p, hp, hpδ, s, hsK, hdata⟩ :=
    hB.data K hK k N α q δ hα hq hδ hδ₁
  have htail : ∀ n ∈ finiteSequenceRoutingTests s, N ≤ n := by
    intro n hn
    exact (hdata n hn).1
  have herror : ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      n ∈ finiteSequenceRoutingTests s →
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows s.template) →
        q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius s.template p := by
    intro r n hn hr
    exact (hdata n hn).2 r hn hr
  have hp₁ : p ≤ 1 := by
    nlinarith [hpδ, hδ₁]
  obtain ⟨H, hHo, hHp, hHμ, hHhit⟩ :=
    finite_sequence_routing_blocker s hsK hp hp₁ N htail α q hα hq herror
  exact ⟨H, hHo, hHp,
    hHμ.trans ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hpδ])).2 hpδ), hHhit⟩

/-!  The finite certificate is the only remaining interface between the
abstract late-window property and the actual-sequence blocker.  The provider
below makes that interface explicit while allowing the annulus and routing
schedule to be selected by `WindowFilling`.  In particular, the provider is
not an existence axiom for the blocker: it must construct all finite lists,
their numerical guards, and the tail error bound. -/

structure WindowFillingFiniteSequenceProvider (Z : LogScale) : Prop where
  build : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (p α q : ℝ),
    0 < p → 0 < α → 0 ≤ q →
    ∀ (U : ℕ) (R D : ℝ),
      FillsAnnulus Z (U : ℝ) R D →
      ∀ s : RoutingSchedule K k N p, s.template.origin = U →
      ∃ c : FiniteSequenceRoutingCertificate Z K k p,
        c.branching = s.branching ∧
        c.depth = s.depth ∧
        HEq c.template s.template ∧
        (∀ n ∈ finiteSequenceRoutingTests c, N ≤ n) ∧
        (∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
          n ∈ finiteSequenceRoutingTests c →
          r ∈ sequenceWindowActivations Z n k
            (globalRoutingWindows c.template) →
          q * (input Z n) ^ (r.1.1 + α) <
            routingBufferRadius c.template p)

/-- A `WindowFillingFiniteSequenceProvider` closes the global finite-data
quantifier.  The choice `p = δ/12` is deliberately explicit, so the strict
budget `6*p < δ` is discharged in the kernel.  All geometric work is confined
to the provider; this theorem only synchronizes its annulus with the schedule
selected by `WindowFilling` and assembles the already-proved blocker lemma. -/
theorem finiteSequenceBlockerSpec_of_windowFilling_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingFiniteSequenceProvider Z) :
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
  obtain ⟨U, D, j, sched, hsched, hlog, hfill, hratio, hk, hupper⟩ :=
    WindowFilling.exists_scheduled_annulus_with_active_guards hW K hK k N p hp
  obtain ⟨c, hbranch, hdepth, htemplate, htail, herror⟩ :=
    hP.build K hK k N p α q hp hα hq (U j) (4 * (K : ℝ)) (D j)
      hfill sched hsched
  refine ⟨p, hp, hpδ, c, hK, ?_⟩
  intro n hn
  exact ⟨htail n hn, fun r => herror r n⟩

end ErdosSimilarityGrowingGaps
