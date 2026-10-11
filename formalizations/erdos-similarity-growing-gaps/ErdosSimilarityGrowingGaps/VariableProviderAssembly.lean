import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker
import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open Filter Topology Asymptotics
open scoped BigOperators

/-! A direct variable-schedule provider.  Unlike the legacy provider, this
interface does not quantify over a preselected `RoutingSchedule`: the
branching, depth, gap, and base length may all depend on the supplied filled
annulus.  Its fields expose the scalar choices, so an implementation cannot
silently fall back to a fixed-rate tree. -/
structure WindowFillingVariableSequenceProvider (Z : LogScale) : Prop where
  build : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (p α q δ Δ : ℝ),
    0 < p → 0 < α → 0 ≤ q → 0 < δ → δ < 1 → 6 * p < δ →
    0 < Δ → 3 ≤ (1 / (K : ℝ)) * Δ →
    ∀ (U : ℕ) (R D : ℝ),
      FillsAnnulus Z (U : ℝ) R D →
      ∃ c : FiniteSequenceRoutingCertificate Z K k p,
        c.template.origin = U ∧
        c.branching = lateBranching K p δ D ∧
        c.depth = lateDepth K p δ D ∧
        c.template.gap = lateStableGapExplicit K p δ D ∧
        c.rate = lateActivationRate K δ D ∧
        (∀ n ∈ finiteSequenceRoutingTests c, N ≤ n) ∧
        (∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
          n ∈ finiteSequenceRoutingTests c →
          r ∈ sequenceWindowActivations Z n k
            (globalRoutingWindows c.template) →
          q * (input Z n) ^ (r.1.1 + α) <
            routingBufferRadius c.template p)

/-! Canonical node inputs use the actual selector-edge starts as their `u`
coordinates.  This removes an easy source of dependent-type mistakes: the
window identity is definitional, while all annulus inequalities remain
explicit obligations for the geometric bridge. -/
noncomputable def variableRateNodeInput_of_canonical
    {Z : LogScale} {K : ℕ} {k : ℤ} {M d : ℕ}
    (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D δ : ℝ)
    (ha : ∀ child,
      U / R ≤ (c.edgeStart
        (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) + (k : ℝ)) /
        (K : ℝ) - D)
    (ha_hi : ∀ child,
      (c.edgeStart
        (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) + (k : ℝ)) /
        (K : ℝ) ≤ R * U)
    (hnum : ∀ child,
      0 ≤ c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) +
        (vertexWindowLength c v : ℝ) + (k : ℝ))
    (huk : ∀ child,
      0 ≤ c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) +
        (k : ℝ))
    (hell : 2 * ((K : ℝ) * (δ + D)) ≤ vertexWindowLength c v)
    (hannulus : ∀ child,
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) +
        (vertexWindowLength c v : ℝ) + (k : ℝ)) /
          (1 / (K : ℝ)) + δ + D ≤ R * U)
    (hsep : 3 ≤ (1 / (K : ℝ)) * δ) :
    VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D δ := by
  refine {
    u := fun child =>
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ)
    ell := vertexWindowLength c v
    ha := ?_
    ha_hi := ?_
    hnum := ?_
    huk := ?_
    ell_eq := rfl
    hwindow := ?_
    hell := hell
    hannulus := ?_
    hsep := hsep
  }
  · intro child
    exact ha child
  · intro child
    exact ha_hi child
  · intro child
    exact hnum child
  · intro child
    exact huk child
  · intro child
    constructor
    · rfl
    · rfl
  · intro child
    exact hannulus child

/-! A geometric wrapper for the canonical constructor.  The assumptions are
the exact late-annulus guards used by the proof (origin/span, coefficient
bound, width bound, and a base-length budget); the resulting `u` and window
identity are then supplied automatically for every selector child. -/
noncomputable def variableRateNodeInput_of_template_guards
    {Z : LogScale} {K : ℕ} {k : ℤ} {M d : ℕ}
    (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D δ : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (horigin : (c.origin : ℝ) = U)
    (hU : 0 ≤ U)
    (hR : 4 * (K : ℝ) ≤ R)
    (hspan : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ U)
    (hk : |(k : ℝ)| ≤ U / 2)
    (hD : 0 ≤ D)
    (hDsmall : D ≤ U / (4 * (K : ℝ)))
    (hδU : δ ≤ U)
    (hbase : 2 * ((K : ℝ) * (δ + D)) ≤ (c.baseLength : ℝ))
    (hsep : 3 ≤ (1 / (K : ℝ)) * δ) :
    VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D δ := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hlen_nat : c.baseLength ≤ vertexWindowLength c v := by
    exact RoutingTemplate.base_le_length M c.gap c.baseLength
      (d - v.1.val) hM
  have hlen : (c.baseLength : ℝ) ≤ vertexWindowLength c v := by
    exact_mod_cast hlen_nat
  have hell : 2 * ((K : ℝ) * (δ + D)) ≤ vertexWindowLength c v :=
    hbase.trans hlen
  have hklo : -(U / 2) ≤ (k : ℝ) := (abs_le.mp hk).1.trans_eq (by ring)
  have hkhi : (k : ℝ) ≤ U / 2 := (abs_le.mp hk).2
  apply variableRateNodeInput_of_canonical c v U R D δ
  · intro child
    let e : RoutingEdge M d :=
      RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
    have hstart_nat : c.origin ≤ c.edgeStart e :=
      c.edgeStart_ge_origin e
    have hstart : U ≤ (c.edgeStart e : ℝ) := by
      have hs : (c.origin : ℝ) ≤ (c.edgeStart e : ℝ) := by
        exact_mod_cast hstart_nat
      linarith
    have hnum : U / 2 ≤ (c.edgeStart e : ℝ) + (k : ℝ) := by
      linarith
    have hlowK : U / (2 * (K : ℝ)) ≤
        ((c.edgeStart e : ℝ) + (k : ℝ)) / (K : ℝ) := by
      calc
        U / (2 * (K : ℝ)) = (U / 2) / (K : ℝ) := by ring
        _ ≤ ((c.edgeStart e : ℝ) + (k : ℝ)) / (K : ℝ) :=
          (div_le_div_iff_of_pos_right hKpos).2 hnum
    have hDlow : U / (4 * (K : ℝ)) ≤
        U / (2 * (K : ℝ)) - D := by
      have hK4 : (0 : ℝ) < 4 * K := by positivity
      apply (le_sub_iff_add_le).2
      have hmul : D ≤ U / (4 * (K : ℝ)) := hDsmall
      have hEq : U / (4 * (K : ℝ)) + U / (4 * (K : ℝ)) =
          U / (2 * (K : ℝ)) := by field_simp; ring
      rw [← hEq]
      exact add_le_add_right hmul _
    have hRinv : U / R ≤ U / (4 * (K : ℝ)) := by
      apply (div_le_div_iff₀ hRpos (by positivity)).2
      nlinarith
    calc
      U / R ≤ U / (4 * (K : ℝ)) := hRinv
      _ ≤ U / (2 * (K : ℝ)) - D := hDlow
      _ ≤ ((c.edgeStart e : ℝ) + (k : ℝ)) / (K : ℝ) - D :=
        sub_le_sub_right hlowK D
  · intro child
    let e : RoutingEdge M d :=
      RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
    have hend_nat : c.edgeStart e + c.edgeLength e ≤
        c.origin + RoutingTemplate.span M c.gap c.baseLength d := by
      have hh := (c.edgeEnd_within_total hM hL e).2
      unfold RoutingTemplate.edgeEnd at hh
      omega
    have hend : (c.edgeStart e : ℝ) + (vertexWindowLength c v : ℝ) ≤ U +
        (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
      have hh : (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) ≤
          (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
        exact_mod_cast hend_nat
      have hlen_eq : (c.edgeLength e : ℝ) = vertexWindowLength c v := rfl
      have hh' : (c.edgeStart e : ℝ) + (vertexWindowLength c v : ℝ) ≤
          (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
        rw [← hlen_eq]
        exact hh
      simpa [horigin] using hh'
    have hupper : (c.edgeStart e : ℝ) + (k : ℝ) ≤ (5 / 2 : ℝ) * U := by
      have hlen_eq : (c.edgeLength e : ℝ) = vertexWindowLength c v := rfl
      have hstartupper : (c.edgeStart e : ℝ) ≤ U +
          (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
        have hpos : 0 < c.edgeLength e := by
          exact RoutingTemplate.length_positive M c.gap c.baseLength
            (d - e.1.1.val) hM hL
        linarith [hend]
      linarith [hspan, hkhi]
    have hKle : (0 : ℝ) < K := hKpos
    apply (div_le_iff₀ hKpos).2
    have hRU : (0 : ℝ) ≤ U := hU
    have hRbound : (5 / 2 : ℝ) * U ≤ R * U := by
      apply mul_le_mul_of_nonneg_right _ hU
      nlinarith [hR, hKreal]
    have hRUK : R * U ≤ R * U * (K : ℝ) := by
      have hRU' : 0 ≤ R * U := mul_nonneg hRpos.le hU
      nlinarith [hKreal]
    exact hupper.trans (hRbound.trans hRUK)
  · intro child
    let e : RoutingEdge M d :=
      RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
    have hs : U ≤ (c.edgeStart e : ℝ) := by
      have hsn := c.edgeStart_ge_origin e
      have hs' : (c.origin : ℝ) ≤ (c.edgeStart e : ℝ) := by exact_mod_cast hsn
      linarith
    have he : 0 ≤ vertexWindowLength c v := by
      have := RoutingTemplate.length_positive M c.gap c.baseLength
        (d - e.1.1.val) hM hL
      positivity
    linarith [hklo]
  · intro child
    let e : RoutingEdge M d :=
      RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
    have hs : U ≤ (c.edgeStart e : ℝ) := by
      have hsn := c.edgeStart_ge_origin e
      have hs' : (c.origin : ℝ) ≤ (c.edgeStart e : ℝ) := by exact_mod_cast hsn
      linarith
    linarith [hklo]
  · exact hell
  · intro child
    let e : RoutingEdge M d :=
      RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
    have hend_nat : c.edgeStart e + c.edgeLength e ≤
        c.origin + RoutingTemplate.span M c.gap c.baseLength d := by
      have hh := (c.edgeEnd_within_total hM hL e).2
      unfold RoutingTemplate.edgeEnd at hh
      omega
    have hend : (c.edgeStart e : ℝ) + (vertexWindowLength c v : ℝ) ≤ U +
        (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
      have hh : (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) ≤
          (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
        exact_mod_cast hend_nat
      have hlen_eq : (c.edgeLength e : ℝ) = vertexWindowLength c v := rfl
      have hh' : (c.edgeStart e : ℝ) + (vertexWindowLength c v : ℝ) ≤
          (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
        rw [← hlen_eq]
        exact hh
      simpa [horigin] using hh'
    have hupper : (c.edgeStart e : ℝ) + vertexWindowLength c v + (k : ℝ) ≤
        (5 / 2 : ℝ) * U := by
      linarith [hend, hspan, hkhi]
    have hDsmall' : δ + D ≤ (5 / 4 : ℝ) * U := by
      have hKinv : U / (4 * (K : ℝ)) ≤ U / 8 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [hKreal]
      nlinarith [hδU, hDsmall, hKinv]
    have hprod :
        ((c.edgeStart e : ℝ) + vertexWindowLength c v + (k : ℝ)) /
            (1 / (K : ℝ)) ≤ (5 / 2 : ℝ) * (K : ℝ) * U := by
      rw [div_eq_mul_inv]
      have hinv : (1 / (K : ℝ))⁻¹ = (K : ℝ) := by field_simp
      rw [hinv]
      calc
        ((c.edgeStart e : ℝ) + vertexWindowLength c v + (k : ℝ)) * (K : ℝ) ≤
            ((5 / 2 : ℝ) * U) * (K : ℝ) :=
          mul_le_mul_of_nonneg_right hupper (by positivity)
        _ = (5 / 2 : ℝ) * (K : ℝ) * U := by ring
    have hRbound :
        (5 / 2 : ℝ) * (K : ℝ) * U + (5 / 4 : ℝ) * U ≤ R * U := by
      have hcoef : (5 / 2 : ℝ) * (K : ℝ) + 5 / 4 ≤ 4 * (K : ℝ) := by
        nlinarith [hKreal]
      have hcoef' := mul_le_mul_of_nonneg_right hcoef hU
      have hR' := mul_le_mul_of_nonneg_right hR hU
      calc
        (5 / 2 : ℝ) * (K : ℝ) * U + (5 / 4 : ℝ) * U =
            ((5 / 2 : ℝ) * (K : ℝ) + 5 / 4) * U := by ring
        _ ≤ (4 * (K : ℝ)) * U := hcoef'
        _ ≤ R * U := hR'
    calc
      ((c.edgeStart e : ℝ) + vertexWindowLength c v + (k : ℝ)) /
          (1 / (K : ℝ)) + δ + D =
          ((c.edgeStart e : ℝ) + vertexWindowLength c v + (k : ℝ)) /
            (1 / (K : ℝ)) + (δ + D) := by ring
      _ ≤ (5 / 2 : ℝ) * (K : ℝ) * U + (δ + D) :=
        add_le_add_left hprod _
      _ ≤ (5 / 2 : ℝ) * (K : ℝ) * U + (5 / 4 : ℝ) * U :=
        calc
          _ = (δ + D) + (5 / 2 : ℝ) * (K : ℝ) * U := by ring
          _ ≤ (5 / 4 : ℝ) * U + (5 / 2 : ℝ) * (K : ℝ) * U :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hDsmall'
                  ((5 / 2 : ℝ) * (K : ℝ) * U))
          _ = _ := by ring
      _ ≤ R * U := hRbound
  · exact hsep

/-! The assembly theorem is fully kernel-checked.  The only pending work is
the construction of the direct provider above; once supplied, the theorem
selects `p = δ/12`, obtains a late annulus from `WindowFilling`, and feeds its
variable certificate to the already proved finite blocker. -/
theorem finiteSequenceBlockerSpec_of_windowFilling_variable_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingVariableSequenceProvider Z) :
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
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  let Δ : ℝ := 3 * (K : ℝ)
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hΔsep : 3 ≤ (1 / (K : ℝ)) * Δ := by
    dsimp [Δ]
    have hK0 : (K : ℝ) ≠ 0 := ne_of_gt hKpos
    rw [one_div]
    field_simp [hK0]
    exact le_rfl
  obtain ⟨U, D, hUN, hlog, hfill, _hratio⟩ :=
    WindowFilling.exists_late_annulus hW (4 * K) (by omega)
      (max (N : ℝ) 1) (K : ℝ) (by positivity) hKpos
  have hD : 0 ≤ D := by
    linarith [hfill.2.2.1]
  have hfill' : FillsAnnulus Z (U : ℝ) (4 * (K : ℝ)) D := by
    simpa using hfill
  obtain ⟨c, horigin, hbranch, hdepth, hgap, hrate, htail, herror⟩ :=
    hP.build K hK k N p α q δ Δ hp hα hq hδ hδ₁ hpδ hΔ hΔsep
      U (4 * (K : ℝ)) D hfill'
  refine ⟨p, hp, hpδ, c, hK, ?_⟩
  intro n hn
  exact ⟨htail n hn, fun r => herror r n⟩

end ErdosSimilarityGrowingGaps
