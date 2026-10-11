import ErdosSimilarityGrowingGaps.SequenceCounting

namespace ErdosSimilarityGrowingGaps

open Set
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The finite actual-log sample list obtained by truncating the greedy sampler.
The values are natural indices of the original sequence, so no representative
or rounded logarithm is introduced. -/
noncomputable def greedyWindowSamples
    (Z : LogScale) (v δ : ℝ) (B : ℕ) : Fin (B + 1) → ℕ :=
  fun i => greedyIndex Z v δ i.1

@[simp] theorem greedyWindowSamples_apply
    (Z : LogScale) (v δ : ℝ) (B : ℕ) (i : Fin (B + 1)) :
    greedyWindowSamples Z v δ B i = greedyIndex Z v δ i.1 := rfl

theorem exists_greedyWindowSamples_crossing
    (Z : LogScale) (v T δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, T ≤ Z.z (greedyWindowSamples Z v δ B
      ⟨B, Nat.lt_succ_self B⟩) := by
  obtain ⟨B, hB⟩ := exists_greedyIndex_crossing Z v T δ hδ
  exact ⟨B, hB⟩

/-- Distinct entries of a finite greedy list are distinct actual indices. -/
theorem greedyWindowSamples_injective
    (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) (B : ℕ) :
    Function.Injective (greedyWindowSamples Z v δ B) := by
  intro i j hij
  apply Fin.ext
  apply (greedyIndex_injective Z v δ hδ)
  exact hij

/-- A positive greedy separation gives the required three-unit gap for every
pair of distinct samples in the finite list. -/
theorem greedyWindowSamples_gap
    {B : ℕ} {s₀ : ℝ} (Z : LogScale) (v δ : ℝ)
    (hδ : 0 < δ) (hs₀ : 0 < s₀) (hsep : 3 ≤ s₀ * δ)
    (i j : Fin (B + 1)) (hij : i ≠ j) :
    3 ≤ s₀ * |Z.z (greedyWindowSamples Z v δ B j) -
      Z.z (greedyWindowSamples Z v δ B i)| := by
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hlog := greedyIndex_log_gap_between Z v δ hδ hlt
    have hmono : Z.z (greedyIndex Z v δ i.1) ≤
        Z.z (greedyIndex Z v δ j.1) :=
      Z.strictMono.monotone ((greedyIndex_strictMono Z v δ hδ).monotone
        (Nat.le_of_lt hlt))
    rw [greedyWindowSamples_apply, greedyWindowSamples_apply,
      abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hmul := mul_le_mul_of_nonneg_left
      (show δ ≤ Z.z (greedyIndex Z v δ j.1) -
        Z.z (greedyIndex Z v δ i.1) by linarith) (le_of_lt hs₀)
    linarith
  · have hlog := greedyIndex_log_gap_between Z v δ hδ hgt
    have hmono : Z.z (greedyIndex Z v δ j.1) ≤
        Z.z (greedyIndex Z v δ i.1) :=
      Z.strictMono.monotone ((greedyIndex_strictMono Z v δ hδ).monotone
        (Nat.le_of_lt hgt))
    rw [greedyWindowSamples_apply, greedyWindowSamples_apply,
      abs_of_nonpos (sub_nonpos.mpr hmono)]
    have hmul := mul_le_mul_of_nonneg_left
      (show δ ≤ Z.z (greedyIndex Z v δ i.1) -
        Z.z (greedyIndex Z v δ j.1) by linarith) (le_of_lt hs₀)
    linarith

/-- A direct h-many bound for the actual candidate set of one routing window.
The first hypothesis is the geometric count supplied by
`sequenceActiveLocalCandidates_card_ge_of_greedy_filter`; the second only
transfers it to a common upper scale `s₁`, which is useful when one schedule
serves every parameter in a rectangle. -/
theorem sequenceActiveLocalCandidates_hmany_of_greedy_filter
    {M d B : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (child : Fin (M - 1))
    (k : ℤ) (p : PowerParams s₀ s₁)
    (children : Fin (B + 1) → Fin (M - 1))
    (indices : Fin (B + 1) → ℕ)
    (u ell D δ η : ℝ)
    (hcount : ell / (2 * (p.1.1 * (δ + D))) ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card)
    (hs₀ : 0 < s₀) (hupper : p.1.1 ≤ s₁)
    (hD : 0 ≤ D) (hδ : 0 < δ)
    (hell_nonneg : 0 ≤ ell)
    (hη : η * ell ≤ ell / (2 * (s₁ * (δ + D)))) :
    η * ell ≤ (sequenceActiveLocalCandidates Z c v children indices k p).card := by
  have hden : 0 ≤ δ + D := by linarith
  have hmul : p.1.1 * (δ + D) ≤ s₁ * (δ + D) := by
    exact mul_le_mul_of_nonneg_right hupper hden
  have hposp : 0 < p.1.1 := lt_of_lt_of_le hs₀ p.1.2.1
  have hs₁p : 0 < s₁ := lt_of_lt_of_le hposp hupper
  have hdenp : 0 < 2 * (p.1.1 * (δ + D)) := by
    positivity
  have hden₁ : 0 < 2 * (s₁ * (δ + D)) := by
    positivity
  have hfrac : ell / (2 * (s₁ * (δ + D))) ≤
      ell / (2 * (p.1.1 * (δ + D))) := by
    apply div_le_div_of_nonneg_left hell_nonneg hdenp
    nlinarith [hmul]
  exact hη.trans (hfrac.trans hcount)

/-- The greedy prefix itself can be used in the local-candidate API.  The
conclusion records both the finite cardinality lower bound and the gap needed
by the fixed-parameter independence theorem. -/
theorem sequenceGreedyWindow_hmany_and_gap
    {M d B : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (child : Fin (M - 1))
    (k : ℤ) (p : PowerParams s₀ s₁)
    {U R : ℝ} (a u ell D δ η : ℝ)
    (hfill : FillsAnnulus Z U R D)
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hlo : U / R ≤ a)
    (hwindow : c.edgeStart (RoutingTemplate.selectorRoutingEdge
      ⟨v, child⟩) = u ∧
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) = u + ell)
    (hell : 2 * (p.1.1 * (δ + D)) ≤ ell)
    (hstart : p.1.1 * Z.z (greedyIndex Z a δ 0) - (k : ℝ) ≤ u)
    (hannulus : (u + ell + (k : ℝ)) / p.1.1 + δ + D ≤ R * U)
    (Bcross : ℕ) (hcross : u + ell ≤
      p.1.1 * Z.z (greedyIndex Z a δ Bcross) - (k : ℝ))
    (hupper : p.1.1 ≤ s₁) (hsep : 3 ≤ s₀ * δ)
    (hη : η * ell ≤ ell / (2 * (s₁ * (δ + D)))) :
    η * ell ≤
      (sequenceActiveLocalCandidates Z c v
        (fun _ : Fin (Bcross + 1) => child)
        (greedyWindowSamples Z a δ Bcross) k p).card ∧
      (∀ i j : Fin (Bcross + 1), i ≠ j →
        3 ≤ s₀ * |Z.z (greedyWindowSamples Z a δ Bcross j) -
          Z.z (greedyWindowSamples Z a δ Bcross i)|) := by
  have hcount := sequenceActiveLocalCandidates_card_ge_of_greedy_filter
    Z c v child k p a u ell D δ hfill hs₀ hδ hlo hwindow hell hstart
    hannulus Bcross hcross
  constructor
  · apply sequenceActiveLocalCandidates_hmany_of_greedy_filter
      Z c v child k p _ _ u ell D δ η hcount
    · exact hs₀
    · exact hupper
    · linarith [hfill.2.2.1]
    · exact hδ
    · nlinarith [hell]
    · exact hη
  · intro i j hij
    exact greedyWindowSamples_gap Z a δ hδ hs₀ hsep i j hij

end ErdosSimilarityGrowingGaps
