import Entry005.DeterminantWitness

/-! Fubini closes the cancellation identity for the actual outer law of bases.
The outer law need not be atomic. Integrability and centering are primitive
law hypotheses; cancellation and witness budgets are conclusions.
-/

noncomputable section
open MeasureTheory

namespace Entry005

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {σ : Measure β} [IsProbabilityMeasure μ]

def familyDefect (σ : Measure β) (μ : Measure α) (F : β → α → ℝ) : ℝ :=
  (∫ z : β × α, |F z.1 z.2| ∂σ.prod μ) - (∫ b, |∫ x, F b x ∂μ| ∂σ)

theorem integrable_family_defect {F : β → α → ℝ}
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ)) :
    Integrable (fun b => cancellationDefect μ (F b)) σ := by
  have ha : Integrable (fun b => ∫ x, |F b x| ∂μ) σ := by
    simpa only [Real.norm_eq_abs] using hF.norm.integral_prod_left
  have hb : Integrable (fun b => |∫ x, F b x ∂μ|) σ := by
    simpa only [Real.norm_eq_abs] using hF.integral_prod_left.norm
  exact ha.sub hb

theorem family_cancellation_identity [SFinite σ] {F : β → α → ℝ}
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ))
    (hfiber : ∀ b, Integrable (F b) μ) :
    familyDefect σ μ F =
      2 * ∫ b, min (positiveIntegral μ (F b)) (negativeIntegral μ (F b)) ∂σ := by
  have ha : Integrable (fun b => ∫ x, |F b x| ∂μ) σ := by
    simpa only [Real.norm_eq_abs] using hF.norm.integral_prod_left
  have hb : Integrable (fun b => |∫ x, F b x ∂μ|) σ := by
    simpa only [Real.norm_eq_abs] using hF.integral_prod_left.norm
  unfold familyDefect
  have habs : Integrable (fun z : β × α => |F z.1 z.2|) (σ.prod μ) := by
    simpa only [Real.norm_eq_abs] using hF.norm
  rw [integral_prod _ habs, ← integral_sub ha hb]
  change (∫ b, cancellationDefect μ (F b) ∂σ) = _
  simp_rw [integral_cancellation_identity (hfiber _)]
  rw [integral_const_mul]

theorem family_defect_nonneg [SFinite σ] {F : β → α → ℝ}
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ))
    (hfiber : ∀ b, Integrable (F b) μ) :
    0 ≤ familyDefect σ μ F := by
  rw [family_cancellation_identity hF hfiber]
  exact mul_nonneg (by norm_num) (integral_nonneg fun b =>
    le_min (integral_nonneg fun x => le_max_right _ _)
      (integral_nonneg fun x => le_max_right _ _))

theorem integrated_family_witness_le [SFinite σ] {F : β → α → ℝ}
    (hmF : Measurable (fun z : β × α => F z.1 z.2))
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ))
    (hfiber : ∀ b, Integrable (F b) μ) :
    (∫ b, ∫ z : α × α, oppositeWitness (F b z.1) (F b z.2) ∂μ.prod μ ∂σ) ≤
      familyDefect σ μ F := by
  let H : β → ℝ := fun b => ∫ z : α × α, oppositeWitness (F b z.1) (F b z.2) ∂μ.prod μ
  have hmleft : Measurable (fun z : β × (α × α) => F z.1 z.2.1) :=
    hmF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hmright : Measurable (fun z : β × (α × α) => F z.1 z.2.2) :=
    hmF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hmpsi : Measurable (fun z : β × (α × α) =>
      oppositeWitness (F z.1 z.2.1) (F z.1 z.2.2)) := by
    unfold oppositeWitness
    exact ((hmleft.max measurable_const).min (hmright.neg.max measurable_const)).add
      ((hmleft.neg.max measurable_const).min (hmright.max measurable_const))
  have hH : Integrable H σ := (integrable_family_defect hF).mono'
    hmpsi.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => opposite_witness_nonneg _ _)]
      exact integrated_opposite_witness_le (hfiber b))
  have h := integral_mono hH (integrable_family_defect hF)
    (fun b => integrated_opposite_witness_le (hfiber b))
  have ha : Integrable (fun b => ∫ x, |F b x| ∂μ) σ := by
    simpa only [Real.norm_eq_abs] using hF.norm.integral_prod_left
  have hb : Integrable (fun b => |∫ x, F b x ∂μ|) σ := by
    simpa only [Real.norm_eq_abs] using hF.integral_prod_left.norm
  have habs : Integrable (fun z : β × α => |F z.1 z.2|) (σ.prod μ) := by
    simpa only [Real.norm_eq_abs] using hF.norm
  simpa [H, cancellationDefect, integral_sub ha hb, familyDefect,
    integral_prod (fun z : β × α => |F z.1 z.2|) habs] using h

theorem family_witness_integrable {F : β → α → ℝ}
    (hmF : Measurable (fun z : β × α => F z.1 z.2))
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ))
    (hfiber : ∀ b, Integrable (F b) μ) :
    Integrable (fun z : β × (α × α) =>
      oppositeWitness (F z.1 z.2.1) (F z.1 z.2.2)) (σ.prod (μ.prod μ)) := by
  have hmleft : Measurable (fun z : β × (α × α) => F z.1 z.2.1) :=
    hmF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hmright : Measurable (fun z : β × (α × α) => F z.1 z.2.2) :=
    hmF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hmpsi : Measurable (fun z : β × (α × α) =>
      oppositeWitness (F z.1 z.2.1) (F z.1 z.2.2)) := by
    unfold oppositeWitness
    exact ((hmleft.max measurable_const).min (hmright.neg.max measurable_const)).add
      ((hmleft.neg.max measurable_const).min (hmright.max measurable_const))
  apply (integrable_prod_iff hmpsi.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun b => opposite_witness_integrable (hfiber b)), ?_⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (opposite_witness_nonneg _ _)]
  exact (integrable_family_defect hF).mono'
    hmpsi.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => opposite_witness_nonneg _ _)]
      exact integrated_opposite_witness_le (hfiber b))

def determinantLawDefect {d : ℕ} (σ : Measure β) (μ : Measure α)
    (base : β → Fin d → Fin d → ℝ) (X : α → Fin d → ℝ) : ℝ :=
  (∫ z : β × α, |liftedDeterminant (base z.1) (X z.2)| ∂σ.prod μ) -
    (∫ b, |horizontalDeterminant (base b)| ∂σ)

theorem centered_determinant_family_budget {d : ℕ} [SFinite σ]
    {base : β → Fin d → Fin d → ℝ} {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0)
    (hmF : Measurable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)))
    (hF : Integrable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)) (σ.prod μ)) :
    0 ≤ determinantLawDefect σ μ base X ∧
      determinantLawDefect σ μ base X =
        2 * ∫ b, min (positiveIntegral μ (fun x => liftedDeterminant (base b) (X x)))
          (negativeIntegral μ (fun x => liftedDeterminant (base b) (X x))) ∂σ ∧
      (∫ b, ∫ z : α × α, oppositeWitness (liftedDeterminant (base b) (X z.1))
          (liftedDeterminant (base b) (X z.2)) ∂μ.prod μ ∂σ) ≤
        determinantLawDefect σ μ base X := by
  have hid : familyDefect σ μ (fun b x => liftedDeterminant (base b) (X x)) =
      determinantLawDefect σ μ base X := by
    simp only [familyDefect, determinantLawDefect, integral_lifted_determinant _ hX hcenter]
  have hfiber := fun b => lifted_determinant_integrable (base b) hX
  exact ⟨hid ▸ family_defect_nonneg hF hfiber,
    hid ▸ family_cancellation_identity hF hfiber,
    hid ▸ integrated_family_witness_le hmF hF hfiber⟩

end Entry005
