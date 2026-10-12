import Entry005.FamilyWitness
import Entry005.AnchorSelection

/-! A closed analytic chain: real centered determinant cancellation, transported
finite witness budget, second-moment event probability, and conditional anchors.
The primitive second-moment bound and iid coordinate transports remain explicit
inputs. This is not the full integrated assignment theorem or final stability theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [Fintype ι]
  {μ : Measure α} {σ : Measure β} {ρ : Measure γ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ]

def transportedWitnessSum (μ : Measure α) (F : β → α → ℝ)
    (T : ι → (γ × α) ≃ᵐ (β × (α × α))) (w : γ) : ℝ :=
  ∫ x, ∑ i, oppositeWitness (F (T i (w, x)).1 (T i (w, x)).2.1)
    (F (T i (w, x)).1 (T i (w, x)).2.2) ∂μ

theorem transported_witness_budget {F : β → α → ℝ}
    (hmF : Measurable (fun z : β × α => F z.1 z.2))
    (hF : Integrable (fun z : β × α => F z.1 z.2) (σ.prod μ))
    (hfiber : ∀ b, Integrable (F b) μ)
    (T : ι → (γ × α) ≃ᵐ (β × (α × α)))
    (hT : ∀ i, MeasurePreserving (T i) (ρ.prod μ) (σ.prod (μ.prod μ))) :
    Integrable (transportedWitnessSum μ F T) ρ ∧
      (∀ w, 0 ≤ transportedWitnessSum μ F T w) ∧
      (∫ w, transportedWitnessSum μ F T w ∂ρ) ≤
        (Fintype.card ι : ℝ) * familyDefect σ μ F := by
  let ψ : β × (α × α) → ℝ := fun z => oppositeWitness (F z.1 z.2.1) (F z.1 z.2.2)
  have hψ : Integrable ψ (σ.prod (μ.prod μ)) := family_witness_integrable hmF hF hfiber
  have hi (i : ι) : Integrable (fun z : γ × α => ψ (T i z)) (ρ.prod μ) :=
    (hT i).integrable_comp_of_integrable hψ
  have hsum : Integrable (fun z : γ × α => ∑ i, ψ (T i z)) (ρ.prod μ) :=
    integrable_finsetSum _ fun i _ => hi i
  refine ⟨hsum.integral_prod_left, ?_, ?_⟩
  · intro w
    exact integral_nonneg (fun x => Finset.sum_nonneg fun i _ => opposite_witness_nonneg _ _)
  · change (∫ w, ∫ x, ∑ i, ψ (T i (w, x)) ∂μ ∂ρ) ≤ _
    rw [← integral_prod _ hsum, integral_finsetSum _ (fun i _ => hi i)]
    simp_rw [(hT _).integral_comp' ψ]
    rw [integral_prod _ hψ]
    simpa using mul_le_mul_of_nonneg_left (integrated_family_witness_le hmF hF hfiber)
      (Nat.cast_nonneg (Fintype.card ι))

theorem exists_determinant_witness_anchor {d : ℕ}
    {base : β → Fin d → Fin d → ℝ} {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0)
    (hmF : Measurable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)))
    (hF : Integrable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)) (σ.prod μ))
    (T : ι → (γ × α) ≃ᵐ (β × (α × α)))
    (hT : ∀ i, MeasurePreserving (T i) (ρ.prod μ) (σ.prod (μ.prod μ)))
    {V : γ → ℝ} (hV : Measurable V) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ w ∂ρ, 0 ≤ V w) (hVC : ∀ᵐ w ∂ρ, V w ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ w, V w ^ 2 ∂ρ) :
    ∃ w, v ≤ V w ∧
      transportedWitnessSum μ (fun b x => liftedDeterminant (base b) (X x)) T w ≤
        ((Fintype.card ι : ℝ) * determinantLawDefect σ μ base X) * C ^ 2 / v ^ 2 := by
  have hfiber := fun b => lifted_determinant_integrable (base b) hX
  obtain ⟨hH, hH0, hmean⟩ := transported_witness_budget hmF hF hfiber T hT
  have hid : familyDefect σ μ (fun b x => liftedDeterminant (base b) (X x)) =
      determinantLawDefect σ μ base X := by
    simp only [familyDefect, determinantLawDefect, integral_lifted_determinant _ hX hcenter]
  rw [hid] at hmean
  exact exists_well_conditioned_low_witness hV hv hC hV0 hVC hmoment hH hH0 hmean

theorem exists_determinant_witness_anchor_ae_good {d : ℕ}
    {base : β → Fin d → Fin d → ℝ} {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0)
    (hmF : Measurable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)))
    (hF : Integrable (fun z : β × α => liftedDeterminant (base z.1) (X z.2)) (σ.prod μ))
    (T : ι → (γ × α) ≃ᵐ (β × (α × α)))
    (hT : ∀ i, MeasurePreserving (T i) (ρ.prod μ) (σ.prod (μ.prod μ)))
    {V : γ → ℝ} (hV : Measurable V) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ w ∂ρ, 0 ≤ V w) (hVC : ∀ᵐ w ∂ρ, V w ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ w, V w ^ 2 ∂ρ)
    {G : γ → Prop} (hG : ∀ᵐ w ∂ρ, G w) :
    ∃ w, G w ∧ v ≤ V w ∧
      transportedWitnessSum μ (fun b x => liftedDeterminant (base b) (X x)) T w ≤
        ((Fintype.card ι : ℝ) * determinantLawDefect σ μ base X) * C ^ 2 / v ^ 2 := by
  have hfiber := fun b => lifted_determinant_integrable (base b) hX
  obtain ⟨hH, hH0, hmean⟩ := transported_witness_budget hmF hF hfiber T hT
  have hid : familyDefect σ μ (fun b x => liftedDeterminant (base b) (X x)) =
      determinantLawDefect σ μ base X := by
    simp only [familyDefect, determinantLawDefect, integral_lifted_determinant _ hX hcenter]
  rw [hid] at hmean
  exact exists_well_conditioned_low_witness_ae_good hV hv hC hV0 hVC hmoment hH hH0 hG hmean

end Entry005
