import GaussianRegularEmbeddedMoments

/-! Complete almost-everywhere equality classification, retaining the sole
unproved perimeter hypothesis explicitly. The reverse attainment implication
is unconditional and valid in every ambient dimension. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e k : ℕ} [NeZero k]

lemma winningCell_positive_smul (v : Fin k → Space e) (a : ℝ) (ha : 0 < a)
    (i : Fin k) : winningCell (a • v) 0 i = winningCell v 0 i := by
  ext x
  simp only [winningCell,mem_setOf_eq,Pi.smul_apply,Pi.zero_apply,sub_zero,
    real_inner_smul_left,mul_lt_mul_iff_right₀ ha]

lemma FractionalPartition.moment_eq_of_labels_ae
    (F G : FractionalPartition e k)
    (h : ∀ᵐ x ∂gaussian e,∀ i,F.labels i x=G.labels i x) : F.moment = G.moment := by
  funext i
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx i]

lemma FractionalPartition.energy_eq_of_labels_ae
    (F G : FractionalPartition e k)
    (h : ∀ᵐ x ∂gaussian e,∀ i,F.labels i x=G.labels i x) : F.momentEnergy = G.momentEnergy := by
  unfold FractionalPartition.momentEnergy
  rw [F.moment_eq_of_labels_ae G h]

def IsRegularGaussianFan (F : FractionalPartition e (d+2)) : Prop :=
  ∃ u : Fin (d+2) → Space e,∃ hu : Function.Injective u,
    scoreGram u = regularCovariance (d+2) ∧
      ∀ᵐ x ∂gaussian e,∀ i,F.labels i x=(winningPartition u 0 hu).labels i x

theorem regular_fan_attains (F : FractionalPartition e (d+2)) (hfan : IsRegularGaussianFan F) :
    F.momentEnergy = simplexConstant (d+2)^2 := by
  obtain ⟨u,hu,hg,hae⟩ := hfan
  have henergy := regular_embedding_winning_energy u hg
  have he := F.energy_eq_of_labels_ae (winningPartition u 0 hu) hae
  exact he.trans henergy

theorem equality_iff_regular_fan_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d) (F : FractionalPartition e (d+2))
    (hF : ∀ i,F.mass i = uniformMass (d+2) i) :
    F.momentEnergy = simplexConstant (d+2)^2 ↔ IsRegularGaussianFan F := by
  constructor
  · intro he
    obtain ⟨hv,hg,hae⟩ := moment_equality_ae_regular_winning_of_perimeter hper F hF he
    have hc : 0 < simplexConstant (d+2) := simplexConstant_positive
    let u : Fin (d+2) → Space e := (simplexConstant (d+2))⁻¹ • F.moment
    have hscale : simplexConstant (d+2) • u = F.moment := by
      simp [u,smul_smul,mul_inv_cancel₀ hc.ne']
    have hgu : scoreGram u = regularCovariance (d+2) := by
      change scoreGram ((simplexConstant (d+2))⁻¹ • F.moment) = _
      rw [scoreGram_smul,hg,smul_smul,inv_pow,inv_mul_cancel₀ (sq_pos_of_pos hc).ne',one_smul]
    have hu := regular_embedding_injective u hgu
    refine ⟨u,hu,hgu,?_⟩
    filter_upwards [hae] with x hx
    intro i
    rw [hx i]
    have hcell : winningCell F.moment 0 i = winningCell u 0 i := by
      rw [← hscale,winningCell_positive_smul u _ hc]
    simp only [winningPartition,hcell]
  · exact regular_fan_attains F

end GaussianMeasureBridge
