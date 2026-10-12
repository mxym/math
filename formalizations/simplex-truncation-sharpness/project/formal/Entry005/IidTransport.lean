import Entry005.WitnessAnchorChain
import Mathlib.MeasureTheory.Constructions.Pi

/-! Actual iid coordinate permutations for the witness sum. The probability
transport property is a proved output for every permutation, not a caller premise.
-/

noncomputable section
open MeasureTheory

namespace Entry005

variable {α : Type*} [MeasurableSpace α]

def iidLaw (ν : Measure α) (n : ℕ) : Measure (Fin n → α) := Measure.pi (fun _ => ν)

instance iidLaw_probability (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (iidLaw ν n) := by
  unfold iidLaw
  infer_instance

def iidSplit (n : ℕ) : (Fin (n + 1) → α) ≃ᵐ (α × (Fin n → α)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => α) 0

theorem iid_split_preserving (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (iidSplit n) (iidLaw ν (n + 1)) (ν.prod (iidLaw ν n)) := by
  exact measurePreserving_piFinSuccAbove (fun _ => ν) 0

def iidAnchorTestSplit (d : ℕ) : (Fin (d + 2) → α) ≃ᵐ ((Fin (d + 1) → α) × α) :=
  (iidSplit (d + 1)).trans MeasurableEquiv.prodComm

theorem iid_anchor_test_preserving (ν : Measure α) [IsProbabilityMeasure ν] (d : ℕ) :
    MeasurePreserving (iidAnchorTestSplit d) (iidLaw ν (d + 2))
      ((iidLaw ν (d + 1)).prod ν) := by
  exact Measure.measurePreserving_swap.comp (iid_split_preserving ν (d + 1))

def iidBasePairSplit (d : ℕ) : (Fin (d + 2) → α) ≃ᵐ ((Fin d → α) × (α × α)) :=
  (iidAnchorTestSplit d).trans
    ((MeasurableEquiv.prodCongr (iidSplit d) (MeasurableEquiv.refl α)).trans
      (MeasurableEquiv.prodAssoc.trans
        (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc)))

theorem iid_base_pair_preserving (ν : Measure α) [IsProbabilityMeasure ν] (d : ℕ) :
    MeasurePreserving (iidBasePairSplit d) (iidLaw ν (d + 2))
      ((iidLaw ν d).prod (ν.prod ν)) := by
  have h₁ := (iid_split_preserving ν d).prod (MeasurePreserving.id ν)
  have h₂ := measurePreserving_prodAssoc ν (iidLaw ν d) ν
  have h₃ := Measure.measurePreserving_swap (μ := ν) (ν := (iidLaw ν d).prod ν)
  have h₄ := measurePreserving_prodAssoc (iidLaw ν d) ν ν
  exact h₄.comp (h₃.comp (h₂.comp (h₁.comp (iid_anchor_test_preserving ν d))))

def iidWitnessTransport (d : ℕ) (p : Equiv.Perm (Fin (d + 2))) :
    ((Fin (d + 1) → α) × α) ≃ᵐ ((Fin d → α) × (α × α)) :=
  (iidAnchorTestSplit d).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => α) p).trans (iidBasePairSplit d))

theorem iid_witness_transport_preserving (ν : Measure α) [IsProbabilityMeasure ν]
    (d : ℕ) (p : Equiv.Perm (Fin (d + 2))) :
    MeasurePreserving (iidWitnessTransport d p) ((iidLaw ν (d + 1)).prod ν)
      ((iidLaw ν d).prod (ν.prod ν)) := by
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => α) p)
      (iidLaw ν (d + 2)) (iidLaw ν (d + 2)) :=
    measurePreserving_piCongrLeft (fun _ => ν) p
  exact (iid_base_pair_preserving ν d).comp
    (hp.comp (iid_anchor_test_preserving ν d).symm)

theorem iid_determinant_witness_anchor {d : ℕ} {ι : Type*} [Fintype ι]
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hF : Integrable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) =>
      liftedDeterminant z.1 z.2) ((iidLaw ν d).prod ν))
    (p : ι → Equiv.Perm (Fin (d + 2))) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hbound : ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1),
      |liftedDeterminant (fun i => w i.succ) (w 0)| ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun i => w i.succ) (w 0)| ^ 2 ∂iidLaw ν (d + 1)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support) ∧
      v ≤ |liftedDeterminant (fun i => w i.succ) (w 0)| ∧
      transportedWitnessSum ν (fun b x => liftedDeterminant b x)
        (fun i => iidWitnessTransport d (p i)) w ≤
        ((Fintype.card ι : ℝ) * determinantLawDefect (iidLaw ν d) ν id id) * C ^ 2 / v ^ 2 := by
  have hmF : Measurable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) =>
      liftedDeterminant z.1 z.2) := measurable_lifted_determinant
    (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)
  have hmV : Measurable (fun w : Fin (d + 1) → Fin d → ℝ =>
      |liftedDeterminant (fun i => w i.succ) (w 0)|) := by
    have hd : Measurable (fun w : Fin (d + 1) → Fin d → ℝ =>
        liftedDeterminant (fun i => w i.succ) (w 0)) := measurable_lifted_determinant
      (fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i.succ))
      (fun i => (measurable_pi_apply i).comp (measurable_pi_apply 0))
    simpa only [Real.norm_eq_abs] using hd.norm
  have hG : ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1),
      ∀ i, w i ∈ ν.support := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin (d + 1) => ν) i).quasiMeasurePreserving.ae
      ν.support_mem_ae
  exact exists_determinant_witness_anchor_ae_good hX hcenter hmF hF
    (fun i => iidWitnessTransport d (p i))
    (fun i => iid_witness_transport_preserving ν d (p i)) hmV hv hC
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmoment hG

end Entry005
