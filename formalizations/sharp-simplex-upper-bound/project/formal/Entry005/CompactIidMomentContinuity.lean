import Entry005.IidTransport
import Entry005.DeterminantWitness
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Instances.Matrix

/-! Weak continuity of the literal finite iid product law and its continuous
first-moment tests on compact sample spaces. -/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators

namespace Entry005

section ActualIid

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability-measure packaging of the actual finite iid `Measure.pi`. -/
def iidProbabilityMeasure (ν : ProbabilityMeasure Ω) (n : ℕ) :
    ProbabilityMeasure (Fin n → Ω) :=
  ⟨iidLaw (ν : Measure Ω) n, inferInstance⟩

@[simp] theorem iidProbabilityMeasure_toMeasure (ν : ProbabilityMeasure Ω) (n : ℕ) :
    (iidProbabilityMeasure ν n : Measure (Fin n → Ω)) = iidLaw (ν : Measure Ω) n := rfl

/-- Adjoining the first coordinate is an actual product-measure pushforward. -/
theorem iidProbabilityMeasure_cons (ν : ProbabilityMeasure Ω) (n : ℕ) :
    iidProbabilityMeasure ν (n + 1) =
      (ν.prod (iidProbabilityMeasure ν n)).map (fun p => Fin.cons p.1 p.2) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (ν : Measure Ω)) 0
  have hs := MeasurePreserving.symm e hp
  have he : (e.symm : (Ω × (Fin n → Ω)) → (Fin (n + 1) → Ω)) =
      (fun p => Fin.cons p.1 p.2) := by
    funext p i
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_zero, Fin.consEquiv_apply]
  apply Subtype.ext
  change Measure.pi (fun _ : Fin (n + 1) => (ν : Measure Ω)) =
    ((ν : Measure Ω).prod (Measure.pi fun _ : Fin n => (ν : Measure Ω))).map
      (fun p => Fin.cons p.1 p.2)
  simpa only [he] using hs.map_eq.symm

theorem iidProbabilityMeasure_map {Ω' : Type*} [MeasurableSpace Ω']
    (ν : ProbabilityMeasure Ω) (n : ℕ) (f : Ω → Ω') (hf : Measurable f) :
    (iidProbabilityMeasure ν n).map (fun w i => f (w i)) =
      iidProbabilityMeasure (ν.map f) n := by
  apply Subtype.ext
  exact Measure.pi_map_pi (fun _ : Fin n => hf.aemeasurable)

/-- Coordinatewise pushforward commutes with the literal iid integral. -/
theorem iid_integral_map {Ω' : Type*} [MeasurableSpace Ω']
    (ν : ProbabilityMeasure Ω) (n : ℕ) (f : Ω → Ω') (hf : Measurable f)
    (g : (Fin n → Ω') → ℝ) (hg : Measurable g) :
    (∫ w, g w ∂iidLaw (ν.map f : Measure Ω') n) =
      ∫ w, g (fun i => f (w i)) ∂iidLaw (ν : Measure Ω) n := by
  have hmap := congrArg (fun μ : ProbabilityMeasure (Fin n → Ω') => (μ : Measure (Fin n → Ω')))
    (iidProbabilityMeasure_map ν n f hf)
  simp only [ProbabilityMeasure.toMeasure_map, iidProbabilityMeasure_toMeasure] at hmap
  change (∫ w, g w ∂iidLaw ((ν : Measure Ω).map f) n) = _
  rw [← hmap]
  exact integral_map (measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i))).aemeasurable
    hg.aestronglyMeasurable

end ActualIid

section WeakContinuity

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω]

omit [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [PseudoMetrizableSpace Ω] in
theorem continuous_fin_cons (n : ℕ) :
    Continuous (fun p : Ω × (Fin n → Ω) => (Fin.cons p.1 p.2 : Fin (n + 1) → Ω)) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using (continuous_fst : Continuous (Prod.fst : Ω × (Fin n → Ω) → Ω))
  | succ j => simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp continuous_snd

/-- The actual finite iid product depends continuously on its one-point law. -/
theorem continuous_iidProbabilityMeasure (n : ℕ) :
    Continuous (fun ν : ProbabilityMeasure Ω => iidProbabilityMeasure ν n) := by
  induction n with
  | zero =>
    apply continuous_of_const
    intro μ ν
    apply Subtype.ext
    change Measure.pi (fun _ : Fin 0 => (μ : Measure Ω)) =
      Measure.pi (fun _ : Fin 0 => (ν : Measure Ω))
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
    have hp : Continuous (fun ν : ProbabilityMeasure Ω => ν.prod (iidProbabilityMeasure ν n)) :=
      ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk ih)
    have hm := (ProbabilityMeasure.continuous_map (continuous_fin_cons (Ω := Ω) n)).comp hp
    exact hm.congr (fun ν => (iidProbabilityMeasure_cons ν n).symm)

theorem tendsto_iidProbabilityMeasure {α : Type*} {l : Filter α}
    {νs : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) (n : ℕ) :
    Tendsto (fun a => iidProbabilityMeasure (νs a) n) l (𝓝 (iidProbabilityMeasure ν n)) :=
  (continuous_iidProbabilityMeasure n).continuousAt.tendsto.comp hν

variable [CompactSpace Ω]

/-- Continuous real tests on compact sample tuples have continuous actual iid integrals. -/
theorem continuous_iid_integral (n : ℕ) (f : C(Fin n → Ω, ℝ)) :
    Continuous (fun ν : ProbabilityMeasure Ω => ∫ w, f w ∂iidLaw (ν : Measure Ω) n) :=
  (ProbabilityMeasure.continuous_integral_continuousMap f).comp
    (continuous_iidProbabilityMeasure n)

theorem tendsto_iid_integral {α : Type*} {l : Filter α}
    {νs : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) (n : ℕ) (f : C(Fin n → Ω, ℝ)) :
    Tendsto (fun a => ∫ w, f w ∂iidLaw (νs a : Measure Ω) n) l
      (𝓝 (∫ w, f w ∂iidLaw (ν : Measure Ω) n)) :=
  (continuous_iid_integral n f).continuousAt.tendsto.comp hν

end WeakContinuity

section DeterminantTests

variable {Ω : Type*} [TopologicalSpace Ω] {d : ℕ}

/-- The first absolute horizontal determinant of the actual coordinate images. -/
def horizontalAbsoluteDeterminantTest (x : C(Ω, Fin d → ℝ)) : C(Fin d → Ω, ℝ) where
  toFun w := |horizontalDeterminant (fun j => x (w j))|
  continuous_toFun := by
    have hm : Continuous (fun w : Fin d → Ω => Matrix.of (fun i j => x (w j) i)) :=
      continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (x.continuous.comp (continuous_apply j))
    exact hm.matrix_det.abs

/-- The affine lift has literal height-first coordinates and samples column zero at `w 0`. -/
def liftedAbsoluteDeterminantTest (x : C(Ω, Fin d → ℝ)) : C(Fin (d + 1) → Ω, ℝ) where
  toFun w := |liftedDeterminant (fun j => x (w j.succ)) (x (w 0))|
  continuous_toFun := by
    have hm : Continuous (fun w : Fin (d + 1) → Ω =>
        witnessMatrix (fun j => x (w j.succ)) (x (w 0))) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact continuous_const
        | succ j => exact continuous_const
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa [witnessMatrix, Function.comp_def] using (continuous_apply i).comp (x.continuous.comp (continuous_apply 0))
        | succ j => simpa [witnessMatrix, Function.comp_def] using (continuous_apply i).comp (x.continuous.comp (continuous_apply j.succ))
    exact hm.matrix_det.abs

variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [PseudoMetrizableSpace Ω] [CompactSpace Ω]

theorem continuous_horizontal_iid_first_moment (x : C(Ω, Fin d → ℝ)) :
    Continuous (fun ν : ProbabilityMeasure Ω =>
      ∫ w, |horizontalDeterminant (fun j => x (w j))| ∂iidLaw (ν : Measure Ω) d) :=
  continuous_iid_integral d (horizontalAbsoluteDeterminantTest x)

theorem continuous_lifted_iid_first_moment (x : C(Ω, Fin d → ℝ)) :
    Continuous (fun ν : ProbabilityMeasure Ω =>
      ∫ w : Fin (d + 1) → Ω, |liftedDeterminant (fun j => x (w j.succ)) (x (w 0))|
        ∂iidLaw (ν : Measure Ω) (d + 1)) :=
  continuous_iid_integral (d + 1) (liftedAbsoluteDeterminantTest x)

omit [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [CompactSpace Ω] in
theorem horizontal_iid_first_moment_map (x : C(Ω, Fin d → ℝ)) (ν : ProbabilityMeasure Ω) :
    (∫ w, |horizontalDeterminant w| ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) d) =
      ∫ w, |horizontalDeterminant (fun j => x (w j))| ∂iidLaw (ν : Measure Ω) d := by
  have hg : Measurable (fun w : Fin d → Fin d → ℝ => |horizontalDeterminant w|) :=
    (horizontalAbsoluteDeterminantTest (ContinuousMap.id (Fin d → ℝ))).continuous.measurable
  exact iid_integral_map ν d x x.continuous.measurable _ hg

omit [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [CompactSpace Ω] in
theorem lifted_iid_first_moment_map (x : C(Ω, Fin d → ℝ)) (ν : ProbabilityMeasure Ω) :
    (∫ w : Fin (d + 1) → Fin d → ℝ, |liftedDeterminant (fun j => w j.succ) (w 0)|
      ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) (d + 1)) =
      ∫ w : Fin (d + 1) → Ω, |liftedDeterminant (fun j => x (w j.succ)) (x (w 0))|
        ∂iidLaw (ν : Measure Ω) (d + 1) := by
  have hg : Measurable (fun w : Fin (d + 1) → Fin d → ℝ =>
      |liftedDeterminant (fun j => w j.succ) (w 0)|) :=
    (liftedAbsoluteDeterminantTest (ContinuousMap.id (Fin d → ℝ))).continuous.measurable
  exact iid_integral_map ν (d + 1) x x.continuous.measurable _ hg

/-- Weak continuity of the first absolute determinant under the actual raw pushforward iid law. -/
theorem continuous_horizontal_mapped_iid_first_moment (x : C(Ω, Fin d → ℝ)) :
    Continuous (fun ν : ProbabilityMeasure Ω =>
      ∫ w, |horizontalDeterminant w| ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) d) :=
  (continuous_horizontal_iid_first_moment x).congr
    (fun ν => (horizontal_iid_first_moment_map x ν).symm)

theorem continuous_lifted_mapped_iid_first_moment (x : C(Ω, Fin d → ℝ)) :
    Continuous (fun ν : ProbabilityMeasure Ω =>
      ∫ w : Fin (d + 1) → Fin d → ℝ, |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) (d + 1)) :=
  (continuous_lifted_iid_first_moment x).congr
    (fun ν => (lifted_iid_first_moment_map x ν).symm)

theorem tendsto_horizontal_mapped_iid_first_moment {α : Type*} {l : Filter α}
    {νs : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) (x : C(Ω, Fin d → ℝ)) :
    Tendsto (fun a => ∫ w, |horizontalDeterminant w|
      ∂iidLaw ((νs a).map x : Measure (Fin d → ℝ)) d) l
      (𝓝 (∫ w, |horizontalDeterminant w| ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) d)) :=
  (continuous_horizontal_mapped_iid_first_moment x).continuousAt.tendsto.comp hν

theorem tendsto_lifted_mapped_iid_first_moment {α : Type*} {l : Filter α}
    {νs : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) (x : C(Ω, Fin d → ℝ)) :
    Tendsto (fun a => ∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw ((νs a).map x : Measure (Fin d → ℝ)) (d + 1)) l
      (𝓝 (∫ w : Fin (d + 1) → Fin d → ℝ, |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (ν.map x : Measure (Fin d → ℝ)) (d + 1))) :=
  (continuous_lifted_mapped_iid_first_moment x).continuousAt.tendsto.comp hν

end DeterminantTests
end Entry005
