import HydrologyTree.LeakRelocationDifferential
import HydrologyTree.ScalarSlotJacobian

/-! Exact actual rational Jacobian multiplier for single-edge leak relocation.
It is derived from two unit-determinant shears and a proved scalar-slot map. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def edgeRatio (d : G.Dart) (v : G.Dart → ℝ) : ℝ := v d.symm/v d

def slideByShears (d : G.Dart) : GraphRates G → GraphRates G :=
  (scalarVectorShear (-Pi.single d.symm 1)) ∘ (scalarSlotScale (edgeRatio d)) ∘
    (scalarVectorShear (Pi.single d 1))

lemma slideByShears_eq (d : G.Dart) (y : GraphRates G) (ht : y.2 d+y.1 ≠ 0) :
    slideByShears d y=slideLeakRates d y := by
  have ht2 : y.1+y.2 d ≠ 0 := by simpa only [add_comm] using ht
  apply Prod.ext
  · simp [slideByShears,scalarSlotScale,edgeRatio,scalarVectorShear_apply,d.symm_ne]
    ring
  · funext e
    by_cases he : e=d
    · subst e
      simp [slideByShears,scalarSlotScale,edgeRatio,scalarVectorShear_apply,
        slideLeak_forward,d.symm_ne,Ne.symm d.symm_ne]
      ring
    · by_cases hr : e=d.symm
      · subst e
        simp only [slideByShears,Function.comp_apply,scalarVectorShear_apply,scalarSlotScale,
          edgeRatio,Prod.fst,Prod.snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply]
        simp [d.symm_ne,Ne.symm d.symm_ne,slideLeak_reverse]
        field_simp [ht,ht2]
        <;> ring
      · simp [slideByShears,scalarSlotScale,edgeRatio,scalarVectorShear_apply,
          slideLeak_other d e y he hr,he,hr,Ne.symm he,Ne.symm hr,d.symm_ne]

lemma differentiableAt_edgeRatio (d : G.Dart) (v : G.Dart → ℝ) (hv : v d ≠ 0) :
    DifferentiableAt ℝ (edgeRatio d) v := by
  have ha : DifferentiableAt ℝ (fun v : G.Dart → ℝ => v d.symm) v := by fun_prop
  have hb : DifferentiableAt ℝ (fun v : G.Dart → ℝ => v d) v := by fun_prop
  have hi := (hasDerivAt_inv hv).differentiableAt.comp v hb
  convert! ha.mul hi using 1 <;> simp [edgeRatio,div_eq_mul_inv,Function.comp_def]

/-- Exact single-edge determinant on the positive physical domain. Both poles
and parameter singularities are tracked through their actual denominators. -/
theorem slideLeakJacobian_formula (d : G.Dart) (y : GraphRates G) (hy : PositiveGraphRates y) :
    endJacobian (slideLeakRates d) y=y.2 d.symm/(y.2 d+y.1) := by
  have ht := ne_of_gt (add_pos (hy.2 d) hy.1)
  have he : slideLeakRates d =ᶠ[𝓝 y] slideByShears d := by
    filter_upwards [positiveGraphRates_eventually y hy] with z hz
    exact (slideByShears_eq d z (ne_of_gt (add_pos (hz.2 d) hz.1))).symm
  let S := scalarVectorShear (Pi.single d 1 : G.Dart → ℝ)
  let T := scalarVectorShear (-Pi.single d.symm 1 : G.Dart → ℝ)
  have hs : (S y).2 d ≠ 0 := by simpa [S,scalarVectorShear_apply,add_comm] using ht
  have hr := differentiableAt_edgeRatio d (S y).2 hs
  have hf := (hasFDerivAt_scalarSlotScale (edgeRatio d) (S y) hr).differentiableAt
  have heJ : endJacobian (slideLeakRates d) y=endJacobian (slideByShears d) y := by
    rw [endJacobian,endJacobian,he.fderiv_eq]
  rw [heJ]
  change endJacobian ((T ∘ scalarSlotScale (edgeRatio d)) ∘ S) y=_
  rw [endJacobian_comp (T.differentiableAt.comp _ hf) S.differentiableAt,
    endJacobian_comp T.differentiableAt hf,scalarVectorShear_jacobian,
    scalarSlotScale_jacobian _ _ hr,scalarVectorShear_jacobian,one_mul,mul_one]
  simp [edgeRatio,S,scalarVectorShear_apply,d.symm_ne,add_comm]

/-- The exact multiplier is the ratio of the actual new and old leak rates. -/
theorem slideLeakJacobian_leak_weight (d : G.Dart) (y : GraphRates G) (hy : PositiveGraphRates y) :
    y.1*endJacobian (slideLeakRates d) y=(slideLeakRates d y).1 := by
  rw [slideLeakJacobian_formula d y hy,slideLeak_leak]
  ring

/-- The product telescopes along a finite walk: actual leak-weighted Jacobians
are transported with no unspecified normalization constant or sign. -/
theorem leakWalkJacobian_leak_weight {u v : V} (p : G.Walk u v)
    (y : GraphRates G) (hy : PositiveGraphRates y) :
    y.1*endJacobian (leakWalkRates p) y=(leakWalkRates p y).1 := by
  induction p generalizing y with
  | nil => simp [leakWalkRates,endJacobian]
  | cons h p ih =>
    let d : G.Dart := ⟨(_, _),h⟩
    have hd := differentiableAt_slideLeakRates d y (ne_of_gt (add_pos (hy.2 d) hy.1))
    have hp := (leakWalkRates_differentiable_regular p _ (slideLeakRates_positive d y hy)).1
    rw [leakWalkRates,endJacobian_comp hp hd]
    calc
      _ = (y.1*endJacobian (slideLeakRates d) y)*endJacobian (leakWalkRates p) (slideLeakRates d y) := by ring
      _ = _ := by rw [slideLeakJacobian_leak_weight d y hy]; exact ih _ (slideLeakRates_positive d y hy)

end HydrologyTree
