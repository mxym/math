import HydrologyTree.LeakRelocationWalk
import HydrologyTree.EndJacobian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Actual derivatives of the positive leak-location coordinate changes.
Local invertibility is proved by differentiating the genuine rational inverse,
not supplied as a local-diffeomorphism or nonsingular-Jacobian assumption. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma positiveGraphRates_eventually (y : GraphRates G) (hy : PositiveGraphRates y) :
    ∀ᶠ z in 𝓝 y, PositiveGraphRates z := by
  have h1 : ∀ᶠ z : GraphRates G in 𝓝 y, 0<z.1 :=
    continuousAt_const.eventually_lt continuous_fst.continuousAt hy.1
  have h2 (d : G.Dart) : ∀ᶠ z : GraphRates G in 𝓝 y, 0<z.2 d := by
    have hc : Continuous (fun z : GraphRates G => z.2 d) := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (hy.2 d)
  filter_upwards [h1,Filter.eventually_all.mpr h2] with z hz1 hz2
  exact ⟨hz1,hz2⟩

/-- The actual rational map is differentiable wherever its displayed denominator
is nonzero; no positivity premise is needed for this derivative statement. -/
theorem differentiableAt_slideLeakRates (d : G.Dart) (y : GraphRates G)
    (hy : y.2 d+y.1 ≠ 0) : DifferentiableAt ℝ (slideLeakRates d) y := by
  have hl : DifferentiableAt ℝ (fun z : GraphRates G => z.1) y := by fun_prop
  have ha : DifferentiableAt ℝ (fun z : GraphRates G => z.2 d.symm) y := by fun_prop
  have hf : DifferentiableAt ℝ (fun z : GraphRates G => z.2 d) y := by fun_prop
  have hd := hf.add hl
  have hi := (hasDerivAt_inv hy).differentiableAt.comp y hd
  apply DifferentiableAt.prodMk
  · convert! (ha.mul hl).mul hi using 1 <;> simp [div_eq_mul_inv,Function.comp_def]
  · apply differentiableAt_pi.mpr
    intro e
    change DifferentiableAt ℝ (fun z : GraphRates G =>
      if e=d then z.2 d+z.1 else if e=d.symm then z.2 d.symm*z.2 d/(z.2 d+z.1) else z.2 e) y
    by_cases h : e=d
    · simp only [if_pos h]
      exact hd
    · by_cases hr : e=d.symm
      · simp only [if_neg h,if_pos hr]
        convert! (ha.mul hf).mul hi using 1 <;> simp [div_eq_mul_inv,Function.comp_def]
      · simp only [if_neg h,if_neg hr]
        fun_prop

/-- The product of the two actual derivative determinants is exactly one at
every positive vector. The proof differentiates a checked neighborhood identity. -/
theorem slideLeakJacobian_inverse (d : G.Dart) (y : GraphRates G) (hy : PositiveGraphRates y) :
    endJacobian (slideLeakRates d.symm) (slideLeakRates d y)*endJacobian (slideLeakRates d) y=1 := by
  have he : (slideLeakRates d.symm ∘ slideLeakRates d) =ᶠ[𝓝 y] id := by
    filter_upwards [positiveGraphRates_eventually y hy] with z hz
    exact slideLeakRates_reverse d z (ne_of_gt (add_pos (hz.2 d) hz.1)) (ne_of_gt (hz.2 d.symm))
  have hd := differentiableAt_slideLeakRates d y (ne_of_gt (add_pos (hy.2 d) hy.1))
  have hy' := slideLeakRates_positive d y hy
  have hi := differentiableAt_slideLeakRates d.symm (slideLeakRates d y)
    (ne_of_gt (add_pos (hy'.2 d.symm) hy'.1))
  have hf : endJacobian (slideLeakRates d.symm ∘ slideLeakRates d) y=1 := by
    rw [endJacobian,he.fderiv_eq]
    simp
  rwa [endJacobian_comp hi hd] at hf

theorem slideLeakJacobian_ne_zero (d : G.Dart) (y : GraphRates G) (hy : PositiveGraphRates y) :
    endJacobian (slideLeakRates d) y ≠ 0 := by
  intro hz
  have h := slideLeakJacobian_inverse d y hy
  rw [hz,mul_zero] at h
  exact zero_ne_one h

/-- Underlying real map of a walk, before restricting to positive physical rates. -/
def leakWalkRates : {u v : V} → G.Walk u v → GraphRates G → GraphRates G
  | _,_,.nil => id
  | _,_,.cons h p => leakWalkRates p ∘ slideLeakRates ⟨(_, _),h⟩

lemma leakWalkRates_positive {u v : V} (p : G.Walk u v) (y : GraphRates G) (hy : PositiveGraphRates y) :
    PositiveGraphRates (leakWalkRates p y) := by
  induction p generalizing y with
  | nil => exact hy
  | cons h p ih => exact ih _ (slideLeakRates_positive ⟨(_, _),h⟩ y hy)

lemma leakWalkRates_eq_equiv {u v : V} (p : G.Walk u v) (y : GraphRates G) (hy : PositiveGraphRates y) :
    leakWalkRates p y=(leakWalkEquiv p ⟨y,hy⟩).val := by
  induction p generalizing y with
  | nil => rfl
  | cons h p ih => exact ih _ (slideLeakRates_positive ⟨(_, _),h⟩ y hy)

/-- A finite composition of actual edge moves has a differentiable nonzero
Jacobian at every positive graph rate vector. -/
theorem leakWalkRates_differentiable_regular {u v : V} (p : G.Walk u v)
    (y : GraphRates G) (hy : PositiveGraphRates y) :
    DifferentiableAt ℝ (leakWalkRates p) y ∧ endJacobian (leakWalkRates p) y ≠ 0 := by
  induction p generalizing y with
  | nil =>
    refine ⟨differentiableAt_id,?_⟩
    simp [leakWalkRates,endJacobian]
  | cons h p ih =>
    let d : G.Dart := ⟨(_, _),h⟩
    have hs := differentiableAt_slideLeakRates d y (ne_of_gt (add_pos (hy.2 d) hy.1))
    have hp := ih _ (slideLeakRates_positive d y hy)
    refine ⟨hp.1.comp y hs,?_⟩
    rw [leakWalkRates,endJacobian_comp hp.1 hs]
    exact mul_ne_zero hp.2 (slideLeakJacobian_ne_zero d y hy)

def relocateLeakRates (hG : G.IsTree) (u v : V) : GraphRates G → GraphRates G :=
  leakWalkRates (Classical.choice (hG.connected u v))

lemma relocateLeakRates_eq_positive (hG : G.IsTree) (u v : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    relocateLeakRates hG u v y=(relocatePositiveLeak hG u v ⟨y,hy⟩).val :=
  leakWalkRates_eq_equiv _ y hy

theorem relocateLeakRates_differentiable_regular (hG : G.IsTree) (u v : V)
    (y : GraphRates G) (hy : PositiveGraphRates y) :
    DifferentiableAt ℝ (relocateLeakRates hG u v) y ∧ endJacobian (relocateLeakRates hG u v) y ≠ 0 :=
  leakWalkRates_differentiable_regular _ y hy

end HydrologyTree
