import HydrologyTree.PhysicalForcedODE
import HydrologyTree.DischargeFiber

/-! Closed actual-ODE implication of the full real-response classification.
Every real response realization is proved positive before constructing solutions.
All-input equalities below concern arbitrary continuous inputs and actual states. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Every real full-target model has a unique actual zero-initial trajectory
for every continuous input, with the explicitly prescribed time-domain output. -/
theorem real_full_response_forced_ODE {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w)
    (u : ℝ → ℝ) (hu : Continuous u) (a : ℝ) :
    ∃! z : ℝ → Fin (n+1) → ℝ,
      IsPhysicalForcedSolution t x u z ∧ z a=0 ∧
      ∀ s : ℝ, z s 0=∑ i, w i*scalarForcedSolution (r i) u a 0 s := by
  obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  have hpositive := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  obtain ⟨z,hz,hunique⟩ := physical_forced_ODE_existsUnique t x hpositive u hu a 0
  refine ⟨z,⟨hz.1,hz.2,?_⟩,?_⟩
  · exact fun s => physical_forced_root_formula t x hpositive r w hr hP hF u hu a z hz.1 hz.2 s
  · intro y hy
    exact hunique y ⟨hy.1,hy.2.1⟩

/-- Two prescribed topologies with the same full response give identical actual
root state and discharge for EVERY continuous input and every initial time.
No positivity or regularity premise is imposed on the competing rate vectors. -/
theorem same_full_response_all_continuous_inputs {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hx : HasStieltjesRootResponse t x r w) (hy : HasStieltjesRootResponse v y r w)
    (u : ℝ → ℝ) (hu : Continuous u) (a : ℝ)
    (z q : ℝ → Fin (n+1) → ℝ)
    (hz : IsPhysicalForcedSolution t x u z) (hq : IsPhysicalForcedSolution v y u q)
    (hz0 : z a=0) (hq0 : q a=0) :
    ∀ s : ℝ, z s 0=q s 0 ∧ x.1 0*z s 0=y.1 0*q s 0 := by
  obtain ⟨hPx,hFx⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  obtain ⟨hPy,hFy⟩ := (stieltjes_root_response_iff_polynomials v r w hr hpos hw hm y).mp hy
  have hposx := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hPx hFx
  have hposy := real_stieltjes_realization_is_positive v y r w hr hpos hw hm hPy hFy
  have hleakx := full_stieltjes_leak_identified t x r w hr hpos hw hm hPx hFx
  have hleaky := full_stieltjes_leak_identified v y r w hr hpos hw hm hPy hFy
  intro s
  have he : z s 0=q s 0 :=
    (physical_forced_root_formula t x hposx r w hr hPx hFx u hu a z hz hz0 s).trans
      (physical_forced_root_formula v y hposy r w hr hPy hFy u hu a q hq hq0 s).symm
  exact ⟨he,by rw [he,hleakx,hleaky]⟩

end HydrologyTree
