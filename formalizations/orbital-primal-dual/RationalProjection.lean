import Duality
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin
import Mathlib.LinearAlgebra.Basis.VectorSpace

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

/-- A rational-linear functional fixes rational constants and preserves the signs
of any specified finite collection of nonnegative real numbers.  Positivity is
only asserted on the supplied finite set, never globally on the real line. -/
theorem finite_rational_projection (s : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧ ∀ x ∈ s, 0 ≤ x → 0 ≤ f x := by
  classical
  let t : Finset ℝ := insert 1 s
  let S : Submodule ℚ ℝ := Submodule.span ℚ (t : Set ℝ)
  let b := Module.finBasis ℚ S
  let K := Fin (Module.finrank ℚ S)
  let X := {x : ℝ // x ∈ t.filter (fun x => 0 < x)}
  letI : Fintype X := (t.filter (fun x => 0 < x)).fintypeCoeSort
  let sx : X → S := fun x => ⟨x.1, Submodule.subset_span (Finset.mem_filter.mp x.2).1⟩
  let L : X → (K → ℝ) → ℝ := fun x w =>
    ∑ i, ((b.repr (sx x) i : ℚ) : ℝ) * w i
  let U : Set (K → ℝ) := {w | ∀ x : X, 0 < L x w}
  have hU : IsOpen U := by
    have hh : IsOpen (⋂ x : X, {w | 0 < L x w}) :=
      isOpen_iInter_of_finite fun x => isOpen_lt continuous_const (by dsimp [L]; fun_prop)
    convert hh using 1
    ext w
    simp [U]
  let v : K → ℝ := fun i => (b i).1
  have hv : v ∈ U := by
    intro x
    have he : L x v = x.1 := by
      have hh := congrArg (fun z : S => (z : ℝ)) (b.sum_repr (sx x))
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] using hh
    rw [he]
    exact (Finset.mem_filter.mp x.2).2
  have hd : DenseRange (fun r : K → ℚ => fun i => (r i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨r, hr⟩ := hd.exists_mem_open hU ⟨v, hv⟩
  let fs : S →ₗ[ℚ] ℚ := b.constr ℚ r
  obtain ⟨g, hg⟩ := fs.exists_extend
  have hgx (x : X) : 0 < g x.1 := by
    have he : (g x.1 : ℝ) = L x (fun i => (r i : ℝ)) := by
      have hh := congrArg (fun f : S →ₗ[ℚ] ℚ => f (sx x)) hg
      change g x.1 = fs (sx x) at hh
      rw [hh]
      simp [fs, Module.Basis.constr_apply_fintype, L]
    exact_mod_cast (he.symm ▸ hr x)
  have h1 : 0 < g 1 := by
    exact hgx ⟨1, by simp [t]⟩
  let f : ℝ →ₗ[ℚ] ℚ := (g 1)⁻¹ • g
  refine ⟨f, ?_, ?_⟩
  · simp [f, h1.ne']
  · intro x hx hnonneg
    by_cases hz : x = 0
    · simp [hz]
    · have hxpos : 0 < x := lt_of_le_of_ne hnonneg (Ne.symm hz)
      have hh := hgx ⟨x, by simp [t, hx, hxpos]⟩
      change 0 ≤ (g 1)⁻¹ * g x
      positivity

/-- Evaluation on a rational multiple commutes with the rational projection. -/
theorem rational_projection_mul (f : ℝ →ₗ[ℚ] ℚ) (c : ℚ) (x : ℝ) :
    f ((c : ℝ) * x) = c * f x := by
  simpa only [Rat.smul_def, Rat.cast_id] using f.map_smul c x

end
end OrbitalMarginals
