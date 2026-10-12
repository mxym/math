import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Basic.Real.Basic

/-! Resultant algebra with actual polynomial degrees. Monicity removes the
artificial right-degree padding, including zero polynomials and zero scales. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma monic_resultant_right_degree (f g : ℝ[X]) (hf : f.Monic)
    (N : ℕ) (hN : g.natDegree ≤ N) :
    f.resultant g f.natDegree N = f.resultant g := by
  have h := Polynomial.resultant_add_right_deg f g f.natDegree g.natDegree
    (N-g.natDegree) le_rfl
  rw [Nat.add_sub_of_le hN,Polynomial.coeff_natDegree,hf,one_pow,one_mul] at h
  exact h

/-- Addition of an arbitrary multiple of a monic left factor does not change
its resultant. The right polynomial's degree is allowed to drop. -/
theorem monic_resultant_add_multiple (f g p : ℝ[X]) (hf : f.Monic) :
    f.resultant (g+f*p) = f.resultant g := by
  let N := (g+f*p).natDegree + g.natDegree + p.natDegree + f.natDegree
  have hg : g.natDegree ≤ N := by dsimp [N]; omega
  have hgp : (g+f*p).natDegree ≤ N := by dsimp [N]; omega
  have hp : p.natDegree + f.natDegree ≤ N := by dsimp [N]; omega
  rw [← monic_resultant_right_degree f (g+f*p) hf N hgp,
    Polynomial.resultant_add_mul_right f g p f.natDegree N hp le_rfl,
    monic_resultant_right_degree f g hf N hg]

/-- Multiplicativity in the right factor at actual degrees, including zero factors. -/
theorem monic_resultant_mul_right (f g h : ℝ[X]) (hf : f.Monic) :
    f.resultant (g*h) = f.resultant g * f.resultant h := by
  rw [← monic_resultant_right_degree f (g*h) hf (g.natDegree+h.natDegree)
    Polynomial.natDegree_mul_le]
  exact Polynomial.resultant_mul_right f g h f.natDegree le_rfl

lemma monic_resultant_mul_left (f g h : ℝ[X]) (hf : f.Monic) (hg : g.Monic) :
    (f*g).resultant h = f.resultant h * g.resultant h := by
  rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero]
  exact Polynomial.resultant_mul_left f g h h.natDegree le_rfl

/-- Scaling formula valid even when c=0 drops the right polynomial's degree. -/
theorem monic_resultant_scale (f g : ℝ[X]) (hf : f.Monic) (c : ℝ) :
    f.resultant (C c*g) = c^f.natDegree * f.resultant g := by
  rw [monic_resultant_mul_right f (C c) g hf]
  simp only [Polynomial.natDegree_C,Polynomial.resultant_C_zero_right]

/-- Exact gluing resultant identity for arbitrary monic denominator blocks.
No numerator degree bound, coprimality or nonzero connector premise is used. -/
theorem monic_resultant_glue (u v r s : ℝ[X]) (hu : u.Monic) (hv : v.Monic) :
    (u*v).resultant (r*v+u*s) =
      (-1 : ℝ)^(u.natDegree*v.natDegree) *
        u.resultant r * v.resultant s * (u.resultant v)^2 := by
  rw [monic_resultant_mul_left u v _ hu hv,
    monic_resultant_add_multiple u (r*v) s hu]
  have he : r*v+u*s = u*s+v*r := by ring
  rw [he,monic_resultant_add_multiple v (u*s) r hv,
    monic_resultant_mul_right u r v hu,monic_resultant_mul_right v u s hv,
    Polynomial.resultant_comm v u]
  rw [Nat.mul_comm v.natDegree u.natDegree]
  ring

end HydrologyTree
