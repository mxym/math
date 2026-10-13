import HydrologyTree.StieltjesReindex

/-! Exact matching of two full finite factorizations. Simple reference poles
force a genuine bijection; no numerical root matching or spectral oracle is used. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Equal full monic pole products with a simple reference determine a bijection
of every factor, even when simplicity was not assumed for the competing list. -/
theorem stieltjes_factor_matching {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e0 : I ≃ J) (q : I → ℝ) (b : J → ℝ)
    (hb : Function.Injective b) (hP : stieltjesDenominator q = stieltjesDenominator b) :
    ∃ e : I ≃ J, ∀ u, q u = b (e u) := by
  have hex (i : J) : ∃ u : I, q u = b i := by
    have h := stieltjesDenominator_eval_pole b i
    rw [← hP,eval_stieltjesDenominator,Finset.prod_eq_zero_iff] at h
    obtain ⟨u,_,hu⟩ := h
    exact ⟨u,by linarith⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply hb
    rw [← hf i,← hf j,hij]
  have hsur : Function.Surjective f := by
    have hs := Finite.surjective_of_injective (e0.injective.comp hinj)
    intro u
    obtain ⟨i,hi⟩ := hs (e0 u)
    exact ⟨i,e0.injective hi⟩
  let E : J ≃ I := Equiv.ofBijective f ⟨hinj,hsur⟩
  refine ⟨E.symm,?_⟩
  intro u
  have h := hf (E.symm u)
  change q (E (E.symm u)) = b (E.symm u) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- Factor matching also proves simplicity of the competing enumeration. -/
theorem stieltjes_equal_product_injective {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e0 : I ≃ J) (q : I → ℝ) (b : J → ℝ)
    (hb : Function.Injective b) (hP : stieltjesDenominator q = stieltjesDenominator b) :
    Function.Injective q := by
  obtain ⟨e,he⟩ := stieltjes_factor_matching e0 q b hb hP
  intro i j hij
  apply e.injective
  apply hb
  rwa [← he i,← he j]

end HydrologyTree
