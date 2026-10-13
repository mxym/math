import HydrologyTree.StieltjesReciprocal
import Mathlib.Data.Finset.Sort

/-! Reindexing and sorting the actual Stieltjes data, including the empty
index type. No increasing order is imposed on the physical model's labels. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma stieltjesDenominator_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (r : J → ℝ) :
    stieltjesDenominator (fun i => r (e i)) = stieltjesDenominator r := by
  exact e.prod_comp (fun j => (X+C (r j) : ℝ[X]))

lemma stieltjes_erased_product_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (r : J → ℝ) (i : I) :
    (∏ j ∈ Finset.univ.erase i, (X+C (r (e j)))) =
      ∏ j ∈ Finset.univ.erase (e i), (X+C (r j)) := by
  apply Finset.prod_equiv e
  · intro j
    simp
  · intro j _
    rfl

lemma stieltjesNumerator_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (r w : J → ℝ) :
    stieltjesNumerator (fun i => r (e i)) (fun i => w (e i)) = stieltjesNumerator r w := by
  unfold stieltjesNumerator
  simp_rw [stieltjes_erased_product_reindex e r]
  exact e.sum_comp (fun j => (C (w j) * ∏ k ∈ Finset.univ.erase j, (X+C (r k)) : ℝ[X]))

/-- Every injective finite list of real rates admits a sorting permutation. -/
theorem exists_sorted_rate_permutation {n : ℕ} (r : Fin n → ℝ) (hr : Function.Injective r) :
    ∃ e : Fin n ≃ Fin n, StrictMono (fun i => r (e i)) := by
  classical
  let s : Finset ℝ := Finset.univ.image r
  have hs : s.card=n := by simp [s,Finset.card_image_of_injective,hr]
  let o : Fin n ≃o s := s.orderIsoOfFin hs
  have hx (i : Fin n) : ∃ j : Fin n, r j=(o i).val := by
    have h := (o i).property
    simpa only [s,Finset.mem_image,Finset.mem_univ,true_and] using h
  let p : Fin n → Fin n := fun i => Classical.choose (hx i)
  have hp (i : Fin n) : r (p i)=(o i).val := Classical.choose_spec (hx i)
  have hpi : Function.Injective p := by
    intro i j hij
    apply o.injective
    apply Subtype.ext
    rw [← hp i,← hp j,hij]
  let e : Fin n ≃ Fin n := Equiv.ofBijective p ⟨hpi,Finite.surjective_of_injective hpi⟩
  refine ⟨e,?_⟩
  intro i j hij
  change r (p i) < r (p j)
  rw [hp i,hp j]
  exact o.strictMono hij

/-- Reciprocal data for arbitrary INJECTIVE rates, not only sorted input labels.
The poles of the new response are sorted; both actual input polynomials are
preserved under the sorting permutation. -/
theorem exists_positive_reciprocal_data_unordered {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i)
    (hm : (∑ i, w i)=1) :
    ∃ (b g : Fin n → ℝ) (d : ℝ),
      StrictMono b ∧ (∀ i, 0 < b i) ∧ (∀ i, 0 < g i) ∧
      stieltjesNumerator r w = stieltjesDenominator b ∧
      stieltjesDenominator r = (X+C d)*stieltjesDenominator b-stieltjesNumerator b g ∧
      0 < d-∑ i, g i/b i := by
  obtain ⟨e,he⟩ := exists_sorted_rate_permutation r hr
  have hmass : (∑ i, w (e i))=1 := (e.sum_comp w).trans hm
  obtain ⟨b,g,d,hb,_,hbpos,hg,hF,hP,hleak⟩ := exists_positive_reciprocal_stieltjes_data
    (fun i => r (e i)) (fun i => w (e i)) he (fun i => hpos (e i))
    (fun i => hw (e i)) hmass
  rw [stieltjesNumerator_reindex e r w] at hF
  rw [stieltjesDenominator_reindex e r] at hP
  exact ⟨b,g,d,hb,hbpos,hg,hF,hP,hleak⟩

end HydrologyTree
