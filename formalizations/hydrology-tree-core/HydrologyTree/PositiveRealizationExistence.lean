import HydrologyTree.StieltjesChildAssembly
import HydrologyTree.PositiveAssignment

/-! Unconditional existence of a strictly positive conservative realization on
EVERY original finite rooted tree for every full positive Stieltjes response.
The recursive construction uses actual child states and actual matrix recursions;
no realization theorem or local-inverse assertion is assumed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Every normalized positive full Stieltjes pair is realized by the ACTUAL
physical matrix on any prescribed rooted tree of the corresponding size. -/
theorem positive_tree_stieltjes_realization_exists {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    ∃ x : TreeRates n, PositiveRateVector x ∧
      physicalCharacteristic t x = stieltjesDenominator r ∧
      physicalRootCofactor t x = stieltjesNumerator r w := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨b,g,d,hb,hbpos,hg,hF,hP,hleak⟩ :=
      exists_positive_reciprocal_data_unordered r w hr hpos hw hm
    let e := numberedEdgeEquiv t
    let br (c : RootChild t) (i : Fin (childEdgeCount t c+1)) := b (e ⟨c,i⟩)
    let mass (c : RootChild t) := ∑ i : Fin (childEdgeCount t c+1), g (e ⟨c,i⟩)
    have hmass (c : RootChild t) : 0 < mass c :=
      Finset.sum_pos (fun i _ => hg _) Finset.univ_nonempty
    let bw (c : RootChild t) (i : Fin (childEdgeCount t c+1)) := g (e ⟨c,i⟩)/mass c
    have hc (c : RootChild t) : ∃ y : TreeRates (childEdgeCount t c), PositiveRateVector y ∧
        physicalCharacteristic (childTree t c) y = stieltjesDenominator (br c) ∧
        physicalRootCofactor (childTree t c) y = stieltjesNumerator (br c) (bw c) := by
      have hir : Function.Injective (br c) := by
        intro i j hij
        have hh := e.injective (hb.injective hij)
        exact Fin.ext (congrArg (fun v : NumberedChildNodes t => v.2.val) hh)
      have hwr : ∀ i, 0 < bw c i := fun i => div_pos (hg _) (hmass c)
      have hmr : (∑ i, bw c i)=1 := by
        dsimp only [bw]
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt (hmass c))
      exact ih _ (childEdgeCount_lt t c) (childTree t c) (br c) (bw c) hir
        (fun i => hbpos _) hwr hmr
    choose y hy hPy hFy using hc
    obtain ⟨x,hx,hFx,hPx,_⟩ := assemble_positive_stieltjes_children t e b g d hbpos hg hleak
      y hy hPy hFy
    exact ⟨x,hx,hPx.trans hP.symm,hFx.trans hF.symm⟩

/-- Every such response has an actual strictly positive physical realization
with exactly the requested root-resolvent function off its original poles. -/
theorem positive_tree_response_realization_exists {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    ∃ x : TreeRates n, PositiveRateVector x ∧
      (∀ s : ℝ, (∀ i, s+r i ≠ 0) → physicalRootResponse t x s = ∑ i, w i/(s+r i)) ∧
      physicalCharacteristic t x = stieltjesDenominator r ∧
      physicalRootCofactor t x = stieltjesNumerator r w := by
  obtain ⟨x,hx,hP,hF⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
  refine ⟨x,hx,?_,hP,hF⟩
  intro s hs
  rw [physicalRootResponse_eq,hP,hF]
  exact stieltjes_quotient_eq_sum r w s hs

/-- Two different prescribed tree topologies of the same size can realize the
same full positive response. This is exact, not a finite sampled comparison. -/
theorem any_two_trees_share_positive_stieltjes_response {n : ℕ} (t u : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    ∃ (x y : TreeRates n), PositiveRateVector x ∧ PositiveRateVector y ∧
      physicalCharacteristic t x = physicalCharacteristic u y ∧
      physicalRootCofactor t x = physicalRootCofactor u y ∧
      ∀ s : ℝ, physicalRootResponse t x s = physicalRootResponse u y s := by
  obtain ⟨x,hx,hPx,hFx⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
  obtain ⟨y,hy,hPy,hFy⟩ := positive_tree_stieltjes_realization_exists u r w hr hpos hw hm
  refine ⟨x,y,hx,hy,hPx.trans hPy.symm,hFx.trans hFy.symm,?_⟩
  intro s
  rw [physicalRootResponse_eq,physicalRootResponse_eq,hPx,hPy,hFx,hFy]

end HydrologyTree
