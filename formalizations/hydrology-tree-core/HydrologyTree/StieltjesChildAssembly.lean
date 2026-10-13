import HydrologyTree.StieltjesGrouping
import HydrologyTree.PositiveRateAssembly
import HydrologyTree.PhysicalConstants

/-! Conservative positive reconstruction for any prescribed grouping of the
reciprocal poles. The assembled object is the original rate-indexed tree,
not a substitute matrix or an assumed realization. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma realized_child_connector {k : ℕ} (t : OrderedTree k) (x : TreeRates k)
    (b g : Fin (k+1) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hx : PositiveRateVector x) (hb : ∀ i, 0 < b i)
    (hP : physicalCharacteristic t x = stieltjesDenominator b)
    (hF : physicalRootCofactor t x = stieltjesNumerator b (fun i => g i/c)) :
    c/x.1 0 = ∑ i, g i/b i := by
  have hF0 := physicalRootCofactor_eval_zero_pos t x (fun i => hx.1 i.succ)
  have hconst := physicalCharacteristic_eval_zero_leak t x
  have hscale := congrArg (fun Q : ℝ[X] => Q.eval 0)
    (stieltjesNumerator_normalization b g c hc)
  simp only [Polynomial.eval_mul,Polynomial.eval_C] at hscale
  have hsum := stieltjes_sum_mul_denominator b g 0 (fun i => by simpa using ne_of_gt (hb i))
  simp only [zero_add] at hsum
  rw [← hF] at hscale
  rw [← hP] at hsum
  apply (div_eq_iff (ne_of_gt (hx.1 0))).mpr
  apply mul_right_cancel₀ (ne_of_gt hF0)
  calc
    c*(physicalRootCofactor t x).eval 0 = (stieltjesNumerator b g).eval 0 := hscale
    _ = (∑ i, g i/b i)*(physicalCharacteristic t x).eval 0 := hsum.symm
    _ = ((∑ i, g i/b i)*x.1 0)*(physicalRootCofactor t x).eval 0 := by rw [hconst]; ring

/-- One complete positive root reconstruction from actual positive child
realizations and any bijective pole allocation. This is the induction step;
existence of all child realizations is discharged in the all-tree theorem. -/
theorem assemble_positive_stieltjes_children {n : ℕ} (t : OrderedTree n)
    (e : NumberedChildNodes t ≃ Fin n) (b g : Fin n → ℝ) (d : ℝ)
    (hb : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (y : ChildStates t) (hy : ∀ c, PositiveRateVector (y c))
    (hP : ∀ c, physicalCharacteristic (childTree t c) (y c) =
      stieltjesDenominator (fun i => b (e ⟨c,i⟩)))
    (hF : ∀ c, physicalRootCofactor (childTree t c) (y c) =
      stieltjesNumerator (fun i => b (e ⟨c,i⟩))
        (fun i => g (e ⟨c,i⟩)/(∑ j : Fin (childEdgeCount t c+1), g (e ⟨c,j⟩)))) :
    ∃ x : TreeRates n, PositiveRateVector x ∧
      physicalRootCofactor t x = stieltjesDenominator b ∧
      physicalCharacteristic t x = (X+C d)*stieltjesDenominator b-stieltjesNumerator b g ∧
      (∀ c, childRates t c x = y c) := by
  let mass : RootChild t → ℝ := fun c => ∑ i : Fin (childEdgeCount t c+1), g (e ⟨c,i⟩)
  have hm (c : RootChild t) : 0 < mass c :=
    Finset.sum_pos (fun i _ => hg _) Finset.univ_nonempty
  let f : RootChild t → ℝ := fun c => mass c/(y c).1 0
  have hf (c : RootChild t) : 0 < f c := div_pos (hm c) ((hy c).1 0)
  have hfval (c : RootChild t) : f c=∑ i : Fin (childEdgeCount t c+1),g (e ⟨c,i⟩)/b (e ⟨c,i⟩) :=
    realized_child_connector (childTree t c) (y c) _ _ (mass c) (ne_of_gt (hm c))
      (hy c) (fun i => hb _) (hP c) (hF c)
  have hfsum : (∑ c, f c) = ∑ i : Fin n, g i/b i := by
    simp only [hfval]
    exact (Fintype.sum_sigma (fun v : NumberedChildNodes t => g (e v)/b (e v))).symm.trans
      (e.sum_comp (fun i => g i/b i))
  let l := d-∑ i, g i/b i
  let x := assemblePositiveRates t l f y
  have hx := assemblePositiveRates_positive t l f y hl hf hy
  have hchildren (c : RootChild t) : childRates t c x=y c := assembledRates_child t l f y c
  have hPchild (c : RootChild t) : childCharacteristic t x c =
      stieltjesDenominator (fun i => b (e ⟨c,i⟩)) := by
    change physicalCharacteristic (childTree t c) (childRates t c x) = _
    rw [hchildren,hP]
  have hFchild (c : RootChild t) : childCofactor t x c =
      stieltjesNumerator (fun i => b (e ⟨c,i⟩)) (fun i => g (e ⟨c,i⟩)/mass c) := by
    change physicalRootCofactor (childTree t c) (childRates t c x) = _
    rw [hchildren,hF]
  have hwhole : (∏ c : RootChild t, childCharacteristic t x c) = stieltjesDenominator b := by
    simp only [hPchild]
    exact (stieltjesDenominator_sigma (childEdgeCount t) (fun v => b (e v))).symm.trans
      (stieltjesDenominator_reindex e b)
  have hden : physicalRootCofactor t x=stieltjesDenominator b := by
    rw [physicalRootCofactor_child_product,hwhole]
  have hdiag : (rateChart t x).1 0=d := by
    rw [assembledRates_diagonal,hfsum]
    exact sub_add_cancel _ _
  have hedge (c : RootChild t) : x.1 c.val*outwardByVertex x.2 c.val=mass c := by
    rw [assembledRates_child_leak,assembledRates_connector]
    exact mul_div_cancel₀ _ (ne_of_gt ((hy c).1 0))
  have hnum : (∑ c : RootChild t, C (x.1 c.val*outwardByVertex x.2 c.val)*childCofactor t x c *
      ∏ j ∈ Finset.univ.erase c, childCharacteristic t x j) = stieltjesNumerator b g := by
    simp only [hedge,hFchild,hPchild,stieltjesNumerator_normalization _ _ _ (ne_of_gt (hm _))]
    exact (stieltjesNumerator_sigma (childEdgeCount t) (fun v => b (e v))
      (fun v => g (e v))).symm.trans (stieltjesNumerator_reindex e b g)
  refine ⟨x,hx,hden,?_,hchildren⟩
  rw [physicalCharacteristic_child_recursion,hdiag,hwhole,hnum]

end HydrologyTree
