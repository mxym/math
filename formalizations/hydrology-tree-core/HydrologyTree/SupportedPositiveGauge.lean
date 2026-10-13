import HydrologyTree.SupportedStieltjesChildren
import HydrologyTree.ArrowDiagonalGauge

/-! Any real tree-supported matrix with a full positive Stieltjes pair is
explicitly diagonally similar to a positive conservative ROOT-leak model.
The competing matrix need not conserve mass, have positive rates or be stable.
The full child induction is discharged, not exposed as a theorem premise. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Complete same-topology real diagonal realization, including a normalized
nonzero state scale and the exact actual matrix identity. -/
theorem supported_positive_diagonal_realization {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1)
    (hP : A.charpoly=stieltjesDenominator r) (hF : diagonalCofactor A 0=stieltjesNumerator r w) :
    ∃ x : PositiveStieltjesFiber t r w, ∃ h : Fin (n+1) → ℝ,
      (∀ v,h v ≠ 0) ∧ h 0=1 ∧ A=diagonalGauge h (compartmentMatrix t x.val) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨b,g,d,hb,hbpos,hg,hFb,hPb,hl⟩ :=
      exists_positive_reciprocal_data_unordered r w hr hpos hw hm
    have hFA := hF.trans hFb
    have hPA := hP.trans hPb
    obtain ⟨a,ha⟩ := supported_child_allocation_exists t A hA b hb.injective hFA
    have hFc := supported_child_stieltjes_cofactors t A hA b g d hb.injective hbpos hg hl hPA a ha
    have hc (c : RootChild t) :
        ∃ y : PositiveStieltjesFiber (childTree t c) (allocatedRates b a c) (allocatedWeights t g a c),
          ∃ h : Fin (childEdgeCount t c+1) → ℝ,
            (∀ i,h i ≠ 0) ∧ h 0=1 ∧
              supportedChildMatrix t A c=diagonalGauge h (compartmentMatrix (childTree t c) y.val) :=
      ih _ (childEdgeCount_lt t c) (childTree t c) (supportedChildMatrix t A c)
        (supportedChild_support t A hA c) (allocatedRates b a c) (allocatedWeights t g a c)
        (allocatedRates_injective t b hb.injective a c) (fun i => hbpos _)
        (allocatedWeights_pos t g hg a c) (allocatedWeights_sum t g hg a c) (ha c) (hFc c)
    choose y h hh hroot hgauge using hc
    obtain ⟨z,hz⟩ := allocatedChildren_assemble t b g d hbpos hg hl a y
    have hzP : physicalCharacteristic t z.val=stieltjesDenominator r := z.property.2.1.trans hPb.symm
    have hzF : physicalRootCofactor t z.val=stieltjesNumerator r w := z.property.2.2.trans hFb.symm
    have hzc (c : RootChild t) : childCharacteristic t z.val c=allocatedDenominator b a c := by
      change physicalCharacteristic _ (childRates t c z.val)=_
      rw [hz]
      exact (y c).property.2.1
    have hcop : ∀ c k : RootChild t,c ≠ k → IsCoprime (childCharacteristic t z.val c) (childCharacteristic t z.val k) := by
      intro c k hck
      rw [hzc c,hzc k]
      exact allocated_child_factors_coprime t b hb.injective a c k hck
    have hd := supported_physical_reference_data t A hA z.val z.property.1 hcop
      (fun c => (ha c).trans (hzc c).symm) (hP.trans hzP.symm)
    let B := compartmentMatrix t z.val
    have hf (c : RootChild t) : B c.val 0 ≠ 0 := by
      change compartmentMatrix t z.val c.val 0 ≠ 0
      rw [root_outward_child]
      exact ne_of_gt (outward_nonroot_pos z.val z.property.1.2 c.val c.property.1)
    have hbeta (c : RootChild t) : A c.val 0 ≠ 0 := by
      have hp : A 0 c.val*A c.val 0 ≠ 0 := by
        rw [(hd.2 c).2,root_inward_child,root_outward_child]
        exact mul_ne_zero (ne_of_gt (z.property.1.1 c.val))
          (ne_of_gt (outward_nonroot_pos z.val z.property.1.2 c.val c.property.1))
      exact right_ne_zero_of_mul hp
    have hchild (c : RootChild t) : supportedChildMatrix t A c=diagonalGauge (h c) (supportedChildMatrix t B c) := by
      rw [supportedChild_physical,hz]
      exact hgauge c
    let H := arrowGaugeWeight (fun c : RootChild t => B c.val 0) (fun c => A c.val 0) h
    have hH : ∀ v,H v ≠ 0 := arrowGaugeWeight_nonzero _ _ _ hf hbeta hh
    let E := numberedRootEquiv t
    let H' : Fin (n+1) → ℝ := fun v => H (E.symm v)
    have hsub : A.submatrix E E=diagonalGauge H (B.submatrix E E) := by
      rw [supportedMatrix_arrow t A hA,supportedMatrix_arrow t B (compartmentMatrix_tree_support t z.val),hd.1]
      exact arrow_diagonal_gauge (B 0 0) (supportedChildMatrix t A) (supportedChildMatrix t B)
        (fun _ => 0) (fun c => A 0 c.val) (fun c => A c.val 0)
        (fun c => B 0 c.val) (fun c => B c.val 0) h hf hbeta hh hroot hchild (fun c => (hd.2 c).2)
    refine ⟨⟨z.val,z.property.1,hzP,hzF⟩,H',fun v => hH _,?_,?_⟩
    · change H (E.symm (E (.inl ())))=1
      rw [Equiv.symm_apply_apply]
      rfl
    · ext i j
      have he := congrArg (fun M : Matrix (Unit ⊕ NumberedChildNodes t) (Unit ⊕ NumberedChildNodes t) ℝ =>
        M (E.symm i) (E.symm j)) hsub
      simpa only [diagonalGauge_apply,Matrix.submatrix_apply,Equiv.apply_symm_apply,H'] using he

end HydrologyTree
