import HydrologyTree.SupportedMatrixRecursion
import HydrologyTree.RealFactorAllocation
import HydrologyTree.PositiveFiberTypes

/-! Exact normalized Stieltjes child data of any tree-supported real matrix.
Conservation and positivity of the competing matrix are not hypotheses. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

theorem supported_child_allocation_exists {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (b : Fin n → ℝ) (hb : Function.Injective b)
    (hF : diagonalCofactor A 0=stieltjesDenominator b) :
    ∃ a : TreePoleAllocation t, ∀ c, matrixChildP t A c=allocatedDenominator b a c := by
  have hsplit : (stieltjesDenominator b).Splits :=
    Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_add_C (b i))
  have hc (c : RootChild t) : ∃ q : Fin (childEdgeCount t c+1) → ℝ,
      matrixChildP t A c=stieltjesDenominator q := by
    have hdvd : matrixChildP t A c ∣ stieltjesDenominator b := by
      rw [← hF,supportedMatrix_cofactor_recursion t A hA]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
    exact monic_split_fin_factorization _ (matrixChildP_monic t A c)
      (hsplit.of_dvd (stieltjesDenominator_monic b).ne_zero hdvd) (matrixChildP_natDegree t A c)
  choose q hq using hc
  let z : NumberedChildNodes t → ℝ := fun v => q v.1 v.2
  have heq : stieltjesDenominator z=stieltjesDenominator b := by
    rw [stieltjesDenominator_sigma]
    calc
      (∏ c : RootChild t, stieltjesDenominator (q c)) = ∏ c, matrixChildP t A c :=
        Finset.prod_congr rfl (fun c _ => (hq c).symm)
      _ = diagonalCofactor A 0 := (supportedMatrix_cofactor_recursion t A hA).symm
      _ = stieltjesDenominator b := hF
  obtain ⟨e,he⟩ := stieltjes_factor_matching (numberedEdgeEquiv t) z b hb heq
  refine ⟨allocationOfEquiv e,?_⟩
  intro c
  rw [hq c,allocatedDenominator_of_equiv]
  congr 1
  funext i
  exact he ⟨c,i⟩

/-- Actual root/child invariant recovery against a proved positive reference. -/
theorem supported_physical_reference_data {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (x : TreeRates n) (hx : PositiveRateVector x)
    (hcop : ∀ c d : RootChild t, c ≠ d → IsCoprime (childCharacteristic t x c) (childCharacteristic t x d))
    (hchild : ∀ c, matrixChildP t A c=childCharacteristic t x c)
    (hparent : A.charpoly=physicalCharacteristic t x) :
    A 0 0=compartmentMatrix t x 0 0 ∧
      ∀ c : RootChild t, matrixChildF t A c=childCofactor t x c ∧
        A 0 c.val*A c.val 0=compartmentMatrix t x 0 c.val*compartmentMatrix t x c.val 0 := by
  have hB := compartmentMatrix_tree_support t x
  have hc : ∀ c d : RootChild t, c ≠ d →
      IsCoprime (matrixChildP t (compartmentMatrix t x) c) (matrixChildP t (compartmentMatrix t x) d) := by
    simpa only [matrixChildP_physical] using hcop
  have he : ∀ c, matrixChildP t (compartmentMatrix t x) c=matrixChildP t A c := by
    intro c
    rw [matrixChildP_physical]
    exact (hchild c).symm
  have hroot := supportedMatrix_root_diagonal_identified t (compartmentMatrix t x) A hB hA hc he hparent.symm
  have hdata := supportedMatrix_child_data_identified t (compartmentMatrix t x) A hB hA hc he hparent.symm (by
    intro c
    rw [root_inward_child,root_outward_child]
    exact mul_ne_zero (ne_of_gt (hx.1 c.val))
      (ne_of_gt (outward_nonroot_pos x hx.2 c.val c.property.1)))
  refine ⟨hroot.symm,?_⟩
  intro c
  exact ⟨(hdata c).1.symm.trans (matrixChildF_physical t x c),(hdata c).2.symm⟩

/-- Every child receives the true normalized positive reciprocal target. -/
theorem supported_child_stieltjes_cofactors {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (b g : Fin n → ℝ) (d : ℝ)
    (hb : Function.Injective b) (hpos : ∀ i,0<b i) (hg : ∀ i,0<g i)
    (hl : 0<d-∑ i,g i/b i)
    (hP : A.charpoly=(X+C d)*stieltjesDenominator b-stieltjesNumerator b g)
    (a : TreePoleAllocation t) (ha : ∀ c,matrixChildP t A c=allocatedDenominator b a c) :
    ∀ c, matrixChildF t A c=stieltjesNumerator (allocatedRates b a c) (allocatedWeights t g a c) := by
  let y := Classical.choice (allocatedChildFibers_nonempty t b g hb hpos hg a)
  obtain ⟨z,hz⟩ := allocatedChildren_assemble t b g d hpos hg hl a y
  have hzc (c : RootChild t) : childCharacteristic t z.val c=allocatedDenominator b a c := by
    change physicalCharacteristic _ (childRates t c z.val)=_
    rw [hz]
    exact (y c).property.2.1
  have hcop : ∀ c k : RootChild t, c ≠ k → IsCoprime (childCharacteristic t z.val c) (childCharacteristic t z.val k) := by
    intro c k hck
    rw [hzc c,hzc k]
    exact allocated_child_factors_coprime t b hb a c k hck
  have he := supported_physical_reference_data t A hA z.val z.property.1 hcop
    (fun c => (ha c).trans (hzc c).symm) (hP.trans z.property.2.1.symm)
  intro c
  rw [(he.2 c).1]
  change physicalRootCofactor _ (childRates t c z.val)=_
  rw [hz]
  exact (y c).property.2.2

end HydrologyTree
