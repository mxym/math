import HydrologyTree.RootModalData
import HydrologyTree.StieltjesNumerator

/-! Construction of modal coordinates from the ORIGINAL positive physical matrix.
The diagonalization, inverse maps, input vector, root output and both actual
coefficient polynomials are proved. No modal-representation premise remains. -/
open Matrix Polynomial Unitary
noncomputable section
namespace HydrologyTree

theorem physical_root_modal_representation {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    ∃ M : RootModalData (compartmentMatrix t x),
      (∀ i, 0 < M.rates i) ∧
      physicalCharacteristic t x = stieltjesDenominator M.rates ∧
      physicalRootCofactor t x = stieltjesNumerator M.rates (fun i => (M.amplitudes i)^2) := by
  let A := compartmentMatrix t x
  let B := symmetricNegativeGenerator t x
  have hB : B.PosDef := symmetricNegativeGenerator_posDef t x hell ha hf
  let U := hB.isHermitian.eigenvectorUnitary
  let r := hB.isHermitian.eigenvalues
  let D := sqrtWeightDiagonal t x
  let E := invSqrtWeightDiagonal t x
  let S := D*(U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
  let T := star (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)*E
  have hDE : D*E=1 := sqrtWeightDiagonal_mul_inv t x ha hf
  have hED : E*D=1 := invSqrtWeightDiagonal_mul_sqrt t x ha hf
  have hUU : (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)*star (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)=1 := U.property.2
  have hUT : star (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)*(U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)=1 := U.property.1
  have hST : S*T=1 := by
    change (D*(U : Matrix _ _ ℝ))*(star (U : Matrix _ _ ℝ)*E)=1
    calc
      _ = D*((U : Matrix _ _ ℝ)*star (U : Matrix _ _ ℝ))*E := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU,Matrix.mul_one,hDE]
  have hTS : T*S=1 := by
    change (star (U : Matrix _ _ ℝ)*E)*(D*(U : Matrix _ _ ℝ))=1
    calc
      _ = star (U : Matrix _ _ ℝ)*(E*D)*(U : Matrix _ _ ℝ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hED,Matrix.mul_one,hUT]
  have hspec : B=(U : Matrix _ _ ℝ)*Matrix.diagonal r*star (U : Matrix _ _ ℝ) := by
    simpa only [conjStarAlgAut_apply,RCLike.ofReal_real_eq_id,Function.id_comp] using
      hB.isHermitian.spectral_theorem
  have hEA : E*A*D= -B := by
    exact neg_eq_iff_eq_neg.mp (physical_negative_similarity t x ha hf).symm
  have hBU : (-B)*(U : Matrix _ _ ℝ)=(U : Matrix _ _ ℝ)*Matrix.diagonal (fun i => -r i) := by
    rw [hspec,Matrix.neg_mul]
    simp only [Matrix.mul_assoc,hUT,Matrix.mul_one]
    ext i j
    simp [Matrix.mul_diagonal]
  have hAS : A*S=S*Matrix.diagonal (fun i => -r i) := by
    change A*(D*(U : Matrix _ _ ℝ))=(D*(U : Matrix _ _ ℝ))*Matrix.diagonal (fun i => -r i)
    calc
      _ = D*((E*A*D)*(U : Matrix _ _ ℝ)) := by simp only [← Matrix.mul_assoc,hDE,Matrix.one_mul]
      _ = D*((-B)*(U : Matrix _ _ ℝ)) := by rw [hEA]
      _ = _ := by rw [hBU,Matrix.mul_assoc]
  have hEinput : E *ᵥ (Pi.single 0 1 : Fin (n+1) → ℝ)=Pi.single 0 1 := by
    ext i
    by_cases hi : i=0
    · subst i
      simp [E,invSqrtWeightDiagonal,Matrix.mulVec,dotProduct,Matrix.diagonal_apply]
    · simp [E,invSqrtWeightDiagonal,Matrix.mulVec,dotProduct,Matrix.diagonal_apply,hi]
  have hinput : T *ᵥ (Pi.single 0 1 : Fin (n+1) → ℝ)=(fun i => U 0 i) := by
    change (star (U : Matrix _ _ ℝ)*E)*ᵥ Pi.single 0 1= _
    rw [← Matrix.mulVec_mulVec,hEinput]
    ext i
    simp [Matrix.mulVec_single_one,Matrix.star_apply,Matrix.conjTranspose_apply,star_trivial]
  have hout (y : Fin (n+1) → ℝ) : (S*ᵥy) 0=∑ i, U 0 i*y i := by
    simp [S,D,sqrtWeightDiagonal,Matrix.diagonal_mul,Matrix.mulVec,dotProduct]
  let M : RootModalData A := ⟨r,(fun i => U 0 i),S,T,hST,hTS,hAS,hinput,hout⟩
  have hP : physicalCharacteristic t x=stieltjesDenominator r :=
    (physical_charpoly_symmetric t x ha hf).trans (charpoly_neg_posDef B hB)
  refine ⟨M,hB.eigenvalues_pos,hP,?_⟩
  change physicalRootCofactor t x=stieltjesNumerator r (fun i => (U 0 i)^2)
  apply polynomial_stieltjes_recovery
  intro s hs
  have hn : (physicalCharacteristic t x).eval s ≠ 0 := by
    rw [hP,eval_stieltjesDenominator]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  have he : B=conjStarAlgAut ℝ _ U (Matrix.diagonal r) := by
    simpa only [conjStarAlgAut_apply] using hspec
  have hi := conjugated_diagonal_resolvent U r s hs
  rw [← he] at hi
  calc
    _ = physicalRootResponse t x s := by rw [physicalRootResponse_eq,hP]
    _ = (Matrix.scalar (Fin (n+1)) s+B)⁻¹ 0 0 := physical_root_resolvent_transport t x ha hf s hn
    _ = ∑ i, (U 0 i)^2 / (s+r i) := by
      rw [Matrix.inv_eq_right_inv hi,conjugation_diagonal_entry]
      apply Finset.sum_congr rfl
      intro i _
      exact (div_eq_mul_inv _ _).symm

end HydrologyTree
