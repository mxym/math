import HydrologyTree.SpectralResolvent
import HydrologyTree.Resolvent

/-! The actual positive-rate physical tree has a normalized finite Stieltjes
root resolvent. Every weight and spectral mode comes from the proved diagonal
similarity. No observational/spectral representation is supplied as an axiom. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma similarity_inverse {I : Type*} [Fintype I] [DecidableEq I]
    (D E A : Matrix I I ℝ) (hDE : D*E = 1) (hED : E*D = 1)
    (hA : IsUnit A.det) : (D*A*E)⁻¹ = D*A⁻¹*E := by
  apply Matrix.inv_eq_right_inv
  calc
    (D*A*E)*(D*A⁻¹*E) = D*(A*(E*D)*A⁻¹)*E := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hED, Matrix.mul_one, Matrix.mul_nonsing_inv A hA, Matrix.mul_one, hDE]

lemma scalar_matrix_eq_smul_one {I : Type*} [Fintype I] [DecidableEq I] (s : ℝ) :
    Matrix.scalar I s = s • (1 : Matrix I I ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, h]

/-- The same fixed diagonal change of variables transports the entire resolvent pencil. -/
theorem physical_scalar_similarity {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) (s : ℝ) :
    sqrtWeightDiagonal t x * (Matrix.scalar (Fin (n+1)) s + symmetricNegativeGenerator t x) *
        invSqrtWeightDiagonal t x = Matrix.scalar (Fin (n+1)) s - compartmentMatrix t x := by
  rw [scalar_matrix_eq_smul_one, physical_negative_similarity t x ha hf]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
  have hh : sqrtWeightDiagonal t x *
      (invSqrtWeightDiagonal t x * compartmentMatrix t x * sqrtWeightDiagonal t x) *
        invSqrtWeightDiagonal t x = compartmentMatrix t x := by
    calc
      _ = (sqrtWeightDiagonal t x * invSqrtWeightDiagonal t x) * compartmentMatrix t x *
          (sqrtWeightDiagonal t x * invSqrtWeightDiagonal t x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrtWeightDiagonal_mul_inv t x ha hf]; simp
  rw [hh, sqrtWeightDiagonal_mul_inv t x ha hf]
  rfl

/-- The root entry is unchanged because the constructed root balance weight is 1. -/
theorem physical_root_resolvent_transport {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (s : ℝ) (hs : (physicalCharacteristic t x).eval s ≠ 0) :
    physicalRootResponse t x s =
      (Matrix.scalar (Fin (n+1)) s + symmetricNegativeGenerator t x)⁻¹ 0 0 := by
  have hA : IsUnit (Matrix.scalar (Fin (n+1)) s + symmetricNegativeGenerator t x).det := by
    rw [← sub_neg_eq_add, ← Matrix.eval_charpoly, ← physical_charpoly_symmetric t x ha hf,
      isUnit_iff_ne_zero]
    exact hs
  unfold physicalRootResponse
  rw [← physical_scalar_similarity t x ha hf s,
    similarity_inverse _ _ _ (sqrtWeightDiagonal_mul_inv t x ha hf)
      (invSqrtWeightDiagonal_mul_sqrt t x ha hf) hA]
  simp [sqrtWeightDiagonal, invSqrtWeightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Actual physical roots and normalized observation weights. Hidden modes may
have zero weights; repeated characteristic roots are NOT silently ruled out. -/
theorem physical_finite_stieltjes {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (hf : ∀ e : Fin n, 0 < x.2 e) :
    ∃ r w : Fin (n+1) → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 ≤ w i) ∧
      (∑ i, w i) = 1 ∧
      physicalCharacteristic t x = ∏ i, (X + C (r i)) ∧
      ∀ s : ℝ, (∀ i, s+r i ≠ 0) →
        physicalRootResponse t x s = ∑ i, w i / (s+r i) := by
  have hB := symmetricNegativeGenerator_posDef t x hell ha hf
  obtain ⟨r,w,hr,hw,hm,hP,hR⟩ := posDef_resolvent_representation _ hB (0 : Fin (n+1))
  have hphys : physicalCharacteristic t x = ∏ i, (X+C (r i)) :=
    (physical_charpoly_symmetric t x ha hf).trans hP
  refine ⟨r,w,hr,hw,hm,hphys,?_⟩
  intro s hs
  have hne : (physicalCharacteristic t x).eval s ≠ 0 := by
    rw [hphys, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using hs i
  rw [physical_root_resolvent_transport t x ha hf s hne]
  exact hR s hs

end HydrologyTree
