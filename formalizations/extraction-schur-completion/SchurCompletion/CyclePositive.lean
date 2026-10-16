import SchurCompletion.CycleRatio

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem cycleCharacter_inv (t k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (t : ℂ)^positionCycleCount k σ⁻¹ = (t : ℂ)^positionCycleCount k σ := by
  rw [← copyPermutation_trace_cycleCount,← copyPermutationMatrix_star,Matrix.trace_conjTranspose,
    copyPermutation_trace_cycleCount]
  simp only [star_pow,star_natCast]

theorem cycleOperator_eq_direct_sum (D t k : ℕ) :
    cycleOperator D t k = ∑ σ : Equiv.Perm (Fin k),
      (t : ℂ)^positionCycleCount k σ • copyPermutationMatrix D k σ := by
  have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k)))
    (fun σ => (t : ℂ)^positionCycleCount k σ • copyPermutationMatrix D k σ⁻¹)
  exact h.symm.trans (by simp only [Equiv.inv_apply,inv_inv,cycleCharacter_inv])

theorem copyPermutationMatrix_apply (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (w v : Word D k) :
    copyPermutationMatrix D k σ w v = if w ∘ σ = v then 1 else 0 := by
  simp only [copyPermutationMatrix,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  simp [positionWordEquiv,eq_comm]

def pairWord (D t k : ℕ) (x : Word D k) (y : Word t k) : Word (D*t) k :=
  fun j => finProdFinEquiv (x j,y j)

theorem pairWord_position_eq_iff (D t k : ℕ) (σ : Equiv.Perm (Fin k))
    (x v : Word D k) (y z : Word t k) :
    pairWord D t k x y ∘ σ = pairWord D t k v z ↔ x ∘ σ = v ∧ y ∘ σ = z := by
  constructor
  · intro h
    have hxy (j : Fin k) : (x (σ j),y (σ j)) = (v j,z j) :=
      finProdFinEquiv.injective (congrFun h j)
    exact ⟨funext (fun j => congrArg Prod.fst (hxy j)),
      funext (fun j => congrArg Prod.snd (hxy j))⟩
  · rintro ⟨hx,hy⟩
    apply funext
    intro j
    change finProdFinEquiv (x (σ j),y (σ j)) = finProdFinEquiv (v j,z j)
    apply congrArg finProdFinEquiv
    exact Prod.ext (congrFun hx j) (congrFun hy j)

theorem copyPermutation_pairWord (D t k : ℕ) (σ : Equiv.Perm (Fin k))
    (x v : Word D k) (y z : Word t k) :
    copyPermutationMatrix (D*t) k σ (pairWord D t k x y) (pairWord D t k v z) =
      copyPermutationMatrix D k σ x v * copyPermutationMatrix t k σ y z := by
  simp only [copyPermutationMatrix_apply,pairWord_position_eq_iff]
  split_ifs <;> simp_all

/-- Actual finite partial trace of the occupation projector after pairing the
 D-dimensional and t-dimensional letters in each tensor copy. -/
def partialSymmetricTrace (D t k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  ∑ y : Word t k, (symmetricProjector (D*t) k).submatrix
    (fun x => pairWord D t k x y) (fun x => pairWord D t k x y)

theorem partialSymmetricTrace_posSemidef (D t k : ℕ) :
    (partialSymmetricTrace D t k).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro y _
  exact (symmetricProjector_posSemidef (D*t) k).submatrix _

/-- The actual cycle-character matrix is k! times an actual positive partial
 trace. This derives positivity without a representation-theoretic spectrum. -/
theorem partialSymmetricTrace_eq_cycleOperator (D t k : ℕ) :
    partialSymmetricTrace D t k =
      (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • cycleOperator D t k := by
  ext x v
  simp only [partialSymmetricTrace,Matrix.sum_apply,Matrix.submatrix_apply,
    symmetricProjector_eq_copyPermutationAverage,copyPermutationAverage,
    Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,copyPermutation_pairWord]
  rw [← Finset.mul_sum,Finset.sum_comm]
  rw [cycleOperator_eq_direct_sum]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_sum]
  change copyPermutationMatrix D k σ x v * (copyPermutationMatrix t k σ).trace = _
  rw [copyPermutation_trace_cycleCount,mul_comm]

theorem cycleOperator_posSemidef (D t k : ℕ) :
    (cycleOperator D t k).PosSemidef := by
  have hc : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := (partialSymmetricTrace_posSemidef D t k).smul
    (show (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin k)) from Nat.cast_nonneg _)
  rw [partialSymmetricTrace_eq_cycleOperator,RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_natCast,← mul_smul,mul_inv_cancel₀ hc,one_smul] at h
  exact h

end
end ExtractionSchur
