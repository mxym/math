import MinimaxProfile.Protocol
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.StdBasis

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix

namespace ExtractionCP
noncomputable section
variable {ι ο κ : Type} [Fintype ι] [Fintype ο] [Fintype κ]
  [DecidableEq ι] [DecidableEq ο]

/-- Entrywise physical amplification on every finite auxiliary register. -/
def amplification (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (τ : Type) [Fintype τ] (X : Matrix (ι×τ) (ι×τ) ℂ) :
    Matrix (ο×τ) (ο×τ) ℂ := fun o p => Φ (fun i j => X (i,o.2) (j,p.2)) o.1 p.1

/-- Complete positivity means positivity of all actual finite amplifications. -/
def CompletelyPositive (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ]
    (X : Matrix (ι×τ) (ι×τ) ℂ), X.PosSemidef → (amplification Φ τ X).PosSemidef

def TracePreserving (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) : Prop :=
  ∀ X, (Φ X).trace=X.trace

/-- The Choi matrix uses output-input paired coordinates. -/
def choi (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    Matrix (ο×ι) (ο×ι) ℂ := fun a b => Φ (Matrix.single a.2 b.2 1) a.1 b.1

def entangledVector (ι : Type) [DecidableEq ι] : ι×ι → ℂ :=
  fun a => if a.1=a.2 then 1 else 0

 theorem choi_eq_amplification (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    choi Φ = amplification Φ ι
      (Matrix.vecMulVec (entangledVector ι) (star (entangledVector ι))) := by
  ext a b
  apply congrArg (fun X => Φ X a.1 b.1)
  ext i j
  by_cases hi : i=a.2 <;> by_cases hj : j=b.2 <;>
    simp [entangledVector, Matrix.vecMulVec_apply, Matrix.single_apply, hi, hj, eq_comm]

 theorem CompletelyPositive.choi_posSemidef
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ} (hΦ : CompletelyPositive Φ) :
    (choi Φ).PosSemidef := by
  rw [choi_eq_amplification]
  exact hΦ ι _ (Matrix.posSemidef_vecMulVec_self_star _)

/-- Square-root columns supply actual Kraus operators; no certificate is input. -/
def choiKraus (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    (ο×ι) → Matrix ο ι ℂ := fun a o i => CFC.sqrt (choi Φ) (o,i) a

 theorem choiKraus_gram (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : (choi Φ).PosSemidef) (o p : ο) (i j : ι) :
    ∑ a, choiKraus Φ a o i*star (choiKraus Φ a p j)=choi Φ (o,i) (p,j) := by
  have hR : (CFC.sqrt (choi Φ)).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hRR : CFC.sqrt (choi Φ)*(CFC.sqrt (choi Φ))ᴴ=choi Φ := by
    rw [hR.eq]
    exact CFC.sqrt_mul_sqrt_self _ hΦ.nonneg
  exact congrArg (fun X => X (o,i) (p,j)) hRR

 theorem map_eq_choi_sum (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (X : Matrix ι ι ℂ) (o p : ο) :
    Φ X o p = ∑ i, ∑ j, X i j*choi Φ (o,i) (p,j) := by
  have hx : X=∑ i, ∑ j, X i j • Matrix.single i j (1:ℂ) := by
    ext a b
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
    simp only [ite_and]
    simp [eq_comm]
  conv_lhs => rw [hx]
  simp only [choi, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

 theorem krausApply_entry (A : κ → Matrix ο ι ℂ) (X : Matrix ι ι ℂ) (o p : ο) :
    Extraction.krausApply A X o p = ∑ i, ∑ j, X i j*(∑ a, A a o i*star (A a p j)) := by
  simp only [Extraction.krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

 theorem choiKraus_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : (choi Φ).PosSemidef) (X : Matrix ι ι ℂ) :
    Extraction.krausApply (choiKraus Φ) X=Φ X := by
  ext o p
  rw [krausApply_entry,map_eq_choi_sum]
  simp_rw [choiKraus_gram Φ hΦ]

/-- The concrete finite Kraus action as a complex-linear map. -/
def krausLinearMap (A : κ → Matrix ο ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ where
  toFun := Extraction.krausApply A
  map_add' X Y := by
    simp only [Extraction.krausApply,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Extraction.krausApply,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum,
      RingHom.id_apply]

 theorem amplification_krausLinearMap (A : κ → Matrix ο ι ℂ)
    (τ : Type) [Fintype τ] [DecidableEq τ] (X : Matrix (ι×τ) (ι×τ) ℂ) :
    amplification (krausLinearMap A) τ X=Extraction.krausAmplification A τ X := by
  ext ⟨o,s⟩ ⟨p,t⟩
  exact (Extraction.krausAmplification_apply A τ X o p s t).symm

 theorem krausLinearMap_completelyPositive (A : κ → Matrix ο ι ℂ) :
    CompletelyPositive (krausLinearMap A) := by
  intro τ _ _ X hX
  rw [amplification_krausLinearMap]
  exact Extraction.krausAmplification_posSemidef A τ X hX

/-- The finite Choi theorem, in terms of all actual auxiliary matrix systems. -/
 theorem completelyPositive_iff_choi_posSemidef (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    CompletelyPositive Φ ↔ (choi Φ).PosSemidef := by
  refine ⟨CompletelyPositive.choi_posSemidef,fun hΦ => ?_⟩
  have he : krausLinearMap (choiKraus Φ)=Φ := by
    ext X o p
    exact congrArg (fun Y => Y o p) (choiKraus_apply Φ hΦ X)
  rw [← he]
  exact krausLinearMap_completelyPositive _

/-- Trace preservation forces the completeness identity; it is not an input
certificate for the Kraus representation. -/
 theorem kraus_complete_of_tracePreserving (A : κ → Matrix ο ι ℂ)
    (htrace : ∀ X, (Extraction.krausApply A X).trace=X.trace) :
    ∑ a, (A a)ᴴ*A a=1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  have hd : ((∑ a, (A a)ᴴ*A a)*X).trace=(Extraction.krausApply A X).trace := by
      simpa only [Extraction.krausApply,Matrix.mul_one,Matrix.one_mul,
        Matrix.conjTranspose_conjTranspose] using
        (Extraction.krausApply_trace_duality A X 1).symm
  simpa only [Matrix.one_mul] using hd.trans (htrace X)

 theorem choiKraus_complete (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : (choi Φ).PosSemidef) (ht : TracePreserving Φ) :
    ∑ a, (choiKraus Φ a)ᴴ*choiKraus Φ a=1 := by
  apply kraus_complete_of_tracePreserving
  intro X
  rw [choiKraus_apply Φ hΦ]
  exact ht X

/-- Exact finite-dimensional Kraus representation, derived from CP alone. -/
 theorem CompletelyPositive.exists_kraus
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ} (hΦ : CompletelyPositive Φ) :
    ∃ A : (ο×ι) → Matrix ο ι ℂ, ∀ X, Extraction.krausApply A X=Φ X :=
  ⟨choiKraus Φ,choiKraus_apply Φ hΦ.choi_posSemidef⟩

/-- CP and TP jointly produce complete actual Kraus operators. -/
 theorem CompletelyPositive.exists_complete_kraus
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ} (hΦ : CompletelyPositive Φ)
    (ht : TracePreserving Φ) :
    ∃ A : (ο×ι) → Matrix ο ι ℂ, (∑ a, (A a)ᴴ*A a=1) ∧
      ∀ X, Extraction.krausApply A X=Φ X :=
  ⟨choiKraus Φ,choiKraus_complete Φ hΦ.choi_posSemidef ht,
    choiKraus_apply Φ hΦ.choi_posSemidef⟩

end
end ExtractionCP
