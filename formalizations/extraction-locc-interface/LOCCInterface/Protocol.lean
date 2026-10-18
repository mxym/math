import LOCCInterface.Tree

open scoped BigOperators ComplexOrder Kronecker
open Matrix MinimaxProfile
namespace ExtractionLOCC
noncomputable section

namespace Tree
variable {a b c d : ℕ}

/-- Two independent local channels are a two-round tree: Alice communicates
her Kraus outcome and Bob performs the same instrument on every such branch. -/
def product (r s : ℕ) (A : Fin r → Matrix (Fin c) (Fin a) ℂ)
    (B : Fin s → Matrix (Fin d) (Fin b) ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ i, (B i)ᴴ * B i = 1) :
    Tree c d a b :=
  .alice r (fun _ => c) A hA
    (fun _ => .bob s (fun _ => d) B hB (fun _ => .done))

theorem product_channel (r s : ℕ) (A : Fin r → Matrix (Fin c) (Fin a) ℂ)
    (B : Fin s → Matrix (Fin d) (Fin b) ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ i, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (product r s A B hA hB).channel X =
      Extraction.krausApply (Extraction.productKraus A B) X := by
  unfold product
  rw [channel_alice]
  simp_rw [channel_bob, channel_done]
  simp only [Extraction.krausApply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ B j) *
      (A i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = A i ⊗ₖ B j := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Extraction.productKraus]
    using congrArg (fun L => L * X * Lᴴ) h

/-- Every finite LOCC tree is a genuine cPPT channel on the output systems. -/
def pptChannel {K : ℕ} (T : Tree K K a b) : ExtractionCP.PPTChannel a b K where
  map := T.channel
  cp := T.channel_completelyPositive
  tp := T.channel_tracePreserving
  ppt := T.channel_pt_completelyPositive

def protocol {K : ℕ} (T : Tree K K a b)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) : KrausPPTProtocol a b K :=
  T.pptChannel.toKrausPPTProtocol U

theorem protocol_apply {K : ℕ} (T : Tree K K a b)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Extraction.krausApply (T.protocol U).A X = T.channel X :=
  T.pptChannel.toKrausPPTProtocol_apply U X

end Tree

/-- Actual finite-round LOCC semantics, defined by an adaptive local-instrument
execution tree and equality of its full complex-linear channel. -/
def IsFiniteLOCC {a b c d : ℕ}
    (Φ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) : Prop :=
  ∃ T : Tree c d a b, T.channel = Φ

theorem IsFiniteLOCC.completelyPositive {a b c d : ℕ}
    {Φ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ} (h : IsFiniteLOCC Φ) :
    ExtractionCP.CompletelyPositive Φ := by
  obtain ⟨T,rfl⟩ := h
  exact T.channel_completelyPositive

theorem IsFiniteLOCC.tracePreserving {a b c d : ℕ}
    {Φ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ} (h : IsFiniteLOCC Φ) :
    ExtractionCP.TracePreserving Φ := by
  obtain ⟨T,rfl⟩ := h
  exact T.channel_tracePreserving

theorem IsFiniteLOCC.pt_completelyPositive {a b c d : ℕ}
    {Φ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ} (h : IsFiniteLOCC Φ) :
    ExtractionCP.CompletelyPositive (ExtractionCP.ptConjugate Φ) := by
  obtain ⟨T,rfl⟩ := h
  exact T.channel_pt_completelyPositive

/-- The predicate constrains the actual postprocessing map. The separately
specified global preprocessing unitary is exactly the existing model's U. -/
def IsFiniteLOCCProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K) : Prop :=
  IsFiniteLOCC (ExtractionCP.krausLinearMap P.A)

theorem tree_isFiniteLOCCProtocol {a b K : ℕ} (T : Tree K K a b)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) : IsFiniteLOCCProtocol (T.protocol U) := by
  refine ⟨T, ?_⟩
  ext X p q
  exact congrFun (congrFun (T.protocol_apply U X).symm p) q

theorem productLocal_isFiniteLOCCProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K)
    (hP : P.IsProductLocal) : IsFiniteLOCCProtocol P := by
  obtain ⟨r,s,A,B,hA,hB,hmap⟩ := hP
  refine ⟨Tree.product r s A B hA hB, ?_⟩
  ext X p q
  exact congrFun (congrFun ((Tree.product_channel r s A B hA hB X).trans (hmap X).symm) p) q

/-- Existence is proved from tree semantics; the PPT/Kraus data are conclusions. -/
theorem IsFiniteLOCC.exists_actual_protocol {a b K : ℕ}
    {Φ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ} (h : IsFiniteLOCC Φ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    ∃ P : KrausPPTProtocol a b K, P.U = U ∧ IsFiniteLOCCProtocol P ∧
      ∀ X, Extraction.krausApply P.A X = Φ X := by
  obtain ⟨T,rfl⟩ := h
  exact ⟨T.protocol U,rfl,tree_isFiniteLOCCProtocol T U,T.protocol_apply U⟩

end
end ExtractionLOCC
