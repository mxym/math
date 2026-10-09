import CholletGraphDiagonalBridge
import CholletGraphSumMatrices
import CholletRobustBlock

/-! Vertex-count induction interfaces, with nonnegative diagonal additions
as the strengthened conclusion. All matrices are actual graph Laplacians. -/
set_option autoImplicit false
open scoped BigOperators
universe u
namespace Chollet
noncomputable section

def SmallerDiagonalStrong (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    Fintype.card W < n → LaplacianDiagonalStrong H

variable {V W : Type u} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem matrixStrong_restriction_of_smaller (n : ℕ) (ih : SmallerDiagonalStrong.{u} n)
    (e : W ↪ V) (hcard : Fintype.card W < n) (a : V → ℝ) (ha : ∀ i,0 ≤ a i) :
    MatrixStrong ((G.lapMatrix ℝ+Matrix.diagonal a).submatrix e e) := by
  rw [laplacian_diagonal_restriction G e a]
  exact ih W (G.comap e) hcard (degreeCorrection G e a)
    (degreeCorrection_nonneg G e a ha)

theorem diagonalStrong_of_whole_and_smaller
    (ih : SmallerDiagonalStrong.{u} (Fintype.card V))
    (hwhole : MatrixStrong (G.lapMatrix ℝ)) : LaplacianDiagonalStrong G := by
  intro a ha
  apply matrixStrong_diagonal_extension _ (SimpleGraph.posSemidef_lapMatrix ℝ G) hwhole _ a ha
  intro b hb v
  let e : {i : V // i ≠ v} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  exact matrixStrong_restriction_of_smaller G _ ih e
    (Fintype.card_subtype_lt (x := v) (by simp)) b hb

variable {α β : Type u} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem matrixStrong_directSum_laplacian (n : ℕ) (ih : SmallerDiagonalStrong.{u} n)
    (H : SimpleGraph (α ⊕ β)) [DecidableRel H.Adj]
    (hsize : Fintype.card (α ⊕ β)=n)
    (ha : 0 < Fintype.card α) (hb : 0 < Fintype.card β)
    (hcross : ∀ a b,¬H.Adj (.inl a) (.inr b)) : MatrixStrong (H.lapMatrix ℝ) := by
  have hc : Fintype.card α+Fintype.card β=n := by simpa only [Fintype.card_sum] using hsize
  have hleft := ih α (H.comap Sum.inl) (by omega) (fun _ => 0) (fun _ => le_rfl)
  have hright := ih β (H.comap Sum.inr) (by omega) (fun _ => 0) (fun _ => le_rfl)
  simp only [Matrix.diagonal_zero,add_zero] at hleft hright
  unfold MatrixStrong
  rw [laplacian_directSum_identity H hcross]
  exact strongChollet_directSumMatrix _ _ hleft hright

theorem matrixStrong_onePointSum_laplacian (n : ℕ) (ih : SmallerDiagonalStrong.{u} n)
    (H : SimpleGraph (Option (α ⊕ β))) [DecidableRel H.Adj]
    (hsize : Fintype.card (Option (α ⊕ β))=n)
    (ha : 0 < Fintype.card α) (hb : 0 < Fintype.card β)
    (hcross : ∀ a b,¬H.Adj (some (.inl a)) (some (.inr b))) : MatrixStrong (H.lapMatrix ℝ) := by
  have hc : Fintype.card α+Fintype.card β+1=n := by
    simpa only [Fintype.card_option,Fintype.card_sum] using hsize
  let HL := H.comap (optionLeftEmbedding (α := α) (β := β))
  let HR := H.comap (optionRightEmbedding (α := α) (β := β))
  have hcl : Fintype.card (Option α)<n := by simp only [Fintype.card_option]; omega
  have hcr : Fintype.card (Option β)<n := by simp only [Fintype.card_option]; omega
  have hl := ih (Option α) HL hcl (fun _ => 0) (fun _ => le_rfl)
  have hr := ih (Option β) HR hcr (fun _ => 0) (fun _ => le_rfl)
  simp only [Matrix.diagonal_zero,add_zero] at hl hr
  let el : α ↪ Option α := ⟨some,Option.some_injective α⟩
  let er : β ↪ Option β := ⟨some,Option.some_injective β⟩
  have hdl := matrixStrong_restriction_of_smaller HL n ih el (by omega)
    (fun _ => 0) (fun _ => le_rfl)
  have hdr := matrixStrong_restriction_of_smaller HR n ih er (by omega)
    (fun _ => 0) (fun _ => le_rfl)
  simp only [Matrix.diagonal_zero,add_zero] at hdl hdr
  have ht := rootStrong_onePointSum_psd (HL.lapMatrix ℝ) (HR.lapMatrix ℝ)
    (SimpleGraph.posSemidef_lapMatrix ℝ HL) (SimpleGraph.posSemidef_lapMatrix ℝ HR)
    hl hr hdl hdr
  unfold MatrixStrong
  rw [laplacian_onePointSum_identity H hcross]
  exact ht.whole

end
end Chollet
