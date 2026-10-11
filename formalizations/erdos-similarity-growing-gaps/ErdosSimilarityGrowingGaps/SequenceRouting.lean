import ErdosSimilarityGrowingGaps.SequenceGeometry
import ErdosSimilarityGrowingGaps.RoutingSeparation
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

/-- The finite routing separation theorem with actual logarithmic samples.
Its hypotheses are precisely strict activation and logarithmic separation; no
multiplicative indexing assumption is used. -/
theorem sequence_local_address_separation
    {M d t : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (x : ℝ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (child : Fin t → Fin (M - 1))
    (indices : Fin t → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (hindex : Function.Injective indices)
    (hactive : ∀ i, sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)) p)
    (hgap : ∀ i j, i ≠ j → child i = child j →
      3 ≤ p.1.1 * |Z.z (indices j) - Z.z (indices i)|) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v child
        (fun i => sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p))
      (localTerminalAddresses c hM hd v child
        (fun i => sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) := by
  apply actual_local_address_separation c hM hd hL x bits v child
  · intro i
    have hstart : 4 ≤ c.edgeStart
        (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) := by
      have hs := c.edgeStart_ge_origin
        (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)
      omega
    have hlen : 0 < c.edgeLength
        (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) :=
      RoutingTemplate.length_positive M c.gap c.baseLength
        (d - (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩).1.1.val) hM hL
    simpa only [RoutingTemplate.selectorEnd, RoutingTemplate.edgeEnd] using
      sequence_active_gridAddress_ne_center Z s₀ s₁ x
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (indices i) k hstart hlen p (hactive i)
  · intro i j hij hchild
    have hidx : indices i ≠ indices j := by
      intro heq
      exact hij (hindex heq)
    have hz : Z.z (indices i) ≠ Z.z (indices j) := by
      intro heq
      apply hidx
      exact Z.strictMono.injective heq
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have habs : |Z.z (indices j) - Z.z (indices i)| =
          Z.z (indices j) - Z.z (indices i) := by
        rw [abs_of_nonneg]
        linarith
      have hg : 3 ≤ p.1.1 * (Z.z (indices j) - Z.z (indices i)) := by
        rw [← habs]
        exact hgap i j hij hchild
      have hstart : 4 ≤ c.edgeStart
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) := by
        have hs := c.edgeStart_ge_origin
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)
        omega
      have hlen : 0 < c.edgeLength
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) :=
        RoutingTemplate.length_positive M c.gap c.baseLength
          (d - (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩).1.1.val) hM hL
      have hh := sequence_gridAddress_ne_of_log_gap Z s₀ s₁ x
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (indices i) (indices j) k hstart hlen p hg (hactive i) (by
          simpa only [hchild] using hactive j)
      simpa only [RoutingTemplate.selectorEnd, RoutingTemplate.edgeEnd] using hh
    · have habs : |Z.z (indices i) - Z.z (indices j)| =
          Z.z (indices i) - Z.z (indices j) := by
        rw [abs_of_nonneg]
        linarith
      have hg : 3 ≤ p.1.1 * (Z.z (indices i) - Z.z (indices j)) := by
        rw [← habs]
        exact hgap j i hij.symm hchild.symm
      have hstart : 4 ≤ c.edgeStart
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) := by
        have hs := c.edgeStart_ge_origin
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)
        omega
      have hlen : 0 < c.edgeLength
          (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) :=
        RoutingTemplate.length_positive M c.gap c.baseLength
          (d - (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩).1.1.val) hM hL
      have hh := sequence_gridAddress_ne_of_log_gap Z s₀ s₁ x
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        (indices j) (indices i) k hstart hlen p hg (by
          simpa only [hchild] using hactive j) (hactive i)
      have hh' := hh.symm
      simpa only [RoutingTemplate.selectorEnd, RoutingTemplate.edgeEnd] using hh'

end ErdosSimilarityGrowingGaps
