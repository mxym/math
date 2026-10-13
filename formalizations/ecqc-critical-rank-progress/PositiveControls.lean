import QuadraticResidueReflection
import DistinguishedColumn

open ECQCCriticalRank
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The exceptional prime-three reflection really exists. -/
example : ∃ (κ : ZMod 3)
    (σ : {q : ZMod 3 // q ∈ residues 3} ≃ {q : ZMod 3 // q ∈ residues 3}),
    κ ≠ 0 ∧ ∀ q, q.val + (σ q).val = κ := by
  refine ⟨1, Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩, by decide, ?_⟩
  decide

/-- Positive residue reflections at a non-exceptional admissible prime. -/
example : ∃ (σ : {q : ZMod 5 // q ∈ residues 5} ≃ {q : ZMod 5 // q ∈ residues 5}),
    ∀ q, q.val + (σ q).val = 0 := by
  refine ⟨Equiv.swap ⟨1, by decide⟩ ⟨4, by decide⟩, ?_⟩
  decide
