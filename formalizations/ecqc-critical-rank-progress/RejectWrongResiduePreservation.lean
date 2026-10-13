import QuadraticResidueReflection
open ECQCCriticalRank
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- A reflection in the ambient field need not preserve actual quadratic residues.
example : ∀ q : {q : ZMod 7 // q ∈ residues 7}, (1-q.val) ∈ residues 7 := by
  decide
