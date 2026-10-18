import EffectiveEncoding.DirectPackedExtraction

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Three SPECIFIED annotations from the executed constructive rank program:
list-construction events, filtering requests, and Nat-equality requests. -/
abbrev RankWork := Fin 3 → ℕ

def rankWorkConstant : RankWork := ![28,1,3]

structure EncodedEndpoint (n : ℕ) where
  point : PackedBits n
  work : RankWork

/-- Compute rank once, retain its actual annotations, and construct the
packed binary endpoint from the stored Fin index. -/
def encodedOccupationProgram {k : ℕ} (ν : Sym (Fin 4) k) : EncodedEndpoint (codeWires k) :=
  let ranked:=constructiveRankProgram ν
  ⟨List.Vector.ofFn (fun j => ranked.index.val.testBit j.val),
    ![ranked.constructionSteps,ranked.predicateQueries,ranked.natEqualityQueries]⟩


theorem encodedOccupationProgram_value {k : ℕ} (ν : Sym (Fin 4) k) :
    unpackBits (encodedOccupationProgram ν).point=constructedCompactEncoding k ν := by
  funext j
  change (List.Vector.ofFn (fun j : Fin (codeWires k) =>
    (constructiveRankProgram ν).index.val.testBit j.val)).get j=_
  rw [List.Vector.get_ofFn]
  rfl


theorem encodedOccupationProgram_work {k : ℕ} (ν : Sym (Fin 4) k) (i : Fin 3) :
    (encodedOccupationProgram ν).work i≤rankWorkConstant i*(k+1)^3 := by
  fin_cases i
  · exact constructiveRankProgram_constructionSteps ν
  · change (constructiveRankProgram ν).predicateQueries ≤ 1*(k+1)^3
    rw [one_mul]
    exact (constructiveRankProgram_predicateQueries ν).le
  · exact constructiveRankProgram_natEqualityQueries ν


def encodedBranchEndpoint {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : {i : Fin 4 // i∈ν}) :
    EncodedEndpoint (2+codeWires k) :=
  let child:=encodedOccupationProgram (ν.erase i.1 i.2)
  ⟨packBits (Fin.append (letterBits i.1) (unpackBits child.point)),child.work⟩


theorem encodedBranchEndpoint_value {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : {i : Fin 4 // i∈ν}) :
    (encodedBranchEndpoint ν i).point=packBits (branchEmbedding (constructedCompactEncoding k) ν i) := by
  simp only [encodedBranchEndpoint,encodedOccupationProgram_value,branchEmbedding]
  rfl


theorem encodedBranchEndpoint_work {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (a : {i : Fin 4 // i∈ν}) (i : Fin 3) :
    (encodedBranchEndpoint ν a).work i≤rankWorkConstant i*(k+1)^3 :=
  encodedOccupationProgram_work (ν.erase a.1 a.2) i


def encodedNextEndpoint {k : ℕ} (ν : Sym (Fin 4) (k+1)) : EncodedEndpoint (2+codeWires k) :=
  let child:=encodedOccupationProgram ν
  ⟨packBits (extendBits (codeWires_step k) (unpackBits child.point)),child.work⟩


theorem encodedNextEndpoint_value {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (encodedNextEndpoint ν).point=packBits (constructedNextEncoding k ν) := by
  simp only [encodedNextEndpoint,encodedOccupationProgram_value,constructedNextEncoding,extendEmbedding]
  rfl


theorem encodedNextEndpoint_work {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 3) :
    (encodedNextEndpoint ν).work i≤rankWorkConstant i*(k+2)^3 := by
  simpa only [encodedNextEndpoint,Nat.add_assoc,Nat.reduceAdd] using encodedOccupationProgram_work ν i

end EffectiveEncoding
