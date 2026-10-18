import EffectiveEncoding.LiteralOccupationExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem packBits_eq_iff {n : ℕ} (x y : Bits n) : packBits x=packBits y ↔ x=y := by
  constructor
  · intro h
    have hv:=congrArg unpackBits h
    simpa only [unpackBits_packBits] using hv
  · exact congrArg packBits

/-- Merge precomputed masses at precomputed packed endpoints. The finite
vector check avoids carrying runtime proof objects; valid branch endpoints
are internally proved distinct from the pivot. -/
def packedEntryProgram {n : ℕ} (p : PackedBits n) :
    List (PackedBits n×ℕ) → ℕ → ℕ → List (RawCode n)
  | [],_,_ => []
  | (q,B)::qs,A,j => if h : p=q then packedEntryProgram p qs A j else
      .merge (unpackBits p) (unpackBits q) (fun he => h (unpackBits_injective n he)) A B j::
        packedEntryProgram p qs (A+B) j


def packedIndexedEntries {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) : List (PackedBits n×ℕ) :=
  ((Finset.univ.erase p).attach.sort (·≤·)).map (fun i =>
    let endpoint:=e i.1
    let mass:=c i.1
    (packBits endpoint,mass))


theorem packedEntryProgram_indexed {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι)
    (xs : List {i : ι // i∈Finset.univ.erase p}) (A j : ℕ) :
    packedEntryProgram (packBits (e p)) (xs.map (fun i => (packBits (e i.1),c i.1))) A j=
      countProgram (e p) (indexedCount e c)
        (xs.map (fun i => ⟨e i.1,fun h => (Finset.mem_erase.mp i.2).1 (e.injective h)⟩)) A j := by
  induction xs generalizing A with
  | nil => rfl
  | cons i xs ih =>
    have hp : packBits (e p)≠packBits (e i.1) := by
      intro h
      exact (Finset.mem_erase.mp i.2).1 (e.injective ((packBits_eq_iff _ _).mp h).symm)
    simp only [List.map_cons,packedEntryProgram,dite_eq_right hp,unpackBits_packBits,
      countProgram,indexedCount_image,ih]

structure PackedIndexedRun (n : ℕ) where
  word : WordCode n
  embeddingRequests : ℕ
  massRequests : ℕ

/-- The pivot and every other endpoint/mass are each evaluated and stored
once. Subsequent merge and Gray compilation read only these stored values. -/
def packedIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ} (hn : 0<n)
    (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ) : PackedIndexedRun n :=
  let pivot:=packBits (e p)
  let initialMass:=c p
  let entries:=packedIndexedEntries e c p
  ⟨compileRaw hn (packedEntryProgram pivot entries initialMass j),1+entries.length,1+entries.length⟩


theorem packedIndexedRun_word {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ} (hn : 0<n)
    (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ) :
    (packedIndexedRun hn e c p j).word=integerIndexedCode hn e c p j := by
  simp only [packedIndexedRun,packedIndexedEntries,packedEntryProgram_indexed,integerIndexedCode,explicitOthers]


theorem packedIndexedRun_requests {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ} (hn : 0<n)
    (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ) :
    (packedIndexedRun hn e c p j).embeddingRequests=Fintype.card ι ∧
      (packedIndexedRun hn e c p j).massRequests=Fintype.card ι := by
  have hc : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p⟩
  simp only [packedIndexedRun,packedIndexedEntries,List.length_map,Finset.length_sort,
    Finset.card_attach,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
  constructor <;> omega


def packedBranchRun {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : PackedIndexedRun (2+q) :=
  packedIndexedRun (by omega) (branchEmbedding enc ν) (fun i => ν.val.count i.1)
    (occupiedPivot ν) (k+1)


theorem packedBranchRun_word {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : (packedBranchRun enc ν).word=branchCode enc ν :=
  packedIndexedRun_word _ _ _ _ _


theorem packedBranchRun_requests {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    (packedBranchRun enc ν).embeddingRequests≤4 ∧ (packedBranchRun enc ν).massRequests≤4 := by
  have h:=packedIndexedRun_requests (by omega) (branchEmbedding enc ν)
    (fun i => ν.val.count i.1) (occupiedPivot ν) (k+1)
  have hc : Fintype.card {i : Fin 4 // i∈ν}≤4 :=
    Fintype.card_le_of_injective (fun i : {i : Fin 4 // i∈ν} => i.1) Subtype.val_injective
  constructor <;> simpa only [packedBranchRun,h.1,h.2] using hc

end EffectiveEncoding
