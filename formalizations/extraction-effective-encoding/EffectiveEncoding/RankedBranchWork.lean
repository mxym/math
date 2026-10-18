import EffectiveEncoding.EncodedRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The endpoint records themselves are retained; summing reads their returned
annotations and never re-invokes the rank callback. Counter arithmetic and this
additional traversal are not charged by the three annotations. -/
def endpointMassWork {n : ℕ} (xs : List (EncodedEndpoint n×ℕ)) (i : Fin 3) : ℕ :=
  (xs.map (fun a => a.1.work i)).sum


theorem endpointMassWork_bound {n : ℕ} (xs : List (EncodedEndpoint n×ℕ))
    (i : Fin 3) (B : ℕ) (h : ∀ a∈xs,a.1.work i≤B) :
    endpointMassWork xs i≤xs.length*B := by
  induction xs with
  | nil => simp [endpointMassWork]
  | cons a xs ih =>
    have ha:=h a (by simp)
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [endpointMassWork,List.map_cons,List.sum_cons,List.length_cons] at *
    calc
      _≤B+xs.length*B := Nat.add_le_add ha ht
      _=(xs.length+1)*B := by ring

structure RankedBranchRun (n : ℕ) where
  word : WordCode n
  work : RankWork

/-- Each endpoint and each mass is evaluated once and stored. Merge/Gray
compilation and the annotations consume only the stored records. -/
def rankedIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ} (hn : 0<n)
    (E : ι → EncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ) : RankedBranchRun n :=
  let pivot:=E p
  let initialMass:=c p
  let others:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  ⟨compileRaw hn (packedEntryProgram pivot.point
      (others.map (fun a => (a.1.point,a.2))) initialMass j),
    fun i => pivot.work i+endpointMassWork others i⟩


theorem rankedIndexedRun_word {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (E : ι → EncodedEndpoint n) (e : ι ↪ Bits n)
    (hE : ∀ a,(E a).point=packBits (e a)) (c : ι → ℕ) (p : ι) (j : ℕ) :
    (rankedIndexedRun hn E c p j).word=integerIndexedCode hn e c p j := by
  simp only [rankedIndexedRun,List.map_map,Function.comp_def,hE]
  exact packedIndexedRun_word hn e c p j


theorem rankedIndexedRun_work {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (E : ι → EncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ)
    (i : Fin 3) (B : ℕ) (hE : ∀ a,(E a).work i≤B) :
    (rankedIndexedRun hn E c p j).work i≤Fintype.card ι*B := by
  let xs:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  have hs : endpointMassWork xs i≤xs.length*B := by
    apply endpointMassWork_bound
    intro a ha
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ha
    exact hE a.1
  have hl : xs.length+1=Fintype.card ι := by
    have hc : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [xs,List.length_map,Finset.length_sort,Finset.card_attach,
      Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
    omega
  change (E p).work i+endpointMassWork xs i≤_
  calc
    _≤B+xs.length*B := Nat.add_le_add (hE p) hs
    _=(xs.length+1)*B := by ring
    _=Fintype.card ι*B := congrArg (fun a => a*B) hl


def rankedBranchRun {k : ℕ} (ν : Sym (Fin 4) (k+1)) : RankedBranchRun (2+codeWires k) :=
  rankedIndexedRun (by omega) (encodedBranchEndpoint ν) (fun i => ν.val.count i.1)
    (occupiedPivot ν) (k+1)


theorem rankedBranchRun_word {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (rankedBranchRun ν).word=branchCode (constructedCompactEncoding k) ν :=
  rankedIndexedRun_word _ _ _ (encodedBranchEndpoint_value ν) _ _ _


theorem rankedBranchRun_work {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 3) :
    (rankedBranchRun ν).work i≤4*(rankWorkConstant i*(k+1)^3) := by
  have h:=rankedIndexedRun_work (by omega) (encodedBranchEndpoint ν)
    (fun a => ν.val.count a.1) (occupiedPivot ν) (k+1) i
    (rankWorkConstant i*(k+1)^3) (fun a => encodedBranchEndpoint_work ν a i)
  have hc : Fintype.card {a : Fin 4 // a∈ν}≤4 :=
    Fintype.card_le_of_injective (fun a : {a : Fin 4 // a∈ν} => a.1) Subtype.val_injective
  exact h.trans (Nat.mul_le_mul_right _ hc)

end EffectiveEncoding
