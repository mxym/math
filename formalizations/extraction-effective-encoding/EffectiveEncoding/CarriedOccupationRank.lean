import EffectiveEncoding.AccumulatedRankExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Execute the same rank table and scan directly on an already available
triple. No occupation count or quotient traversal is used by this program. -/
def carriedTripleRankProgram (k : ℕ) (t : Triple) (h : total t≤k) : ConstructiveRankRun k :=
  let candidates:=triplesBuild k
  let scan:=indexTriplesWithQueries t candidates.items
  ⟨⟨scan.1,by
    change (indexTriplesWithQueries t (triplesBuild k).items).1<occupationRank k
    rw [indexTriplesWithQueries_value,triplesBuild_items,← triples_length]
    exact List.idxOf_lt_length_iff.mpr (mem_triples.mpr h)⟩,
    candidates.steps,candidates.queries,scan.2⟩


theorem carriedTripleRankProgram_toTriple {k : ℕ} (ν : Sym (Fin 4) k) :
    carriedTripleRankProgram k (toTriple ν) (toTriple_le ν)=constructiveRankProgram ν := rfl


def carriedEncodedEndpoint (k : ℕ) (t : Triple) (h : total t≤k) : EncodedEndpoint (codeWires k) :=
  let ranked:=carriedTripleRankProgram k t h
  ⟨List.Vector.ofFn (fun j => ranked.index.val.testBit j.val),
    ![ranked.constructionSteps,ranked.predicateQueries,ranked.natEqualityQueries]⟩


theorem carriedEncodedEndpoint_toTriple {k : ℕ} (ν : Sym (Fin 4) k) :
    carriedEncodedEndpoint k (toTriple ν) (toTriple_le ν)=encodedOccupationProgram ν := rfl


theorem carriedEncodedEndpoint_eq {k : ℕ} (ν : Sym (Fin 4) k)
    (t : Triple) (ht : t=toTriple ν) (h : total t≤k) :
    carriedEncodedEndpoint k t h=encodedOccupationProgram ν := by
  subst t
  rfl


theorem carriedEncodedEndpoint_value {k : ℕ} (ν : Sym (Fin 4) k)
    (t : Triple) (h : total t≤k) (ht : t=toTriple ν) :
    unpackBits (carriedEncodedEndpoint k t h).point=constructedCompactEncoding k ν := by
  subst t
  exact encodedOccupationProgram_value ν


theorem carriedEncodedEndpoint_work (k : ℕ) (t : Triple) (h : total t≤k) (i : Fin 3) :
    (carriedEncodedEndpoint k t h).work i≤rankWorkConstant i*(k+1)^3 := by
  have he : carriedEncodedEndpoint k t h=encodedOccupationProgram (fromTriple k t h) := by
    simpa only [toTriple_fromTriple] using carriedEncodedEndpoint_toTriple (fromTriple k t h)
  rw [he]
  exact encodedOccupationProgram_work _ i

/-- An occupation keeps its original loop triple beside the literal value.
The equality is proof-only; runtime rank and masses read the retained triple. -/
structure CarriedOccupation (k : ℕ) where
  occupation : Sym (Fin 4) k
  triple : Triple
  triple_eq : triple=toTriple occupation


def carriedOccupationLiteral (k : ℕ) (t : Triple) (h : total t≤k) : CarriedOccupation k :=
  let literal:=occupationLiteralProgram k t h
  ⟨literal.occupation,t,by rw [occupationLiteralProgram_value,toTriple_fromTriple]⟩


theorem carriedOccupationLiteral_value (k : ℕ) (t : Triple) (h : total t≤k) :
    (carriedOccupationLiteral k t h).occupation=fromTriple k t h :=
  occupationLiteralProgram_value k t h


def carriedOccupationTable (k : ℕ) : List (CarriedOccupation k) :=
  (triplesBuild k).items.attach.map (fun t =>
    carriedOccupationLiteral k t.1 (by
      apply mem_triples.mp
      simpa only [triplesBuild_items] using t.2))


theorem carriedOccupationTable_values (k : ℕ) :
    (carriedOccupationTable k).map CarriedOccupation.occupation=(literalOccupationTable k).occupations := by
  simp only [carriedOccupationTable,List.map_map,Function.comp_def,
    carriedOccupationLiteral_value,literalOccupationTable,occupationLiteralProgram_value]


def erasedTriple (t : Triple) (a : Fin 4) : Triple :=
  (if a=0 then t.1-1 else t.1,
    if a=1 then t.2.1-1 else t.2.1,
    if a=2 then t.2.2-1 else t.2.2)


theorem erasedTriple_toTriple {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (a : {a : Fin 4 // a∈ν}) :
    erasedTriple (toTriple ν) a.1=toTriple (ν.erase a.1 a.2) := by
  rcases a with ⟨a,ha⟩
  fin_cases a <;> simp [erasedTriple,toTriple,Sym.coe_erase,Multiset.count_erase_of_ne]


def carriedMass {k : ℕ} (x : CarriedOccupation k) (a : Fin 4) : ℕ :=
  if a=0 then x.triple.1 else if a=1 then x.triple.2.1 else
    if a=2 then x.triple.2.2 else k-total x.triple


theorem carriedMass_value {k : ℕ} (x : CarriedOccupation k) (a : Fin 4) :
    carriedMass x a=x.occupation.val.count a := by
  have ht:=count_total x.occupation
  fin_cases a <;> simp only [carriedMass,x.triple_eq,toTriple,total] at * <;> norm_num at * <;> omega

end EffectiveEncoding
