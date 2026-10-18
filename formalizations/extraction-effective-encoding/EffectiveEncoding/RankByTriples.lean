import EffectiveEncoding.CountedEnumeration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- All three Nat equalities are explicitly evaluated and stored. Their bit
cost is not assumed constant; the annotation counts calls only. -/
def tripleEqualityRun (a b : Triple) : Bool×ℕ :=
  let x:=a.1==b.1
  let y:=a.2.1==b.2.1
  let z:=a.2.2==b.2.2
  (x&&(y&&z),3)


theorem tripleEqualityRun_value (a b : Triple) : (tripleEqualityRun a b).1=(a==b) := rfl

theorem tripleEqualityRun_count (a b : Triple) : (tripleEqualityRun a b).2=3 := rfl


def indexTriplesWithQueries (x : Triple) : List Triple → ℕ×ℕ
  | [] => (0,0)
  | y::ys =>
    let test:=tripleEqualityRun y x
    if test.1 then (0,test.2) else
      let tail:=indexTriplesWithQueries x ys
      (tail.1+1,test.2+tail.2)


theorem indexTriplesWithQueries_value (x : Triple) (xs : List Triple) :
    (indexTriplesWithQueries x xs).1=xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [indexTriplesWithQueries,tripleEqualityRun_value,List.idxOf_cons]
    split <;> simp_all


theorem indexTriplesWithQueries_count (x : Triple) (xs : List Triple) :
    (indexTriplesWithQueries x xs).2≤3*xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [indexTriplesWithQueries,tripleEqualityRun_count,List.length_cons]
    split <;> dsimp only <;> omega


theorem toTriple_injective (k : ℕ) : Function.Injective (@toTriple k) := by
  intro a b h
  have hs : (⟨toTriple a,toTriple_le a⟩ : {t : Triple // total t≤k})=
      ⟨toTriple b,toTriple_le b⟩ := Subtype.ext h
  have he:=congrArg (fun t : {t : Triple // total t≤k} => fromTriple k t.1 t.2) hs
  simpa only [fromTriple_toTriple] using he


theorem occupations_toTriple (k : ℕ) : (occupations k).map toTriple=triples k := by
  simp [occupations,List.map_map,Function.comp_def,List.attach_map_subtype_val]


theorem idxOf_map_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    (xs.map f).idxOf (f x)=xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y=x
    · subst y
      simp only [List.map_cons,List.idxOf_cons,beq_self_eq_true,ite_true]
    · have hfx : f y≠f x := fun he => h (hf he)
      simp only [List.map_cons,List.idxOf_cons,beq_false_of_ne h,beq_false_of_ne hfx,
        Bool.false_eq_true,ite_false,ih]


theorem triples_length (k : ℕ) : (triples k).length=occupationRank k := by
  rw [← occupations_toTriple k,List.length_map,occupations_length]

structure TripleRankRun (k : ℕ) where
  index : Fin (occupationRank k)
  predicateQueries : ℕ
  natEqualityQueries : ℕ

/-- Rank without constructing any candidate multisets or comparing them.
Only the input's three occupation counts and the filtered Nat triples are used. -/
def tripleRankProgram {k : ℕ} (ν : Sym (Fin 4) k) : TripleRankRun k :=
  let candidates:=countedTriples k
  let scan:=indexTriplesWithQueries (toTriple ν) candidates.1
  ⟨⟨scan.1,by
    change (indexTriplesWithQueries (toTriple ν) (countedTriples k).1).1<occupationRank k
    rw [indexTriplesWithQueries_value,countedTriples_erase,← triples_length]
    exact List.idxOf_lt_length_iff.mpr (mem_triples.mpr (toTriple_le ν))⟩,
    candidates.2,scan.2⟩


def rankByTriples {k : ℕ} (ν : Sym (Fin 4) k) : Fin (occupationRank k) := (tripleRankProgram ν).index


theorem rankByTriples_eq {k : ℕ} (ν : Sym (Fin 4) k) : rankByTriples ν=rank ν := by
  apply Fin.ext
  change (indexTriplesWithQueries (toTriple ν) (countedTriples k).1).1=(occupations k).idxOf ν
  rw [indexTriplesWithQueries_value,countedTriples_erase,← occupations_toTriple]
  exact idxOf_map_injective toTriple (toTriple_injective k) ν (occupations k)


theorem tripleRankProgram_predicateQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (tripleRankProgram ν).predicateQueries=(k+1)^3 := countedTriples_queries k


theorem tripleRankProgram_natEqualityQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (tripleRankProgram ν).natEqualityQueries≤3*(k+1)^3 := by
  have h:=indexTriplesWithQueries_count (toTriple ν) (countedTriples k).1
  have hl : (triples k).length≤(k+1)^3 := by
    simpa only [occupations,List.length_map,List.length_attach] using enumeration_candidate_bound k
  have hh : (tripleRankProgram ν).natEqualityQueries≤3*(triples k).length := by
    simpa only [tripleRankProgram,countedTriples_erase] using h
  exact hh.trans (Nat.mul_le_mul_left 3 hl)

end EffectiveEncoding
