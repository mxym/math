import EffectiveEncoding.Enumeration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The filter predicate is evaluated once at every candidate, including
rejected candidates. This annotation counts calls, not predicate bit time. -/
def filterWithQueries {α : Type*} (p : α → Bool) : List α → List α×ℕ
  | [] => ([],0)
  | x::xs =>
    let accepted:=p x
    let tail:=filterWithQueries p xs
    (if accepted then x::tail.1 else tail.1,tail.2+1)

theorem filterWithQueries_erase {α : Type*} (p : α → Bool) (xs : List α) :
    (filterWithQueries p xs).1=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filterWithQueries,List.filter_cons,ih]

theorem filterWithQueries_queries {α : Type*} (p : α → Bool) (xs : List α) :
    (filterWithQueries p xs).2=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filterWithQueries,ih]


def countedTriples (k : ℕ) : List Triple×ℕ :=
  filterWithQueries (fun t => decide (total t≤k))
    ((List.range (k+1)) ×ˢ ((List.range (k+1)) ×ˢ (List.range (k+1))))

theorem countedTriples_erase (k : ℕ) : (countedTriples k).1=triples k :=
  filterWithQueries_erase _ _

theorem countedTriples_queries (k : ℕ) : (countedTriples k).2=(k+1)^3 := by
  simp [countedTriples,filterWithQueries_queries,List.length_product,pow_succ,Nat.mul_assoc]

def occupationList (k : ℕ) (ts : List Triple) (h : ∀ t∈ts,total t≤k) :
    List (Sym (Fin 4) k) := ts.attach.map (fun t => fromTriple k t.1 (h t.1 t.2))

theorem occupationList_congr (k : ℕ) {ts us : List Triple} (he : ts=us)
    (ht : ∀ t∈ts,total t≤k) (hu : ∀ t∈us,total t≤k) :
    occupationList k ts ht=occupationList k us hu := by cases he;rfl

/-- Reuses the stored filtered candidate list. Proof attachment is erased;
its map invokes the actual occupation constructor once per accepted triple. -/
def countedOccupations (k : ℕ) : List (Sym (Fin 4) k)×ℕ :=
  let ts:=countedTriples k
  (occupationList k ts.1 (by
    intro t ht
    apply mem_triples.mp
    have ht' : t∈(countedTriples k).1 := ht
    rwa [countedTriples_erase] at ht'),ts.2)

theorem countedOccupations_erase (k : ℕ) : (countedOccupations k).1=occupations k := by
  have hc : ∀ t∈(countedTriples k).1,total t≤k := by
    intro t ht
    apply mem_triples.mp
    rwa [countedTriples_erase] at ht
  change occupationList k (countedTriples k).1 hc=occupations k
  exact occupationList_congr k (countedTriples_erase k) hc (fun _ ht => mem_triples.mp ht)

theorem countedOccupations_queries (k : ℕ) : (countedOccupations k).2=(k+1)^3 :=
  countedTriples_queries k

theorem countedOccupations_constructorCalls (k : ℕ) :
    (countedOccupations k).1.length=occupationRank k := by
  rw [countedOccupations_erase,occupations_length]

theorem countedOccupations_constructorCalls_bound (k : ℕ) :
    (countedOccupations k).1.length≤(k+1)^3 := by
  rw [countedOccupations_erase]
  exact enumeration_candidate_bound k

/-- An equality scan, with no assumed constant-time equality implementation. -/
def indexWithQueries {α : Type*} [BEq α] (x : α) : List α → ℕ×ℕ
  | [] => (0,0)
  | y::ys => if y==x then (0,1) else
      let tail:=indexWithQueries x ys
      (tail.1+1,tail.2+1)

theorem indexWithQueries_erase {α : Type*} [BEq α] (x : α) (xs : List α) :
    (indexWithQueries x xs).1=xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [indexWithQueries,List.idxOf_cons]
    split <;> simp_all

theorem indexWithQueries_queries {α : Type*} [BEq α] (x : α) (xs : List α) :
    (indexWithQueries x xs).2≤xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [indexWithQueries,List.length_cons]
    split <;> dsimp only <;> omega

structure RankRun (k : ℕ) where
  index : Fin (occupationRank k)
  candidateQueries : ℕ
  equalityQueries : ℕ

/-- Eagerly constructs the actual enumeration once, then scans it once. -/
def countedRank {k : ℕ} (ν : Sym (Fin 4) k) : RankRun k :=
  let table:=countedOccupations k
  let scan:=indexWithQueries ν table.1
  ⟨⟨scan.1,by
    change (indexWithQueries ν (countedOccupations k).1).1<occupationRank k
    rw [indexWithQueries_erase,countedOccupations_erase]
    exact (rank ν).isLt⟩,table.2,scan.2⟩

theorem countedRank_erase {k : ℕ} (ν : Sym (Fin 4) k) : (countedRank ν).index=rank ν := by
  apply Fin.ext
  simp only [countedRank,indexWithQueries_erase,countedOccupations_erase,rank]

theorem countedRank_candidateQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (countedRank ν).candidateQueries=(k+1)^3 := countedOccupations_queries k

theorem countedRank_equalityQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (countedRank ν).equalityQueries≤occupationRank k := by
  have h:=indexWithQueries_queries ν (countedOccupations k).1
  simpa only [countedRank,countedOccupations_erase,occupations_length] using h

theorem countedRank_equalityQueries_polynomial {k : ℕ} (ν : Sym (Fin 4) k) :
    (countedRank ν).equalityQueries≤(k+1)^3 :=
  (countedRank_equalityQueries ν).trans (by
    simpa only [occupations_length] using enumeration_candidate_bound k)

end EffectiveEncoding
