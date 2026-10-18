import EffectiveEncoding.CarriedRankExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Runtime occupation data contains three integers and an erased bound proof. -/
abbrev NativeOccupation (k : ℕ) := {t : Triple // total t≤k}

/-- Semantic interpretation only; native generation programs do not construct
this multiset as a runtime value. -/
def nativeOccupationValue {k : ℕ} (x : NativeOccupation k) : Sym (Fin 4) k :=
  fromTriple k x.1 x.2


def nativeMass {k : ℕ} (x : NativeOccupation k) (a : Fin 4) : ℕ :=
  if a=0 then x.1.1 else if a=1 then x.1.2.1 else
    if a=2 then x.1.2.2 else k-total x.1


theorem nativeMass_value {k : ℕ} (x : NativeOccupation k) (a : Fin 4) :
    nativeMass x a=(nativeOccupationValue x).val.count a := by
  fin_cases a <;> simp [nativeMass,nativeOccupationValue]


def nativeSelected {k : ℕ} (x : NativeOccupation k) : Finset (Fin 4) :=
  Finset.univ.filter (fun a => 0<nativeMass x a)


theorem nativeSelected_mem {k : ℕ} (x : NativeOccupation k) (a : Fin 4) :
    a∈nativeSelected x ↔ a∈nativeOccupationValue x := by
  simp only [nativeSelected,Finset.mem_filter,Finset.mem_univ,true_and,nativeMass_value,
    Multiset.count_pos]
  rfl


theorem nativeSelected_eq {k : ℕ} (x : NativeOccupation k) :
    nativeSelected x=(nativeOccupationValue x).val.toFinset := by
  ext a
  rw [nativeSelected_mem,Multiset.mem_toFinset]
  rfl

/-- Explicit instance: its runtime list is formed from four native integer
positivity checks. The subtype membership proofs are erased. -/
@[instance_reducible] def nativeOccupiedFintype {k : ℕ} (x : NativeOccupation k) :
    Fintype {a : Fin 4 // a∈nativeOccupationValue x} where
  elems := (nativeSelected x).attach.map
    (⟨fun a : nativeSelected x => ⟨a.1,(nativeSelected_mem x a.1).mp a.2⟩,
      fun a b h => Subtype.ext (congrArg
        (fun c : {a : Fin 4 // a∈nativeOccupationValue x} => c.1) h)⟩ :
        (nativeSelected x) ↪ {a : Fin 4 // a∈nativeOccupationValue x})
  complete := by
    intro a
    apply Finset.mem_map.mpr
    refine ⟨⟨a.1,(nativeSelected_mem x a.1).mpr a.2⟩,Finset.mem_attach _ _,?_⟩
    rfl


def nativeOccupiedPivot {k : ℕ} (x : NativeOccupation (k+1)) :
    {a : Fin 4 // a∈nativeOccupationValue x} :=
  ⟨(nativeSelected x).min' (by
    obtain ⟨a,ha⟩:=Sym.exists_mem (nativeOccupationValue x)
    exact ⟨a,(nativeSelected_mem x a).mpr ha⟩),
    (nativeSelected_mem x _).mp (Finset.min'_mem _ _)⟩


theorem nativeOccupiedPivot_eq {k : ℕ} (x : NativeOccupation (k+1)) :
    nativeOccupiedPivot x=occupiedPivot (nativeOccupationValue x) := by
  apply Subtype.ext
  simp only [nativeOccupiedPivot,occupiedPivot,nativeSelected_eq]


def nativeOccupationTable (k : ℕ) : List (NativeOccupation k) :=
  (triplesBuild k).items.attach.map (fun t => ⟨t.1,by
    apply mem_triples.mp
    simpa only [triplesBuild_items] using t.2⟩)


theorem nativeOccupationTable_values (k : ℕ) :
    (nativeOccupationTable k).map nativeOccupationValue=occupations k := by
  have hc : ∀ t∈(triplesBuild k).items,total t≤k := by
    intro t ht
    apply mem_triples.mp
    rwa [triplesBuild_items] at ht
  simp only [nativeOccupationTable,nativeOccupationValue,List.map_map,Function.comp_def]
  change occupationList k (triplesBuild k).items hc=occupations k
  exact occupationList_congr k (triplesBuild_items k) hc (fun _ ht => mem_triples.mp ht)

end EffectiveEncoding
