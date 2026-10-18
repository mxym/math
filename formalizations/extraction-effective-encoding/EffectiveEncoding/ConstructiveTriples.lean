import EffectiveEncoding.RankByTriples

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Explicit cons/append source construction. Fees are structural events;
Nat arithmetic, comparisons and counter arithmetic are charged separately. -/
structure ListBuild (α : Type*) where
  items : List α
  steps : ℕ


def ListBuild.empty {α : Type*} : ListBuild α := ⟨[],1⟩
def ListBuild.emit {α : Type*} (x : α) (r : ListBuild α) : ListBuild α := ⟨x::r.items,r.steps+1⟩
def ListBuild.append {α : Type*} (a b : ListBuild α) : ListBuild α :=
  ⟨a.items++b.items,a.steps+b.steps+a.items.length+1⟩

/-- A deliberately simple quadratic range builder, with an explicit copy
fee for append. Its erased list has exactly List.range's ordering. -/
def rangeBuild : ℕ → ListBuild ℕ
  | 0 => ListBuild.empty
  | n+1 => (rangeBuild n).append (ListBuild.emit n ListBuild.empty)


theorem rangeBuild_items (n : ℕ) : (rangeBuild n).items=List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rangeBuild,ListBuild.append,ListBuild.emit,ListBuild.empty,ih,List.range_succ]


theorem rangeBuild_steps (n : ℕ) : (rangeBuild n).steps≤3*(n+1)^2 := by
  induction n with
  | zero => simp [rangeBuild,ListBuild.empty]
  | succ n ih =>
    simp only [rangeBuild,ListBuild.append,ListBuild.emit,ListBuild.empty,rangeBuild_items,List.length_range]
    nlinarith

/-- A row constructs one ordered pair and one list cons per entry. -/
def productRowBuild {α β : Type*} (x : α) : List β → ListBuild (α×β)
  | [] => ListBuild.empty
  | y::ys => let tail:=productRowBuild x ys;⟨(x,y)::tail.items,tail.steps+2⟩


theorem productRowBuild_items {α β : Type*} (x : α) (ys : List β) :
    (productRowBuild x ys).items=ys.map (fun y => (x,y)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [productRowBuild,List.map_cons,ih]


theorem productRowBuild_steps {α β : Type*} (x : α) (ys : List β) :
    (productRowBuild x ys).steps=2*ys.length+1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [productRowBuild,List.length_cons,ih];omega


def productBuild {α β : Type*} : List α → List β → ListBuild (α×β)
  | [],_ => ListBuild.empty
  | x::xs,ys => (productRowBuild x ys).append (productBuild xs ys)


theorem productBuild_items {α β : Type*} (xs : List α) (ys : List β) :
    (productBuild xs ys).items=xs×ˢys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productBuild,ListBuild.append,productRowBuild_items,ih]


theorem productBuild_steps {α β : Type*} (xs : List α) (ys : List β) :
    (productBuild xs ys).steps=xs.length*(3*ys.length+2)+1 := by
  induction xs with
  | nil => simp [productBuild,ListBuild.empty]
  | cons x xs ih =>
    simp only [productBuild,ListBuild.append,productRowBuild_steps,productRowBuild_items,List.length_map,
      ih,List.length_cons]
    ring

structure FilterBuild (α : Type*) where
  items : List α
  steps : ℕ
  queries : ℕ

/-- One visit and one predicate request per entry; an accepted cons adds one.
The predicate's own bit operations are outside these structural fees. -/
def filterBuild {α : Type*} (p : α → Bool) : List α → FilterBuild α
  | [] => ⟨[],1,0⟩
  | x::xs =>
    let accepted:=p x
    let tail:=filterBuild p xs
    if accepted then ⟨x::tail.items,tail.steps+3,tail.queries+1⟩
    else ⟨tail.items,tail.steps+2,tail.queries+1⟩


theorem filterBuild_items {α : Type*} (p : α → Bool) (xs : List α) :
    (filterBuild p xs).items=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterBuild,List.filter_cons]
    split <;> simp_all


theorem filterBuild_steps {α : Type*} (p : α → Bool) (xs : List α) :
    (filterBuild p xs).steps≤3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filterBuild,List.length_cons];split <;> dsimp only <;> omega


theorem filterBuild_queries {α : Type*} (p : α → Bool) (xs : List α) :
    (filterBuild p xs).queries=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filterBuild,List.length_cons];split <;> dsimp only <;> omega

/-- Materialize one range and reuse it in both actual ordered products.
The output is the exact original triples list, including filter order. -/
def triplesBuild (k : ℕ) : FilterBuild Triple :=
  let r:=rangeBuild (k+1)
  let inner:=productBuild r.items r.items
  let outer:=productBuild r.items inner.items
  let filtered:=filterBuild (fun t => decide (total t≤k)) outer.items
  ⟨filtered.items,r.steps+inner.steps+outer.steps+filtered.steps,filtered.queries⟩


theorem triplesBuild_items (k : ℕ) : (triplesBuild k).items=triples k := by
  simp only [triplesBuild,rangeBuild_items,productBuild_items,filterBuild_items,triples]


theorem triplesBuild_queries (k : ℕ) : (triplesBuild k).queries=(k+1)^3 := by
  simp [triplesBuild,filterBuild_queries,rangeBuild_items,productBuild_items,List.length_product,pow_succ,Nat.mul_assoc]


theorem triplesBuild_steps (k : ℕ) : (triplesBuild k).steps≤28*(k+1)^3 := by
  let n:=k+1
  have hn : 1≤n := by omega
  have hr:=rangeBuild_steps n
  have hf:=filterBuild_steps (fun t => decide (total t≤k))
    (productBuild (rangeBuild n).items (productBuild (rangeBuild n).items (rangeBuild n).items).items).items
  simp only [productBuild_items,rangeBuild_items,List.length_product,List.length_range] at hf
  have hp2 : n^2≤n^3 := Nat.pow_le_pow_right hn (by decide)
  have hp1 : n≤n^3 := by simpa using Nat.pow_le_pow_right hn (by decide : 1≤3)
  have hp0 : 1≤n^3 := Nat.one_le_pow _ _ (by omega)
  change (rangeBuild n).steps+(productBuild (rangeBuild n).items (rangeBuild n).items).steps+
    (productBuild (rangeBuild n).items (productBuild (rangeBuild n).items (rangeBuild n).items).items).steps+_
      ≤28*n^3
  simp only [productBuild_steps,rangeBuild_items,List.length_range,productBuild_items,List.length_product]
  nlinarith

end EffectiveEncoding
