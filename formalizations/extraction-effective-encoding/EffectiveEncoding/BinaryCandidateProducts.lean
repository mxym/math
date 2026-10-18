import EffectiveEncoding.BinaryTriplePredicate

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Explicit tuple/list construction and append traces. Only these local
structural actions are represented; annotation arithmetic is not included. -/
inductive CandidateProductTrace where
  | done
  | emit : CandidateProductTrace → CandidateProductTrace
  | join : CandidateProductTrace → CandidateProductTrace → ListAssemblyTrace → CandidateProductTrace


def CandidateProductTrace.actions : CandidateProductTrace → ℕ
  | .done => 1
  | .emit tail => tail.actions+6
  | .join row tail copied => row.actions+tail.actions+copied.actions+2

structure CandidateProductResult (α : Type*) where
  items : List α
  trace : CandidateProductTrace


def candidateProductRowProgram {α β : Type*} (x : α) : List β → CandidateProductResult (α×β)
  | [] => ⟨[],.done⟩
  | y::ys =>
    let tail:=candidateProductRowProgram x ys
    ⟨(x,y)::tail.items,.emit tail.trace⟩


theorem candidateProductRowProgram_items {α β : Type*} (x : α) (ys : List β) :
    (candidateProductRowProgram x ys).items=ys.map (fun y => (x,y)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [candidateProductRowProgram,List.map_cons,ih]


theorem candidateProductRowProgram_actions {α β : Type*} (x : α) (ys : List β) :
    (candidateProductRowProgram x ys).trace.actions=6*ys.length+1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [candidateProductRowProgram,CandidateProductTrace.actions,List.length_cons,ih];omega

/-- Every row and tail are computed once; output concatenation is an actual
listAppendProgram call with its returned copy trace, not a fee inferred only
from the product's final output length. -/
def candidateProductProgram {α β : Type*} : List α → List β → CandidateProductResult (α×β)
  | [],_ => ⟨[],.done⟩
  | x::xs,ys =>
    let row:=candidateProductRowProgram x ys
    let tail:=candidateProductProgram xs ys
    let output:=listAppendProgram row.items tail.items
    ⟨output.value,.join row.trace tail.trace output.trace⟩


theorem candidateProductProgram_items {α β : Type*} (xs : List α) (ys : List β) :
    (candidateProductProgram xs ys).items=xs×ˢys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [candidateProductProgram,listAppendProgram_value,candidateProductRowProgram_items,ih]


theorem candidateProductProgram_actions {α β : Type*} (xs : List α) (ys : List β) :
    (candidateProductProgram xs ys).trace.actions=xs.length*(10*ys.length+4)+1 := by
  induction xs with
  | nil => simp [candidateProductProgram,CandidateProductTrace.actions]
  | cons x xs ih =>
    simp only [candidateProductProgram,CandidateProductTrace.actions,candidateProductRowProgram_actions,
      listAppendProgram_actions,candidateProductRowProgram_items,List.length_map,ih,List.length_cons]
    ring


theorem candidateProduct_map {α β γ δ : Type*} (f : α → γ) (g : β → δ) (xs : List α) (ys : List β) :
    (xs.map f)×ˢ(ys.map g)=(xs×ˢys).map (fun t => (f t.1,g t.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,List.map_map,Function.comp_def]

end EffectiveEncoding
