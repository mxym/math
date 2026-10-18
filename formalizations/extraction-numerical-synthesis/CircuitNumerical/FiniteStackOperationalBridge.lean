import CircuitNumerical.FiniteStackReverseMap

namespace CircuitRecursion.ListAssemblyMachine

open Turing

/-- Lifting a partial transition preserves an already terminal option. -/
theorem lifted_iterate_none {σ : Type*} (f : σ → Option σ) (n : ℕ) :
    (fun x : Option σ => x.bind f)^[n] none=none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply'];simp only [ih,Option.bind_none]

/-- This is a semantic bridge from actual iterated transitions, not a cost
annotation supplied independently of the machine execution. -/
theorem lifted_iterate_some_reaches {σ : Type*} (f : σ → Option σ) (n : ℕ)
    (a b : σ) (h : (fun x : Option σ => x.bind f)^[n] (some a)=some b) :
    StateTransition.Reaches f a b := by
  induction n generalizing a with
  | zero =>
    change some a=some b at h
    cases Option.some.inj h
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (fun x : Option σ => x.bind f)^[n] (f a)=some b at h
    cases he : f a with
    | none =>
      rw [he,lifted_iterate_none] at h
      contradiction
    | some a' =>
      rw [he] at h
      exact Relation.ReflTransGen.head he (ih a' h)

theorem evalsTo_reaches {σ : Type*} {f : σ → Option σ} {a b : σ}
    (h : StateTransition.EvalsTo f a (some b)) : StateTransition.Reaches f a b :=
  lifted_iterate_some_reaches f h.steps a b h.evals_in_steps

theorem evalsTo_terminal_mem_eval {σ : Type*} {f : σ → Option σ} {a b : σ}
    (h : StateTransition.EvalsTo f a (some b)) (hb : f b=none) : b∈StateTransition.eval f a :=
  StateTransition.mem_eval.mpr ⟨evalsTo_reaches h,hb⟩

theorem append_mem_eval {α : Type*} [Inhabited α] (as bs : List α) :
    configuration none none [] (as++bs) []∈StateTransition.eval (TM2.step (program α))
      (configuration (.some .move) none as bs []) :=
  evalsTo_terminal_mem_eval (appendRun as bs).toEvalsTo (append_terminal as bs)

theorem reverse_mem_eval {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    configuration none none [] (as.reverse.map f++bs) ws∈StateTransition.eval (TM2.step (reverseProgram α f))
      (configuration (.some .move) none as bs ws) :=
  evalsTo_terminal_mem_eval (reverseRun f as bs ws).toEvalsTo (reverse_terminal f as bs ws)

theorem stack_card : Fintype.card Stack=3 := by decide
theorem label_card : Fintype.card Label=2 := by decide

theorem finite_local_memory_card (α : Type*) [Fintype α] :
    Fintype.card (Option α)=Fintype.card α+1 := Fintype.card_option

theorem finite_running_control_card (α : Type*) [Fintype α] :
    Fintype.card (Label×Option α)=2*(Fintype.card α+1) := by
  rw [Fintype.card_prod,label_card,Fintype.card_option]

/-- Static maximum statement depth. Counting official TM2 transitions does
not hide an unbounded program inside one label: these two programs have
at most four statement constructors on any executed branch. -/
def statementDepth {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => statementDepth q+1
  | .branch _ q r => max (statementDepth q) (statementDepth r)+1
  | .goto _ | .halt => 1

theorem program_statementDepth (α : Type*) [Inhabited α] (q : Label) :
    statementDepth (program α q)=4 := by
  cases q <;> rfl

theorem reverseProgram_statementDepth (α : Type*) [Inhabited α] (f : α → α) (q : Label) :
    statementDepth (reverseProgram α f q)≤4 := by
  cases q <;> simp only [reverseProgram,statementDepth] <;> omega

/-- The fixed Bool alphabet gives a concrete finite stack machine with six
non-halting control/local-memory combinations. -/
theorem bool_running_control_card : Fintype.card (Label×Option Bool)=6 := by decide

/-- Output-label alphabets are finite. This does not claim a uniform
constant-time implementation for arbitrary external inverse providers. The
reverse machine contains the fixed finite inverse table as part of its
transition function. -/
theorem instruction_running_control_card (m : ℕ) :
    Fintype.card (Label×Option (Fin m))=2*(m+1) := by
  rw [finite_running_control_card,Fintype.card_fin]

end CircuitRecursion.ListAssemblyMachine
