import RationalGateMachine.BinaryClock

namespace RationalGateMachine.StateLift

open Turing

/-- Add a finite read-only control component to every actual local statement.
No host call or extra transition is introduced. -/
def compile {K : Type*} {Γ : K → Type*} {Λ σ ρ : Type*} :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (ρ × σ)
  | .push k f q => .push k (fun v => f v.2) (compile q)
  | .peek k f q => .peek k (fun v b => (v.1,f v.2 b)) (compile q)
  | .pop k f q => .pop k (fun v b => (v.1,f v.2 b)) (compile q)
  | .load f q => .load (fun v => (v.1,f v.2)) (compile q)
  | .branch f q r => .branch (fun v => f v.2) (compile q) (compile r)
  | .goto f => .goto (fun v => f v.2)
  | .halt => .halt

def configuration {K : Type*} {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (ρ × σ) :=
  ⟨c.l,(r,c.var),c.stk⟩

theorem stepAux {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (compile q) (r,v) S=configuration r (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      simp only [compile,TM2.stepAux]
      exact ih _ _
  | branch f q s iq is =>
      simp only [compile,TM2.stepAux]
      cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;>
        first | exact iq _ _ | exact is _ _
  | goto f => rfl
  | halt => rfl

theorem step {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    TM2.step (fun l => compile (M l)) (configuration r c)=
      (TM2.step M c).map (configuration r) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [configuration,TM2.step,stepAux,Option.map_some]

theorem iterate {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ) (x : Option (TM2.Cfg Γ Λ σ)) :
    (fun y => y.bind (TM2.step (fun l => compile (M l))))^[n]
        (x.map (configuration r))=
      ((fun y => y.bind (TM2.step M))^[n] x).map (configuration r) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      have hs : (x.map (configuration r)).bind (TM2.step (fun l => compile (M l)))=
          (x.bind (TM2.step M)).map (configuration r) := by
        cases x with
        | none => rfl
        | some c => exact step r M c
      rw [hs,ih]

def run {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (M : Λ → TM2.Stmt Γ Λ σ)
    {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (h : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step (fun l => compile (M l)))
      (configuration r c) (some (configuration r d)) t :=
  ⟨⟨h.steps,by
    have he:=iterate r M h.steps (some c)
    have hr : (fun y : Option (TM2.Cfg Γ Λ σ) => y.bind (TM2.step M))^[h.steps]
        (some c)=some d := h.evals_in_steps
    rw [hr,Option.map_some] at he
    exact he⟩,h.steps_le_m⟩

theorem run_steps {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ ρ : Type*}
    (r : ρ) (M : Λ → TM2.Stmt Γ Λ σ)
    {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (h : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (run r M h).steps=h.steps := rfl

theorem statement_depth {K : Type*} {Γ : K → Type*} {Λ σ ρ : Type*}
    (q : TM2.Stmt Γ Λ σ) :
    CircuitRecursion.ListAssemblyMachine.statementDepth (compile (ρ:=ρ) q)=
      CircuitRecursion.ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      simp only [compile,CircuitRecursion.ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir =>
      simp only [compile,CircuitRecursion.ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end RationalGateMachine.StateLift
