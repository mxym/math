import RationalGateMachine.StateLift

namespace RationalGateMachine.LabelLift
open Turing

/-- Rename goto labels, preserving literal halts and every data operation. -/
def compile {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*} (embed : Λ → Δ) :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Δ σ
  | .push k f q => .push k f (compile embed q)
  | .peek k f q => .peek k f (compile embed q)
  | .pop k f q => .pop k f (compile embed q)
  | .load f q => .load f (compile embed q)
  | .branch f q r => .branch f (compile embed q) (compile embed r)
  | .goto f => .goto (fun v => embed (f v))
  | .halt => .halt

def configuration {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Δ σ :=
  ⟨c.l.map embed,c.var,c.stk⟩

theorem stepAux {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (compile embed q) v S=configuration embed (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      simp only [compile,TM2.stepAux];exact ih _ _
  | branch f q r iq ir =>
      simp only [compile,TM2.stepAux]
      cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;>
        first | exact iq _ _ | exact ir _ _
  | goto f => rfl
  | halt => rfl

theorem step {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (c : TM2.Cfg Γ Λ σ) :
    TM2.step N (configuration embed c)=(TM2.step M c).map (configuration embed) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [configuration,TM2.step,hcode,stepAux,Option.map_some]

theorem iterate {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (n : ℕ) (x : Option (TM2.Cfg Γ Λ σ)) :
    (fun y => y.bind (TM2.step N))^[n] (x.map (configuration embed))=
      ((fun y => y.bind (TM2.step M))^[n] x).map (configuration embed) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      have hs : (x.map (configuration embed)).bind (TM2.step N)=
          (x.bind (TM2.step M)).map (configuration embed) := by
        cases x with
        | none => rfl
        | some c => exact step embed M N hcode c
      rw [hs,ih]

def run {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l))
    {c d : TM2.Cfg Γ Λ σ} {t : ℕ} (h : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step N) (configuration embed c)
      (some (configuration embed d)) t :=
  ⟨⟨h.steps,by
    have he:=iterate embed M N hcode h.steps (some c)
    have hr : (fun y : Option (TM2.Cfg Γ Λ σ) => y.bind (TM2.step M))^[h.steps]
        (some c)=some d := h.evals_in_steps
    rw [hr,Option.map_some] at he
    exact he⟩,h.steps_le_m⟩

theorem statement_depth {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (q : TM2.Stmt Γ Λ σ) :
    CircuitRecursion.ListAssemblyMachine.statementDepth (compile embed q)=
      CircuitRecursion.ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      simp only [compile,CircuitRecursion.ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [compile,CircuitRecursion.ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end RationalGateMachine.LabelLift
