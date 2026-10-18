import CircuitNumerical.BinaryIndexedLookup

namespace CircuitRecursion.TM2Subroutine

open Turing

/-- Compile local labels into enclosing labels and replace halt by a jump
to the caller's return label. This is actual TM2 syntax, not a fee wrapper. -/
def redirect {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Δ σ
  | .push k f q => .push k f (redirect embed ret q)
  | .peek k f q => .peek k f (redirect embed ret q)
  | .pop k f q => .pop k f (redirect embed ret q)
  | .load f q => .load f (redirect embed ret q)
  | .branch f q r => .branch f (redirect embed ret q) (redirect embed ret r)
  | .goto f => .goto (fun v => embed (f v))
  | .halt => .goto ret

/-- The source halting control becomes the caller's active return control.
The local memory and every stack remain exactly the source values. -/
def liftConfiguration {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Δ σ :=
  ⟨some (match c.l with | none => ret c.var | some l => embed l),c.var,c.stk⟩

theorem redirect_stepAux {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (redirect embed ret q) v S=liftConfiguration embed ret (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
    simp only [redirect,TM2.stepAux]
    exact ih _ _
  | branch f q r iq ir =>
    simp only [redirect,TM2.stepAux]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq _ _ | exact ir _ _
  | goto f => rfl
  | halt => rfl

theorem redirect_step {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=redirect embed ret (M l)) (c : TM2.Cfg Γ Λ σ) (hc : c.l≠none) :
    TM2.step N (liftConfiguration embed ret c)=(TM2.step M c).map (liftConfiguration embed ret) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l => simp only [liftConfiguration,TM2.step,hcode,redirect_stepAux,Option.map_some]

def advance {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) : Option (TM2.Cfg Γ Λ σ) → Option (TM2.Cfg Γ Λ σ) :=
  fun c => c.bind (TM2.step M)

theorem active_of_step_some {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (c d : TM2.Cfg Γ Λ σ) (h : TM2.step M c=some d) : c.l≠none := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => cases h
  | some l => exact Option.some_ne_none l

/-- A bounded source prefix ending in a configuration cannot have already
stepped beyond halt: lifted none is absorbing. Thus redirect preserves the
actual complete prefix, including its last return transition, with no extra
steps and without a caller-provided intermediate-state invariant. -/
theorem redirect_iterate {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=redirect embed ret (M l)) (n : ℕ) (c d : TM2.Cfg Γ Λ σ)
    (h : (advance M)^[n] (some c)=some d) :
    (advance N)^[n] (some (liftConfiguration embed ret c))=some (liftConfiguration embed ret d) := by
  induction n generalizing c with
  | zero =>
    change some c=some d at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (advance M)^[n] (TM2.step M c)=some d at h
    change (advance N)^[n] (TM2.step N (liftConfiguration embed ret c))=_
    cases hs : TM2.step M c with
    | none =>
      rw [hs] at h
      change (fun x => x.bind (TM2.step M))^[n] none=some d at h
      rw [ListAssemblyMachine.lifted_iterate_none] at h
      contradiction
    | some c' =>
      rw [hs] at h
      rw [redirect_step embed ret M N hcode c (active_of_step_some M c c' hs),hs,Option.map_some]
      exact ih c' h

/-- Actual subroutine insertion preserves the proved official transition
count. hcode only identifies the compiled program text at embedded labels;
it is not a premise asserting the desired execution or polynomial budget. -/
def redirectedRun {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=redirect embed ret (M l)) {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step N) (liftConfiguration embed ret c)
      (some (liftConfiguration embed ret d)) t :=
  ⟨⟨run.steps,redirect_iterate embed ret M N hcode run.steps c d run.evals_in_steps⟩,run.steps_le_m⟩

theorem redirectedRun_steps {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (M : Λ → TM2.Stmt Γ Λ σ) (N : Δ → TM2.Stmt Γ Δ σ)
    (hcode : ∀ l,N (embed l)=redirect embed ret (M l)) {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (redirectedRun embed ret M N hcode run).steps=run.steps := rfl

theorem redirect_statementDepth {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (q : TM2.Stmt Γ Λ σ) :
    ListAssemblyMachine.statementDepth (redirect embed ret q)=ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
    simp only [redirect,ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [redirect,ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

theorem liftConfiguration_return {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (v : σ) (S : ∀ k,List (Γ k)) :
    (liftConfiguration embed ret (TM2.Cfg.mk none v S)).l=some (ret v) := rfl

theorem liftConfiguration_stacks {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (embed : Λ → Δ) (ret : σ → Δ) (c : TM2.Cfg Γ Λ σ) :
    (liftConfiguration embed ret c).stk=c.stk := rfl

end CircuitRecursion.TM2Subroutine
