import CircuitNumerical.TM2Subroutine

namespace CircuitRecursion.TM2Subroutine

open Turing

/-- An actual compiled enclosing program. Left labels execute the local
subroutine, and right labels execute caller code. The local halt becomes a
jump to a right return label. There is no code-agreement hypothesis. -/
def splice {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ)
    (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ) : Λ⊕Δ → TM2.Stmt Γ (Λ⊕Δ) σ
  | .inl l => redirect Sum.inl (fun v => Sum.inr (ret v)) (M l)
  | .inr q => outer q

@[simp] theorem splice_local {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ) (l : Λ) :
    splice M ret outer (.inl l)=redirect Sum.inl (fun v => Sum.inr (ret v)) (M l) := rfl

@[simp] theorem splice_outer {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ) (q : Δ) :
    splice M ret outer (.inr q)=outer q := rfl

/-- Insert an internally proved local machine execution into this compiled
program. The caller supplies its outer code, not a desired execution or
budget certificate. The original official transition count is preserved. -/
def spliceRun {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ)
    {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step (splice M ret outer))
      (liftConfiguration Sum.inl (fun v => Sum.inr (ret v)) c)
      (some (liftConfiguration Sum.inl (fun v => Sum.inr (ret v)) d)) t :=
  redirectedRun Sum.inl (fun v => Sum.inr (ret v)) M (splice M ret outer) (fun _ => rfl) run

theorem spliceRun_steps {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ)
    {c d : TM2.Cfg Γ Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (spliceRun M ret outer run).steps=run.steps := rfl

theorem splice_local_statementDepth {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ) (l : Λ) :
    ListAssemblyMachine.statementDepth (splice M ret outer (.inl l))=
      ListAssemblyMachine.statementDepth (M l) := redirect_statementDepth _ _ _

/-- A direct counter call for a caller loop/return controller. All counter
correctness and transition bounds are already proved internally. -/
def counterCall {Δ : Type*} (ret : Option Bool → Δ)
    (outer : Δ → TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Bool)
      (BinaryCounterMachine.Label⊕Δ) (Option Bool))
    (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (splice BinaryCounterMachine.program ret outer))
      (liftConfiguration Sum.inl (fun v => Sum.inr (ret v))
        (BinaryCounterMachine.configuration (.some .borrow) none as [] ws))
      (some (liftConfiguration Sum.inl (fun v => Sum.inr (ret v)) (BinaryCounterMachine.terminal as ws)))
      (2*as.length+2) :=
  spliceRun BinaryCounterMachine.program ret outer (BinaryCounterMachine.counterRun as h ws)

theorem counterCall_steps {Δ : Type*} (ret : Option Bool → Δ)
    (outer : Δ → TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Bool)
      (BinaryCounterMachine.Label⊕Δ) (Option Bool))
    (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    (counterCall ret outer as h ws).steps=BinaryCounterMachine.borrowTime as 0 := rfl

theorem supportsStmt_univ {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [Fintype Λ]
    (q : TM2.Stmt Γ Λ σ) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => exact ih
  | branch f q r iq ir => exact ⟨iq,ir⟩
  | goto f => exact fun _ => Finset.mem_univ _
  | halt => trivial

theorem splice_supports {K : Type*} {Γ : K → Type*} {Λ Δ σ : Type*}
    [Fintype Λ] [Fintype Δ] [Inhabited (Λ⊕Δ)]
    (M : Λ → TM2.Stmt Γ Λ σ) (ret : σ → Δ) (outer : Δ → TM2.Stmt Γ (Λ⊕Δ) σ) :
    TM2.Supports (splice M ret outer) Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => supportsStmt_univ _⟩

theorem splice_running_control_card (Λ Δ σ : Type*) [Fintype Λ] [Fintype Δ] [Fintype σ] :
    Fintype.card ((Λ⊕Δ)×σ)=(Fintype.card Λ+Fintype.card Δ)*Fintype.card σ := by
  rw [Fintype.card_prod,Fintype.card_sum]

end CircuitRecursion.TM2Subroutine
