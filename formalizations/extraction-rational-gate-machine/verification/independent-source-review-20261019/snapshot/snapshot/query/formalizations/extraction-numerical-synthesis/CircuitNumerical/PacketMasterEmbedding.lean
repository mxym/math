import CircuitNumerical.PacketMasterClone

namespace CircuitRecursion.PacketMasterMachine

open Turing PacketFraming

/-- All original reader stacks are physically distinct from master. -/
def extendStacks (S : ListAssemblyMachine.Stack → List Symbol) (m : List Symbol) : Stack → List Symbol
  | .inl k => S k
  | .inr _ => m

def liftConfiguration {Λ Δ : Type*} (embed : Λ → Δ)
    (c : PacketRecordMachine.Configuration Λ) (m : List Symbol) : Configuration Δ :=
  ⟨c.l.map embed,c.var,extendStacks c.stk m⟩

/-- Syntactic finite stack/label embedding. Master is absent from every
compiled instruction, including in nested branches. Halt remains halt. -/
def compile {Λ Δ : Type*} (embed : Λ → Δ) :
    TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol) →
      TM2.Stmt (fun _ : Stack => Symbol) Δ (Option Symbol)
  | .push k f q => .push (.inl k) f (compile embed q)
  | .peek k f q => .peek (.inl k) f (compile embed q)
  | .pop k f q => .pop (.inl k) f (compile embed q)
  | .load f q => .load f (compile embed q)
  | .branch f q r => .branch f (compile embed q) (compile embed r)
  | .goto f => .goto (fun v => embed (f v))
  | .halt => .halt

theorem extendStacks_read (S : ListAssemblyMachine.Stack → List Symbol) (m : List Symbol)
    (k : ListAssemblyMachine.Stack) : extendStacks S m (.inl k)=S k := rfl

theorem extendStacks_update (S : ListAssemblyMachine.Stack → List Symbol) (m : List Symbol)
    (k : ListAssemblyMachine.Stack) (xs : List Symbol) :
    extendStacks (Function.update S k xs) m=Function.update (extendStacks S m) (.inl k) xs := by
  funext j
  cases j with
  | inl j => by_cases hj : j=k <;> simp [extendStacks,Function.update,hj]
  | inr j => simp [extendStacks,Function.update]

theorem compile_stepAux {Λ Δ : Type*} (embed : Λ → Δ)
    (q : TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol))
    (v : Option Symbol) (S : ListAssemblyMachine.Stack → List Symbol) (m : List Symbol) :
    TM2.stepAux (compile embed q) v (extendStacks S m)=liftConfiguration embed (TM2.stepAux q v S) m := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [compile,TM2.stepAux,extendStacks_read]
    rw [←extendStacks_update]
    exact ih v _
  | peek k f q ih =>
    simp only [compile,TM2.stepAux,extendStacks_read]
    exact ih _ S
  | pop k f q ih =>
    simp only [compile,TM2.stepAux,extendStacks_read]
    rw [←extendStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [compile,TM2.stepAux]
    exact ih _ S
  | branch f q r iq ir =>
    simp only [compile,TM2.stepAux]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq v S | exact ir v S
  | goto f => rfl
  | halt => rfl

/-- Literal code embedding suffices to lift every actual source transition;
master preservation is proved, not supplied as a trace/cost certificate. -/
theorem compiled_step {Λ Δ : Type*} (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol))
    (N : Δ → TM2.Stmt (fun _ : Stack => Symbol) Δ (Option Symbol))
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (m : List Symbol)
    (c : PacketRecordMachine.Configuration Λ) :
    TM2.step N (liftConfiguration embed c m)=(TM2.step M c).map (fun d => liftConfiguration embed d m) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [liftConfiguration,TM2.step,Option.map_some,hcode,compile_stepAux]

def compiledRun {Λ Δ : Type*} (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol))
    (N : Δ → TM2.Stmt (fun _ : Stack => Symbol) Δ (Option Symbol))
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (m : List Symbol)
    {c d : PacketRecordMachine.Configuration Λ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step N) (liftConfiguration embed c m)
      (some (liftConfiguration embed d m)) t :=
  TM2ConfigurationMap.mapRun _ _ (fun x => liftConfiguration embed x m) (compiled_step embed M N hcode m) run

theorem compiledRun_steps {Λ Δ : Type*} (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol))
    (N : Δ → TM2.Stmt (fun _ : Stack => Symbol) Δ (Option Symbol))
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (m : List Symbol)
    {c d : PacketRecordMachine.Configuration Λ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (compiledRun embed M N hcode m run).steps=run.steps := rfl

theorem lift_recordConfiguration {Λ Δ : Type*} (embed : Λ → Δ) (l : Option Λ) (v : Option Symbol)
    (i s c m : List Symbol) :
    liftConfiguration embed (PacketRecordMachine.configuration l v i s c) m=
      configuration (l.map embed) v i s c m := by
  change TM2.Cfg.mk (l.map embed) v (extendStacks (ListAssemblyMachine.stackData i s c) m)=
    TM2.Cfg.mk (l.map embed) v (stackData i s c m)
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

theorem lift_master {Λ Δ : Type*} (embed : Λ → Δ) (c : PacketRecordMachine.Configuration Λ)
    (m : List Symbol) : (liftConfiguration embed c m).stk (.inr ())=m := rfl

theorem lift_working {Λ Δ : Type*} (embed : Λ → Δ) (c : PacketRecordMachine.Configuration Λ)
    (m : List Symbol) (k : ListAssemblyMachine.Stack) : (liftConfiguration embed c m).stk (.inl k)=c.stk k := rfl

theorem compile_statementDepth {Λ Δ : Type*} (embed : Λ → Δ)
    (q : TM2.Stmt (fun _ : ListAssemblyMachine.Stack => Symbol) Λ (Option Symbol)) :
    ListAssemblyMachine.statementDepth (compile embed q)=ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
    simp only [compile,ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [compile,ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.PacketMasterMachine
