import CircuitNumerical.PacketMasterSemantics

namespace CircuitRecursion.TM2ExtraStack

open Turing

/-- One additional physical stack, untouched by the embedded program. -/
def extendStacks {K A : Type*} (S : K → List A) (extra : List A) : K⊕Unit → List A
  | .inl k => S k
  | .inr _ => extra

def liftConfiguration {K A Λ Δ σ : Type*} (embed : Λ → Δ)
    (c : TM2.Cfg (fun _ : K => A) Λ σ) (extra : List A) : TM2.Cfg (fun _ : K⊕Unit => A) Δ σ :=
  ⟨c.l.map embed,c.var,extendStacks c.stk extra⟩

def compile {K A Λ Δ σ : Type*} (embed : Λ → Δ) :
    TM2.Stmt (fun _ : K => A) Λ σ → TM2.Stmt (fun _ : K⊕Unit => A) Δ σ
  | .push k f q => .push (.inl k) f (compile embed q)
  | .peek k f q => .peek (.inl k) f (compile embed q)
  | .pop k f q => .pop (.inl k) f (compile embed q)
  | .load f q => .load f (compile embed q)
  | .branch f q r => .branch f (compile embed q) (compile embed r)
  | .goto f => .goto (fun v => embed (f v))
  | .halt => .halt

theorem extendStacks_read {K A : Type*} (S : K → List A) (extra : List A) (k : K) :
    extendStacks S extra (.inl k)=S k := rfl

theorem extendStacks_update {K A : Type*} [DecidableEq K]
    (S : K → List A) (extra : List A) (k : K) (xs : List A) :
    extendStacks (Function.update S k xs) extra=Function.update (extendStacks S extra) (.inl k) xs := by
  funext j
  cases j with
  | inl j => by_cases hj : j=k <;> simp [extendStacks,Function.update,hj]
  | inr j => simp [extendStacks,Function.update]

theorem compile_stepAux {K A Λ Δ σ : Type*} [DecidableEq K] (embed : Λ → Δ)
    (q : TM2.Stmt (fun _ : K => A) Λ σ) (v : σ) (S : K → List A) (extra : List A) :
    TM2.stepAux (compile embed q) v (extendStacks S extra)=
      liftConfiguration embed (TM2.stepAux q v S) extra := by
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

theorem compiled_step {K A Λ Δ σ : Type*} [DecidableEq K] (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (N : Δ → TM2.Stmt (fun _ : K⊕Unit => A) Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (extra : List A)
    (c : TM2.Cfg (fun _ : K => A) Λ σ) :
    TM2.step N (liftConfiguration embed c extra)=
      (TM2.step M c).map (fun d => liftConfiguration embed d extra) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [liftConfiguration,TM2.step,Option.map_some,hcode,compile_stepAux]

def compiledRun {K A Λ Δ σ : Type*} [DecidableEq K] (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (N : Δ → TM2.Stmt (fun _ : K⊕Unit => A) Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (extra : List A)
    {c d : TM2.Cfg (fun _ : K => A) Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step N) (liftConfiguration embed c extra)
      (some (liftConfiguration embed d extra)) t :=
  TM2ConfigurationMap.mapRun _ _ (fun x => liftConfiguration embed x extra)
    (compiled_step embed M N hcode extra) run

theorem compiledRun_steps {K A Λ Δ σ : Type*} [DecidableEq K] (embed : Λ → Δ)
    (M : Λ → TM2.Stmt (fun _ : K => A) Λ σ)
    (N : Δ → TM2.Stmt (fun _ : K⊕Unit => A) Δ σ)
    (hcode : ∀ l,N (embed l)=compile embed (M l)) (extra : List A)
    {c d : TM2.Cfg (fun _ : K => A) Λ σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (compiledRun embed M N hcode extra run).steps=run.steps := rfl

theorem compile_statementDepth {K A Λ Δ σ : Type*} (embed : Λ → Δ)
    (q : TM2.Stmt (fun _ : K => A) Λ σ) :
    ListAssemblyMachine.statementDepth (compile embed q)=ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
    simp only [compile,ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [compile,ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.TM2ExtraStack
