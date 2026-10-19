import CircuitNumerical.PacketCounterOperational

namespace CircuitRecursion.PacketStackPermutation

open Turing ListAssemblyMachine PacketFraming

def liftStacks (p : Stack≃Stack) (S : Stack → List Symbol) : Stack → List Symbol := fun k => S (p.symm k)

def liftConfiguration {Λ : Type*} (p : Stack≃Stack)
    (c : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)) : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol) :=
  ⟨c.l,c.var,liftStacks p c.stk⟩

/-- Stack roles are compiled into fixed finite stack labels. No physical
stack shuffle or integer index computation occurs in this transformation. -/
def compile {Λ : Type*} (p : Stack≃Stack) : TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol) →
    TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol)
  | .push k f q => .push (p k) f (compile p q)
  | .peek k f q => .peek (p k) f (compile p q)
  | .pop k f q => .pop (p k) f (compile p q)
  | .load f q => .load f (compile p q)
  | .branch f q r => .branch f (compile p q) (compile p r)
  | .goto f => .goto f
  | .halt => .halt

theorem liftStacks_read (p : Stack≃Stack) (S : Stack → List Symbol) (k : Stack) :
    liftStacks p S (p k)=S k := by simp only [liftStacks,Equiv.symm_apply_apply]

theorem liftStacks_update (p : Stack≃Stack) (S : Stack → List Symbol) (k : Stack) (xs : List Symbol) :
    liftStacks p (Function.update S k xs)=Function.update (liftStacks p S) (p k) xs := by
  funext j
  by_cases hj : j=p k
  · subst j
    simp only [liftStacks,Equiv.symm_apply_apply,Function.update_self]
  · have hj' : p.symm j≠k := by
      intro he
      apply hj
      simpa only [Equiv.apply_symm_apply] using congrArg p he
    simp only [liftStacks,Function.update_of_ne hj,Function.update_of_ne hj']

theorem compile_stepAux {Λ : Type*} (p : Stack≃Stack)
    (q : TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol)) (v : Option Symbol) (S : Stack → List Symbol) :
    TM2.stepAux (compile p q) v (liftStacks p S)=liftConfiguration p (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [compile,TM2.stepAux,liftStacks_read]
    rw [←liftStacks_update]
    exact ih v _
  | peek k f q ih =>
    simp only [compile,TM2.stepAux,liftStacks_read]
    exact ih _ S
  | pop k f q ih =>
    simp only [compile,TM2.stepAux,liftStacks_read]
    rw [←liftStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [compile,TM2.stepAux]
    exact ih _ S
  | branch f q r iq ir =>
    simp only [compile,TM2.stepAux]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq v S | exact ir v S
  | goto f => rfl
  | halt => rfl

theorem program_step {Λ : Type*} (p : Stack≃Stack)
    (M : Λ → TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol))
    (c : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)) :
    TM2.step (fun l => compile p (M l)) (liftConfiguration p c)=
      (TM2.step M c).map (liftConfiguration p) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [liftConfiguration,TM2.step,compile_stepAux,Option.map_some]

def mapRun {Λ : Type*} (p : Stack≃Stack)
    (M : Λ → TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol))
    {c d : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    StateTransition.EvalsToInTime (TM2.step (fun l => compile p (M l))) (liftConfiguration p c)
      (some (liftConfiguration p d)) t :=
  TM2ConfigurationMap.mapRun _ _ (liftConfiguration p) (program_step p M) run

theorem mapRun_steps {Λ : Type*} (p : Stack≃Stack)
    (M : Λ → TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol))
    {c d : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)} {t : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step M) c (some d) t) :
    (mapRun p M run).steps=run.steps := rfl

/-- old input->cache work, old output->left, old scratch->right. -/
def frameRoles : Stack≃Stack where
  toFun
    | .left => .work
    | .right => .left
    | .work => .right
  invFun
    | .left => .right
    | .right => .work
    | .work => .left
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

def configuration {Λ : Type*} (l : Option Λ) (v : Option Symbol) (index scratch cache : List Symbol) :
    TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol) := ⟨l,v,stackData index scratch cache⟩

theorem skip_roles (l : Option Unit) (v : Option Symbol) (input output work : List Symbol) :
    liftConfiguration frameRoles (PacketFrameMachine.skipConfiguration l v input output work)=
      configuration l v output work input := by
  change TM2.Cfg.mk l v (liftStacks frameRoles (stackData input output work))=TM2.Cfg.mk l v (stackData output work input)
  congr 1
  funext k
  cases k <;> rfl

theorem copy_roles (l : Option PacketFrameMachine.CopyLabel) (v : Option Symbol) (input output work : List Symbol) :
    liftConfiguration frameRoles (PacketFrameMachine.copyConfiguration l v input output work)=
      configuration l v output work input := by
  change TM2.Cfg.mk l v (liftStacks frameRoles (stackData input output work))=TM2.Cfg.mk l v (stackData output work input)
  congr 1
  funext k
  cases k <;> rfl

theorem compile_statementDepth {Λ : Type*} (p : Stack≃Stack)
    (q : TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol)) :
    statementDepth (compile p q)=statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => simp only [compile,statementDepth,ih]
  | branch f q r iq ir => simp only [compile,statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.PacketStackPermutation
