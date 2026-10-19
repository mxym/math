import CircuitNumerical.PacketFieldRoundtrip

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

inductive WordStack where
  | scratch
  | numerator : PacketFieldMachine.Coordinate → WordStack
  | denominator
  deriving DecidableEq
instance : Fintype WordStack := ⟨{.scratch,.numerator .n0,.numerator .n1,.numerator .n2,.numerator .n3,.denominator},by
  intro k;cases k with
  | scratch | denominator => simp
  | numerator q => cases q <;> simp⟩
instance : Inhabited WordStack := ⟨.scratch⟩

abbrev Stack := PacketQueryMachine.Stack ⊕ WordStack
abbrev Alphabet : Stack → Type
  | .inl _ => Symbol
  | .inr _ => Bool
abbrev Memory := PacketFieldMachine.Memory

def readerStacks (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) : ∀ k,List (Alphabet k)
  | .inl k => S k
  | .inr k => words k

def readerConfiguration (c : PacketQueryMachine.Configuration PacketQueryMachine.Label) (words : WordStack → List Bool) :
    TM2.Cfg Alphabet PacketQueryMachine.Label Memory :=
  ⟨c.l,(PacketFieldMachine.emptyFlags,c.var,false),readerStacks c.stk words⟩

/-- Concrete memory/stack syntax compilation. Only the current Symbol is
used by reader callbacks; four sign flags and status remain fixed finite data. -/
def compileReader : TM2.Stmt (fun _ : PacketQueryMachine.Stack => Symbol) PacketQueryMachine.Label (Option Symbol) →
    TM2.Stmt Alphabet PacketQueryMachine.Label Memory
  | .push k f q => .push (.inl k) (fun m => f m.2.1) (compileReader q)
  | .peek k f q => .peek (.inl k) (fun m x => PacketFieldMachine.withCell m (f m.2.1 x)) (compileReader q)
  | .pop k f q => .pop (.inl k) (fun m x => PacketFieldMachine.withCell m (f m.2.1 x)) (compileReader q)
  | .load f q => .load (fun m => PacketFieldMachine.withCell m (f m.2.1)) (compileReader q)
  | .branch f q r => .branch (fun m => f m.2.1) (compileReader q) (compileReader r)
  | .goto f => .goto (fun m => f m.2.1)
  | .halt => .halt

def readerProgram (q : PacketQueryMachine.Label) : TM2.Stmt Alphabet PacketQueryMachine.Label Memory :=
  compileReader (PacketQueryMachine.program q)

theorem readerStacks_read (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool)
    (k : PacketQueryMachine.Stack) : readerStacks S words (.inl k)=S k := rfl

theorem readerStacks_update (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool)
    (k : PacketQueryMachine.Stack) (xs : List Symbol) :
    readerStacks (Function.update S k xs) words=Function.update (readerStacks S words) (.inl k) xs := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=k
    · subst j;simp [readerStacks,Function.update]
    · simp [readerStacks,Function.update,hj]
  | inr j => simp [readerStacks,Function.update]

theorem compileReader_stepAux
    (q : TM2.Stmt (fun _ : PacketQueryMachine.Stack => Symbol) PacketQueryMachine.Label (Option Symbol))
    (v : Option Symbol) (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    TM2.stepAux (compileReader q) (PacketFieldMachine.emptyFlags,v,false) (readerStacks S words)=
      readerConfiguration (TM2.stepAux q v S) words := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [compileReader,TM2.stepAux,readerStacks_read]
    rw [←readerStacks_update]
    exact ih v _
  | peek k f q ih =>
    simp only [compileReader,TM2.stepAux,readerStacks_read,PacketFieldMachine.withCell]
    exact ih _ S
  | pop k f q ih =>
    simp only [compileReader,TM2.stepAux,readerStacks_read,PacketFieldMachine.withCell]
    rw [←readerStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [compileReader,TM2.stepAux,PacketFieldMachine.withCell]
    exact ih _ S
  | branch f q r iq ir =>
    simp only [compileReader,TM2.stepAux]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq v S | exact ir v S
  | goto f => rfl
  | halt => rfl

theorem reader_step (c : PacketQueryMachine.Configuration PacketQueryMachine.Label) (words : WordStack → List Bool) :
    TM2.step readerProgram (readerConfiguration c words)=
      (TM2.step PacketQueryMachine.program c).map (fun d => readerConfiguration d words) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [readerConfiguration,TM2.step,readerProgram,compileReader_stepAux,Option.map_some]

def readerRun (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool) :
    StateTransition.EvalsToInTime (TM2.step readerProgram)
      (readerConfiguration (PacketQueryMachine.configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache
        (encodeCache ps) (PacketQueryMachine.queryCode i.bits++rest)) words)
      (some (readerConfiguration (PacketQueryMachine.terminal ps i rest) words))
      (oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+(2*i.bits.length+3)*ps.length+
        4*(encodeCache ps).length+10) :=
  TM2ConfigurationMap.mapRun _ _ (fun c => readerConfiguration c words) (fun c => reader_step c words)
    (PacketQueryMachine.nextQueryRun ps i v oldIndex oldScratch oldCache rest)

theorem readerRun_steps (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool) :
    (readerRun ps i v oldIndex oldScratch oldCache rest words).steps=
      PacketQueryMachine.queryTime ps i oldIndex oldScratch oldCache := rfl

theorem compileReader_statementDepth
    (q : TM2.Stmt (fun _ : PacketQueryMachine.Stack => Symbol) PacketQueryMachine.Label (Option Symbol)) :
    ListAssemblyMachine.statementDepth (compileReader q)=ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
    simp only [compileReader,ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [compileReader,ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.NativeQueryMachine
