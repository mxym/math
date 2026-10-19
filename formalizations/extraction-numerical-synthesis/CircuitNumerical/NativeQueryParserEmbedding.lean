import CircuitNumerical.NativeQueryReaderEmbedding

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

/-- The concrete reader output stack is the parser input. -/
def inputStack : PacketQueryMachine.Stack := .inl (.inl .left)

def parserStacks (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) : ∀ k,List (Alphabet k)
  | .inl k => if k=inputStack then S .input else old k
  | .inr .scratch => S .scratch
  | .inr (.numerator q) => S (.numerator q)
  | .inr .denominator => S .denominator

def parserConfiguration {Λ : Type*} (embed : PacketFieldMachine.Label → Λ)
    (c : PacketFieldMachine.Configuration) (old : PacketQueryMachine.Stack → List Symbol) : TM2.Cfg Alphabet Λ Memory :=
  ⟨c.l.map embed,c.var,parserStacks c.stk old⟩

def compileParser {Λ : Type*} (embed : PacketFieldMachine.Label → Λ) :
    TM2.Stmt PacketFieldMachine.Alphabet PacketFieldMachine.Label Memory → TM2.Stmt Alphabet Λ Memory
  | .push (.input) f q => .push (.inl inputStack) f (compileParser embed q)
  | .push (.scratch) f q => .push (.inr .scratch) f (compileParser embed q)
  | .push (.numerator k) f q => .push (.inr (.numerator k)) f (compileParser embed q)
  | .push (.denominator) f q => .push (.inr .denominator) f (compileParser embed q)
  | .peek (.input) f q => .peek (.inl inputStack) f (compileParser embed q)
  | .peek (.scratch) f q => .peek (.inr .scratch) f (compileParser embed q)
  | .peek (.numerator k) f q => .peek (.inr (.numerator k)) f (compileParser embed q)
  | .peek (.denominator) f q => .peek (.inr .denominator) f (compileParser embed q)
  | .pop (.input) f q => .pop (.inl inputStack) f (compileParser embed q)
  | .pop (.scratch) f q => .pop (.inr .scratch) f (compileParser embed q)
  | .pop (.numerator k) f q => .pop (.inr (.numerator k)) f (compileParser embed q)
  | .pop (.denominator) f q => .pop (.inr .denominator) f (compileParser embed q)
  | .load f q => .load f (compileParser embed q)
  | .branch f q r => .branch f (compileParser embed q) (compileParser embed r)
  | .goto f => .goto (fun m => embed (f m))
  | .halt => .halt

theorem parserStacks_input (S : ∀ k,List (PacketFieldMachine.Alphabet k)) (old : PacketQueryMachine.Stack → List Symbol) :
    parserStacks S old (.inl inputStack)=S .input := by simp only [parserStacks,ite_true]

theorem parserStacks_scratch (S : ∀ k,List (PacketFieldMachine.Alphabet k)) (old : PacketQueryMachine.Stack → List Symbol) :
    parserStacks S old (.inr .scratch)=S .scratch := rfl

theorem parserStacks_numerator (S : ∀ k,List (PacketFieldMachine.Alphabet k)) (old : PacketQueryMachine.Stack → List Symbol)
    (q : PacketFieldMachine.Coordinate) : parserStacks S old (.inr (.numerator q))=S (.numerator q) := rfl

theorem parserStacks_denominator (S : ∀ k,List (PacketFieldMachine.Alphabet k)) (old : PacketQueryMachine.Stack → List Symbol) :
    parserStacks S old (.inr .denominator)=S .denominator := rfl

theorem parserStacks_update_input (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) (xs : List Symbol) :
    parserStacks (Function.update S .input xs) old=Function.update (parserStacks S old) (.inl inputStack) xs := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=inputStack
    · subst j;simp [parserStacks,Function.update] <;> rfl
    · simp [parserStacks,Function.update,hj] <;> rfl
  | inr j =>
    cases j with
    | scratch | denominator => simp [parserStacks,Function.update] <;> rfl
    | numerator k => simp [parserStacks,Function.update] <;> rfl

theorem parserStacks_update_scratch (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) (xs : List Bool) :
    parserStacks (Function.update S .scratch xs) old=Function.update (parserStacks S old) (.inr .scratch) xs := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=inputStack
    · subst j;simp [parserStacks,Function.update] <;> rfl
    · simp [parserStacks,Function.update,hj] <;> rfl
  | inr j =>
    cases j with
    | scratch | denominator => simp [parserStacks,Function.update] <;> rfl
    | numerator k => simp [parserStacks,Function.update] <;> rfl

theorem parserStacks_update_numerator (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) (q : PacketFieldMachine.Coordinate) (xs : List Bool) :
    parserStacks (Function.update S (.numerator q) xs) old=Function.update (parserStacks S old) (.inr (.numerator q)) xs := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=inputStack
    · subst j;simp [parserStacks,Function.update] <;> rfl
    · simp [parserStacks,Function.update,hj] <;> rfl
  | inr j =>
    cases j with
    | scratch | denominator => simp [parserStacks,Function.update] <;> rfl
    | numerator k =>
      by_cases hk : k=q
      · subst k;simp [parserStacks,Function.update] <;> rfl
      · simp [parserStacks,Function.update,hk] <;> rfl

theorem parserStacks_update_denominator (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) (xs : List Bool) :
    parserStacks (Function.update S .denominator xs) old=Function.update (parserStacks S old) (.inr .denominator) xs := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=inputStack
    · subst j;simp [parserStacks,Function.update] <;> rfl
    · simp [parserStacks,Function.update,hj] <;> rfl
  | inr j =>
    cases j with
    | scratch | denominator => simp [parserStacks,Function.update] <;> rfl
    | numerator k => simp [parserStacks,Function.update] <;> rfl

theorem compileParser_stepAux {Λ : Type*} (embed : PacketFieldMachine.Label → Λ)
    (q : TM2.Stmt PacketFieldMachine.Alphabet PacketFieldMachine.Label Memory) (v : Memory)
    (S : ∀ k,List (PacketFieldMachine.Alphabet k)) (old : PacketQueryMachine.Stack → List Symbol) :
    TM2.stepAux (compileParser embed q) v (parserStacks S old)=parserConfiguration embed (TM2.stepAux q v S) old := by
  induction q generalizing v S with
  | push k f q ih =>
    cases k with
    | input =>
      simp only [compileParser,TM2.stepAux,parserStacks_input]
      rw [←parserStacks_update_input]
      exact ih v _
    | scratch =>
      simp only [compileParser,TM2.stepAux,parserStacks_scratch]
      rw [←parserStacks_update_scratch]
      exact ih v _
    | numerator k =>
      simp only [compileParser,TM2.stepAux,parserStacks_numerator]
      rw [←parserStacks_update_numerator]
      exact ih v _
    | denominator =>
      simp only [compileParser,TM2.stepAux,parserStacks_denominator]
      rw [←parserStacks_update_denominator]
      exact ih v _
  | peek k f q ih =>
    cases k with
    | input =>
      simp only [compileParser,TM2.stepAux,parserStacks_input]
      exact ih _ S
    | scratch =>
      simp only [compileParser,TM2.stepAux,parserStacks_scratch]
      exact ih _ S
    | numerator k =>
      simp only [compileParser,TM2.stepAux,parserStacks_numerator]
      exact ih _ S
    | denominator =>
      simp only [compileParser,TM2.stepAux,parserStacks_denominator]
      exact ih _ S
  | pop k f q ih =>
    cases k with
    | input =>
      simp only [compileParser,TM2.stepAux,parserStacks_input]
      rw [←parserStacks_update_input]
      exact ih _ _
    | scratch =>
      simp only [compileParser,TM2.stepAux,parserStacks_scratch]
      rw [←parserStacks_update_scratch]
      exact ih _ _
    | numerator k =>
      simp only [compileParser,TM2.stepAux,parserStacks_numerator]
      rw [←parserStacks_update_numerator]
      exact ih _ _
    | denominator =>
      simp only [compileParser,TM2.stepAux,parserStacks_denominator]
      rw [←parserStacks_update_denominator]
      exact ih _ _
  | load f q ih =>
    simp only [compileParser,TM2.stepAux]
    exact ih _ S
  | branch f q r iq ir =>
    simp only [compileParser,TM2.stepAux]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq v S | exact ir v S
  | goto f => rfl
  | halt => rfl

theorem parser_step {Λ : Type*} (embed : PacketFieldMachine.Label → Λ)
    (N : Λ → TM2.Stmt Alphabet Λ Memory) (hcode : ∀ q,N (embed q)=compileParser embed (PacketFieldMachine.program q))
    (old : PacketQueryMachine.Stack → List Symbol) (c : PacketFieldMachine.Configuration) :
    TM2.step N (parserConfiguration embed c old)=
      (TM2.step PacketFieldMachine.program c).map (fun d => parserConfiguration embed d old) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [parserConfiguration,TM2.step,Option.map_some,hcode,compileParser_stepAux]

def parserRun {Λ : Type*} (embed : PacketFieldMachine.Label → Λ)
    (N : Λ → TM2.Stmt Alphabet Λ Memory) (hcode : ∀ q,N (embed q)=compileParser embed (PacketFieldMachine.program q))
    (old : PacketQueryMachine.Stack → List Symbol) (p : WordIntegerPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step N)
      (parserConfiguration embed (PacketFieldMachine.configuration (some (.sign .n0)) PacketFieldMachine.emptyFlags none false
        (encodePacket p++rest) [] PacketFieldMachine.emptyFields []) old)
      (some (parserConfiguration embed (PacketFieldMachine.terminal (rawPacket p) rest) old))
      (PacketFieldMachine.parseTime (rawPacket p)) :=
  TM2ConfigurationMap.mapRun _ _ (fun c => parserConfiguration embed c old) (parser_step embed N hcode old)
    (PacketFieldMachine.parsePacketRun p rest)

theorem compileParser_statementDepth {Λ : Type*} (embed : PacketFieldMachine.Label → Λ)
    (q : TM2.Stmt PacketFieldMachine.Alphabet PacketFieldMachine.Label Memory) :
    ListAssemblyMachine.statementDepth (compileParser embed q)=ListAssemblyMachine.statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih =>
    cases k <;> simp only [compileParser,ListAssemblyMachine.statementDepth,ih]
  | load f q ih => simp only [compileParser,ListAssemblyMachine.statementDepth,ih]
  | branch f q r iq ir => simp only [compileParser,ListAssemblyMachine.statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.NativeQueryMachine
