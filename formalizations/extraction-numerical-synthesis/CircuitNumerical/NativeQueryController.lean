import CircuitNumerical.NativeQueryParserEmbedding

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

abbrev Label := WordStack ⊕ (PacketQueryMachine.Label ⊕ PacketFieldMachine.Label)
abbrev Configuration := TM2.Cfg Alphabet Label Memory

def readerEmbed (q : PacketQueryMachine.Label) : Label := .inr (.inl q)
def parserEmbed (q : PacketFieldMachine.Label) : Label := .inr (.inr q)
def readerReturn (_ : Memory) : Label := parserEmbed (.sign .n0)
def resetMemory : Memory := (PacketFieldMachine.emptyFlags,none,false)

def clearNext : WordStack → Label
  | .scratch => .inl (.numerator .n0)
  | .numerator .n0 => .inl (.numerator .n1)
  | .numerator .n1 => .inl (.numerator .n2)
  | .numerator .n2 => .inl (.numerator .n3)
  | .numerator .n3 => .inl .denominator
  | .denominator => readerEmbed (.inl .clearIndex)

def clearFinishMemory (w : WordStack) (m : Memory) : Memory :=
  match w with
  | .denominator => resetMemory
  | _ => PacketFieldMachine.withCell m none

/-- The six native-word stacks are explicitly cleared before the actual
query reader. Its halt returns into the typed Bool-word parser in the same
finite heterogeneous-stack program. -/
def program : Label → TM2.Stmt Alphabet Label Memory
  | .inl w => .pop (.inr w) (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome) (.goto (fun _ => .inl w))
        (.load (fun m => match w with | .denominator => resetMemory | _ => m) (.goto (fun _ => clearNext w))))
  | .inr (.inl q) => TM2Subroutine.redirect readerEmbed readerReturn (readerProgram q)
  | .inr (.inr q) => compileParser parserEmbed (PacketFieldMachine.program q)

def configuration (l : Option Label) (m : Memory) (S : PacketQueryMachine.Stack → List Symbol)
    (words : WordStack → List Bool) : Configuration := ⟨l,m,readerStacks S words⟩

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

def emptyWords : WordStack → List Bool := fun _ => []

def wordVolume (words : WordStack → List Bool) : ℕ :=
  (words .scratch).length+(words (.numerator .n0)).length+(words (.numerator .n1)).length+
    (words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length

theorem readerStacks_word_update (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool)
    (w : WordStack) (xs : List Bool) :
    readerStacks S (Function.update words w xs)=Function.update (readerStacks S words) (.inr w) xs := by
  funext k
  cases k with
  | inl k => simp [readerStacks,Function.update]
  | inr k =>
    by_cases hk : k=w
    · subst k;simp [readerStacks,Function.update]
    · simp [readerStacks,Function.update,hk]

theorem words_update_self (words : WordStack → List Bool) (w : WordStack) :
    Function.update words w (words w)=words := by
  funext k
  by_cases hk : k=w
  · subst k;simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]

theorem words_update_twice (words : WordStack → List Bool) (w : WordStack) (xs ys : List Bool) :
    Function.update (Function.update words w xs) w ys=Function.update words w ys := by
  funext k
  by_cases hk : k=w
  · subst k;simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]

theorem clearFinishMemory_withCell (w : WordStack) (m : Memory) (x : Option Symbol) :
    clearFinishMemory w (PacketFieldMachine.withCell m x)=clearFinishMemory w m := by
  cases w <;> rfl

theorem clear_word_nil (w : WordStack) (m : Memory) (S : PacketQueryMachine.Stack → List Symbol)
    (words : WordStack → List Bool) :
    TM2.step program (configuration (some (.inl w)) m S (Function.update words w []))=
      some (configuration (some (clearNext w)) (clearFinishMemory w m) S (Function.update words w [])) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,readerStacks,Function.update_self,
    List.head?_nil,List.tail_nil,Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false]
  rw [←readerStacks_word_update,words_update_twice]
  cases w <;> rfl

theorem clear_word_cons (w : WordStack) (m : Memory) (S : PacketQueryMachine.Stack → List Symbol)
    (words : WordStack → List Bool) (b : Bool) (bs : List Bool) :
    TM2.step program (configuration (some (.inl w)) m S (Function.update words w (b::bs)))=
      some (configuration (some (.inl w)) (PacketFieldMachine.withCell m (some (.bit b))) S (Function.update words w bs)) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,readerStacks,Function.update_self,
    List.head?_cons,List.tail_cons,Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true]
  rw [←readerStacks_word_update,words_update_twice]

theorem clearWord_iterate_override (w : WordStack) (xs : List Bool) (m : Memory)
    (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    advance^[xs.length+1] (some (configuration (some (.inl w)) m S (Function.update words w xs)))=
      some (configuration (some (clearNext w)) (clearFinishMemory w m) S (Function.update words w [])) := by
  induction xs generalizing m with
  | nil => exact clear_word_nil w m S words
  | cons b bs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bs.length+1] (TM2.step program
      (configuration (some (.inl w)) m S (Function.update words w (b::bs))))=_
    rw [clear_word_cons,ih,clearFinishMemory_withCell]

theorem clearWord_iterate (w : WordStack) (m : Memory)
    (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    advance^[(words w).length+1] (some (configuration (some (.inl w)) m S words))=
      some (configuration (some (clearNext w)) (clearFinishMemory w m) S (Function.update words w [])) := by
  simpa only [words_update_self] using clearWord_iterate_override w (words w) m S words

end CircuitRecursion.NativeQueryMachine
