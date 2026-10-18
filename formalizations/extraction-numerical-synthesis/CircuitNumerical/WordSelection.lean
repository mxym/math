import CircuitNumerical.WordPacketDistance

namespace CircuitRecursion

inductive WordMinimumTrace where
  | terminal : WordMinimumTrace
  | frame : WordMinimumTrace → WordScalarComparisonResult → WordMinimumTrace

structure WordMinimumResult (n : ℕ) where
  index : Fin (n+1)
  trace : WordMinimumTrace

/-- The input is materialized scalar data. The recursive minimum and the
comparison result are each stored once. Reading a winning score does not
invoke an expression evaluator. -/
def wordMinimumProgram : (n : ℕ) → List.Vector WordIntegerScalar (n+1) → WordMinimumResult n
  | 0,_ => ⟨0,.terminal⟩
  | n+1,scores =>
    let previous:=wordMinimumProgram n scores.tail
    let comparison:=wordScalarLEProgram (scores.get 0) (scores.get previous.index.succ)
    ⟨if comparison.le then 0 else previous.index.succ,.frame previous.trace comparison⟩

theorem wordMinimumProgram_index (n : ℕ) (scores : List.Vector WordIntegerScalar (n+1)) :
    (wordMinimumProgram n scores).index=integerMinIndex n (fun i => (scores.get i).decode) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordMinimumProgram,integerMinIndex,ih,List.Vector.get_tail_succ,
      wordScalarLEProgram_correct]

def WordMinimumTrace.actions : WordMinimumTrace → ℕ
  | .terminal => 1
  | .frame previous comparison => previous.actions+comparison.actions+4

theorem wordMinimumProgram_height_actions (n : ℕ) (scores : List.Vector WordIntegerScalar (n+1))
    (B : ℕ) (hs : ∀ i,IntegerScalarHeight (scores.get i).decode B) :
    (wordMinimumProgram n scores).trace.actions≤1+n*(400*(B+2)^2+4) := by
  induction n with
  | zero => simp only [wordMinimumProgram,WordMinimumTrace.actions,zero_mul,add_zero,le_refl]
  | succ n ih =>
    have ht:=ih scores.tail (by intro i;simpa only [List.Vector.get_tail_succ] using hs i.succ)
    have hc:=wordScalarLEProgram_height_actions (scores.get 0)
      (scores.get (wordMinimumProgram n scores.tail).index.succ) B (hs 0) (hs _)
    simp only [wordMinimumProgram,WordMinimumTrace.actions]
    calc
      _≤(1+n*(400*(B+2)^2+4))+400*(B+2)^2+4 := by omega
      _=1+(n+1)*(400*(B+2)^2+4) := by ring

structure WordMaximumResult (n : ℕ) where
  index : Fin (n+1)
  negations : List.Vector WordScalarNegationResult (n+1)
  minimum : WordMinimumResult n

/-- Negated scores are materialized once before running the cached minimum. -/
def wordMaximumProgram (n : ℕ) (scores : List.Vector WordIntegerScalar (n+1)) : WordMaximumResult n :=
  let negated:=List.Vector.ofFn (fun i => wordScalarNegateProgram (scores.get i))
  let minimum:=wordMinimumProgram n (negated.map WordScalarNegationResult.scalar)
  ⟨minimum.index,negated,minimum⟩

theorem wordMaximumProgram_index (n : ℕ) (scores : List.Vector WordIntegerScalar (n+1)) :
    (wordMaximumProgram n scores).index=integerMaxIndex n (fun i => (scores.get i).decode) := by
  simp only [wordMaximumProgram,wordMinimumProgram_index,List.Vector.get_map,List.Vector.get_ofFn,
    wordScalarNegateProgram_decode,integerMaxIndex]

def WordMaximumResult.actions {n : ℕ} (result : WordMaximumResult n) : ℕ :=
  (Finset.univ.sum (fun i : Fin (n+1) => (result.negations.get i).normalizationRun.actions+4))+
    result.minimum.trace.actions+4

theorem wordMaximumProgram_height_actions (n : ℕ) (scores : List.Vector WordIntegerScalar (n+1))
    (B : ℕ) (hs : ∀ i,IntegerScalarHeight (scores.get i).decode B) :
    (wordMaximumProgram n scores).actions≤
      (n+1)*(6*(B+2)+8)+(1+n*(400*(B+2)^2+4))+4 := by
  let negated:=List.Vector.ofFn (fun i => wordScalarNegateProgram (scores.get i))
  have hn : ∀ i,(negated.get i).normalizationRun.actions+4≤6*(B+2)+8 := by
    intro i
    have hw:=((scores.get i).height_width B (hs i)).1
    have h:=wordScalarNegateProgram_actions (scores.get i)
    simp only [negated,List.Vector.get_ofFn]
    omega
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hn i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  have hmin:=wordMinimumProgram_height_actions n (negated.map WordScalarNegationResult.scalar) B (by
    intro i
    simp only [negated,List.Vector.get_map,List.Vector.get_ofFn,wordScalarNegateProgram_decode]
    exact IntegerScalar.neg_height _ B (hs i))
  change (Finset.univ.sum (fun i : Fin (n+1) => (negated.get i).normalizationRun.actions+4))+
    (wordMinimumProgram n (negated.map WordScalarNegationResult.scalar)).trace.actions+4≤_
  omega

theorem wordMaximumProgram_four_height_actions (scores : List.Vector WordIntegerScalar 4)
    (B : ℕ) (hs : ∀ i,IntegerScalarHeight (scores.get i).decode B) :
    (wordMaximumProgram 3 scores).actions≤1300*(B+2)^2 := by
  have h:=wordMaximumProgram_height_actions 3 scores B hs
  nlinarith

end CircuitRecursion
