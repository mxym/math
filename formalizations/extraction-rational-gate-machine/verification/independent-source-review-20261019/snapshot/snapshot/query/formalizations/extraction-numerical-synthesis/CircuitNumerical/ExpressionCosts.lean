import CircuitNumerical.ExpressionExecution

namespace CircuitRecursion

mutual
def ScalarExpression.executedOperations : ScalarExpression → ℕ
  | .literal _ => 1
  | .stoppingThreshold _ => 4
  | .add a b => a.executedOperations+b.executedOperations+1
  | .neg a => a.executedOperations+1
  | .mul a b => a.executedOperations+b.executedOperations+1
  | .inv a => a.executedOperations+1
  | .sqrt a _ => a.executedOperations+8
  | .meanMinus a => a.executedOperations+2
  | .coordinate a _ => a.executedOperations+1
  | .distance a b => a.executedOperations+b.executedOperations+16
def PacketExpression.executedOperations : PacketExpression → ℕ
  | .literal _ => 1
  | .tuple a => (∑ i : Fin 4,(a i).executedOperations)+4
  | .mul a b => a.executedOperations+b.executedOperations+48
  | .inverse a => a.executedOperations+4
  | .selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).run)
    (∑ i : Fin 4,(scores i).executedOperations)+
      (branches (rationalMaxIndex 3 values.get)).executedOperations+3
end

mutual
theorem ScalarExpression.executedOperations_le (e : ScalarExpression) :
    e.executedOperations≤e.operations := by
  cases e with
  | literal q => exact le_refl 1
  | stoppingThreshold t => exact le_refl 4
  | add a b => exact Nat.add_le_add_right (Nat.add_le_add (ScalarExpression.executedOperations_le a) (ScalarExpression.executedOperations_le b)) 1
  | neg a => exact Nat.add_le_add_right (ScalarExpression.executedOperations_le a) 1
  | mul a b => exact Nat.add_le_add_right (Nat.add_le_add (ScalarExpression.executedOperations_le a) (ScalarExpression.executedOperations_le b)) 1
  | inv a => exact Nat.add_le_add_right (ScalarExpression.executedOperations_le a) 1
  | sqrt a p => exact Nat.add_le_add_right (ScalarExpression.executedOperations_le a) 8
  | meanMinus a => exact Nat.add_le_add_right (ScalarExpression.executedOperations_le a) 2
  | coordinate a i => exact Nat.add_le_add_right (PacketExpression.executedOperations_le a) 1
  | distance a b =>
    exact Nat.add_le_add_right
      (Nat.add_le_add (PacketExpression.executedOperations_le a) (PacketExpression.executedOperations_le b)) 16
theorem PacketExpression.executedOperations_le (e : PacketExpression) :
    e.executedOperations≤e.operations := by
  cases e with
  | literal q => exact le_refl 1
  | tuple a =>
    exact Nat.add_le_add_right
      (Finset.sum_le_sum (fun i _ => ScalarExpression.executedOperations_le (a i))) 4
  | mul a b => exact Nat.add_le_add_right (Nat.add_le_add (PacketExpression.executedOperations_le a) (PacketExpression.executedOperations_le b)) 48
  | inverse a => exact Nat.add_le_add_right (PacketExpression.executedOperations_le a) 4
  | selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).run)
    let j := rationalMaxIndex 3 values.get
    have hs := Finset.sum_le_sum (s:=Finset.univ)
      (fun i (_ : i∈Finset.univ) => ScalarExpression.executedOperations_le (scores i))
    have hb : (branches j).executedOperations≤∑ i : Fin 4,(branches i).operations :=
      (PacketExpression.executedOperations_le (branches j)).trans
        (Finset.single_le_sum (fun i _ => Nat.zero_le ((branches i).operations)) (Finset.mem_univ j))
    exact Nat.add_le_add_right (Nat.add_le_add hs hb) 3
end

def ArithmeticWordResult.executedOperations {m : ℕ} (r : ArithmeticWordResult m) : ℕ :=
  (r.expressions.map ScalarExpression.executedOperations).sum+r.comparisons

theorem ArithmeticWordResult.executedOperations_le {m : ℕ} (r : ArithmeticWordResult m) :
    r.executedOperations≤r.operations := by
  apply Nat.add_le_add_right
  induction r.expressions with
  | nil => exact le_refl 0
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (ScalarExpression.executedOperations_le e) ih

end CircuitRecursion
