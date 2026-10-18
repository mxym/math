import CircuitNumerical.FiniteStackOperationalBridge

namespace CircuitRecursion

/-- A direct LSB-first borrow program. Its numeric specification is for
canonical input words; zero is represented by the empty list. -/
def binaryPredecessorBits : List Bool → List Bool
  | [] => []
  | true::[] => []
  | true::b::bs => false::b::bs
  | false::bs => true::binaryPredecessorBits bs

theorem binaryWordCanonical_true_cons (as : List Bool) (h : BinaryWordCanonical as) :
    BinaryWordCanonical (true::as) := by
  cases as with
  | nil => exact .one
  | cons b bs => exact .prepend true b bs h

theorem binaryPredecessorBits_canonical (as : List Bool) (h : BinaryWordCanonical as) :
    BinaryWordCanonical (binaryPredecessorBits as) := by
  induction h with
  | nil => exact .nil
  | one => exact .nil
  | prepend b c cs hc ih =>
    cases b with
    | false => exact binaryWordCanonical_true_cons _ ih
    | true => exact .prepend false c cs hc

theorem binaryPredecessorBits_value (as : List Bool) (h : BinaryWordCanonical as) :
    binaryWordValue (binaryPredecessorBits as)=binaryWordValue as-1 := by
  induction h with
  | nil => rfl
  | one => decide
  | prepend b c cs hc ih =>
    have hz : binaryWordValue (c::cs)≠0 := by
      intro hzero
      have he:=(binaryWordCanonical_zero_iff (c::cs) hc).mp hzero
      cases he
    cases b with
    | false =>
      change 1+2*binaryWordValue (binaryPredecessorBits (c::cs))= (0+2*binaryWordValue (c::cs))-1
      rw [ih]
      omega
    | true =>
      change 0+2*binaryWordValue (c::cs)=(1+2*binaryWordValue (c::cs))-1
      omega

theorem binaryPredecessorBits_length (as : List Bool) (h : BinaryWordCanonical as) :
    (binaryPredecessorBits as).length≤as.length := by
  induction h with
  | nil => exact le_refl 0
  | one => decide
  | prepend b c cs hc ih =>
    cases b with
    | false => exact Nat.add_le_add_right ih 1
    | true => exact le_refl _

end CircuitRecursion
