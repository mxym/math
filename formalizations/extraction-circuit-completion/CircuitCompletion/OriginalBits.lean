import CircuitCompletion.EncodedBranches

open SymmetricSupport
namespace CircuitCompletion

def originalWireCount : ℕ → ℕ
  | 0 => 0
  | k+1 => 2+originalWireCount k

theorem originalWireCount_eq (k : ℕ) : originalWireCount k=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [originalWireCount,ih];omega

def wordHeadTail (k : ℕ) : Word 4 (k+1) ≃ Fin 4×Word 4 k where
  toFun w := (w 0,fun i => w i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by cases p;rfl

/-- Explicit paired-copy order on exactly the original 2k wires. New copies
are prefixed so the fresh pair and the old compressed code are contiguous. -/
def originalBitCoordinates : (k : ℕ) → Word 4 k ≃ Bits (originalWireCount k)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ i => Fin.elim0 i
      left_inv := fun w => by funext i;exact Fin.elim0 i
      right_inv := fun w => by funext i;exact Fin.elim0 i }
  | k+1 => (wordHeadTail k).trans
      ((Equiv.prodCongr letterBits (originalBitCoordinates k)).trans
        (splitRegister 2 (originalWireCount k)).symm)

theorem originalBitCoordinates_cons (k : ℕ) (i : Fin 4) (w : Word 4 k) :
    originalBitCoordinates (k+1) (Fin.cons i w)=
      Fin.append (letterBits i) (originalBitCoordinates k w) := rfl

theorem originalBitCoordinates_cons_symm (k : ℕ) (i : Fin 4) (b : Bits (originalWireCount k)) :
    (originalBitCoordinates (k+1)).symm (Fin.append (letterBits i) b)=
      Fin.cons i ((originalBitCoordinates k).symm b) := by
  change (Fin.cons (letterBits.symm (prefixBits (Fin.append (letterBits i) b)))
    ((originalBitCoordinates k).symm (suffixBits (Fin.append (letterBits i) b))) : Word 4 (k+1))=_
  have hp : prefixBits (Fin.append (letterBits i) b)=letterBits i := by funext j;simp [prefixBits]
  have hs : suffixBits (Fin.append (letterBits i) b)=b := by funext j;simp [suffixBits]
  rw [hp,hs,letterBits.symm_apply_apply]

noncomputable def bitOccupation {k : ℕ} (ν : Sym (Fin 4) k) : Bits (originalWireCount k) → ℂ :=
  fun b => occupationVector ν ((originalBitCoordinates k).symm b)

theorem bitOccupation_branch {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 4)
    (b : Bits (originalWireCount k)) :
    bitOccupation ν (Fin.append (letterBits i) b)=
      if hi : i∈ν then (Real.sqrt (occupationMass ν i) : ℂ)*bitOccupation (ν.erase i hi) b else 0 := by
  change occupationVector ν ((originalBitCoordinates (k+1)).symm (Fin.append (letterBits i) b))=
    if hi : i∈ν then (Real.sqrt (occupationMass ν i) : ℂ)*
      occupationVector (ν.erase i hi) ((originalBitCoordinates k).symm b) else 0
  rw [originalBitCoordinates_cons_symm,occupationVector_branch]
  rfl

/-- Reindexing from paired original-copy wires to the physical Alice/Bob
copywise coordinates is fixed explicitly, with no cardinality-choice map. -/
def bitBipartiteCoordinates (k : ℕ) :
    Bits (originalWireCount k) ≃ Fin (2^k)×Fin (2^k) :=
  (originalBitCoordinates k).symm.trans (copywiseCoordinates 2 2 k)

end CircuitCompletion
