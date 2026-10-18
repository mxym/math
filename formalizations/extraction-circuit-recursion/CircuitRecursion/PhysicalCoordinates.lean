import CircuitRecursion.ExtractionCircuit

open CircuitCompletion SymmetricSupport
namespace CircuitRecursion

def castBitsEquiv {m n : ℕ} (he : m=n) : Bits m ≃ Bits n where
  toFun := castBits he
  invFun := castBits he.symm
  left_inv := by subst n; intro b; rfl
  right_inv := by subst n; intro b; rfl

theorem castBits_apply {m n : ℕ} (he : m=n) (b : Bits m) (i : Fin n) :
    castBits he b i=b ⟨i.val,by omega⟩ := by subst n; rfl

def aliceWire (k : ℕ) (i : Fin k) : Fin (originalWireCount k) :=
  ⟨2*i.val+1,by rw [originalWireCount_eq]; omega⟩

def bobWire (k : ℕ) (i : Fin k) : Fin (originalWireCount k) :=
  ⟨2*i.val,by rw [originalWireCount_eq]; omega⟩

theorem pairwiseCoordinates_alice (k : ℕ) (b : Bits (originalWireCount k)) (i : Fin k) :
    (pairwiseCoordinates k b).1 i=b (aliceWire k i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨⟨a,t⟩,rfl⟩ := (splitRegister 2 (originalWireCount k)).symm.surjective b
    change (pairwiseCoordinates (k+1) (Fin.append a t)).1 i=
      Fin.append a t (aliceWire (k+1) i)
    erw [pairwiseCoordinates_append]
    refine Fin.cases ?_ (fun j => ?_) i
    · change a 1=Fin.append a t (aliceWire (k+1) 0)
      have hi : aliceWire (k+1) 0=Fin.castAdd (originalWireCount k) (1 : Fin 2) := by
        apply Fin.ext; rfl
      rw [hi,Fin.append_left]
    · change (pairwiseCoordinates k t).1 j=Fin.append a t (aliceWire (k+1) j.succ)
      rw [ih]
      have hi : aliceWire (k+1) j.succ=Fin.natAdd 2 (aliceWire k j) := by
        apply Fin.ext; simp [aliceWire]; omega
      rw [hi,Fin.append_right]

theorem pairwiseCoordinates_bob (k : ℕ) (b : Bits (originalWireCount k)) (i : Fin k) :
    (pairwiseCoordinates k b).2 i=b (bobWire k i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨⟨a,t⟩,rfl⟩ := (splitRegister 2 (originalWireCount k)).symm.surjective b
    change (pairwiseCoordinates (k+1) (Fin.append a t)).2 i=
      Fin.append a t (bobWire (k+1) i)
    erw [pairwiseCoordinates_append]
    refine Fin.cases ?_ (fun j => ?_) i
    · change a 0=Fin.append a t (bobWire (k+1) 0)
      have hi : bobWire (k+1) 0=Fin.castAdd (originalWireCount k) (0 : Fin 2) := by
        apply Fin.ext; rfl
      rw [hi,Fin.append_left]
    · change (pairwiseCoordinates k t).2 j=Fin.append a t (bobWire (k+1) j.succ)
      rw [ih]
      have hi : bobWire (k+1) j.succ=Fin.natAdd 2 (bobWire k j) := by
        apply Fin.ext; simp [bobWire]; omega
      rw [hi,Fin.append_right]

theorem codeWires_eq_original (k : ℕ) : codeWires k=originalWireCount (encodingPairs k) := by
  rw [originalWireCount_eq]; rfl

theorem local_register_split (k : ℕ) : encodingPairs k+bellPairYield k=k := by
  have h := encodingPairs_le_copy k
  unfold bellPairYield
  omega

/-- Only a local splitting of each party's original k qubits is used for
the readout: retain the last h qubits and discard the first ell qubits. -/
def localReadoutCoordinates (k : ℕ) : Bits k ≃ Bits (bellPairYield k)×Bits (encodingPairs k) :=
  (castBitsEquiv (local_register_split k).symm).trans
    ((splitRegister (encodingPairs k) (bellPairYield k)).trans (Equiv.prodComm _ _))

def readoutCoordinates (k : ℕ) : Bits (originalWireCount k) ≃
    (Bits (bellPairYield k)×Bits (encodingPairs k))×
      (Bits (bellPairYield k)×Bits (encodingPairs k)) :=
  (pairwiseCoordinates k).trans (Equiv.prodCongr (localReadoutCoordinates k) (localReadoutCoordinates k))

def codePairCoordinates (k : ℕ) : Bits (codeWires k) ≃
    Bits (encodingPairs k)×Bits (encodingPairs k) :=
  (castBitsEquiv (codeWires_eq_original k)).trans (pairwiseCoordinates (encodingPairs k))

def localDigits (k : ℕ) : Fin (2^k) ≃ Bits k :=
  (finFunctionFinEquiv : (Fin k → Fin 2) ≃ Fin (2^k)).symm.trans
    (Equiv.piCongrRight (fun _ => finTwoEquiv))

/-- The paired-bit coordinates agree with the existing physical copywise
Alice/Bob convention through two separate local binary-digit equivalences. -/
theorem pairwiseCoordinates_physical (k : ℕ) :
    pairwiseCoordinates k=(bitBipartiteCoordinates k).trans
      (Equiv.prodCongr (localDigits k) (localDigits k)) := by
  apply Equiv.ext
  intro b
  apply Prod.ext <;> funext i
  · change letterBits ((originalBitCoordinates k).symm b i) 1=
      finTwoEquiv (finFunctionFinEquiv.symm
        (finFunctionFinEquiv (fun j =>
          ((finProdFinEquiv : Fin 2×Fin 2 ≃ Fin 4).symm
            ((originalBitCoordinates k).symm b j)).1)) i)
    simp only [Equiv.symm_apply_apply]
    exact (letterBits_physical _).1
  · change letterBits ((originalBitCoordinates k).symm b i) 0=
      finTwoEquiv (finFunctionFinEquiv.symm
        (finFunctionFinEquiv (fun j =>
          ((finProdFinEquiv : Fin 2×Fin 2 ≃ Fin 4).symm
            ((originalBitCoordinates k).symm b j)).2)) i)
    simp only [Equiv.symm_apply_apply]
    exact (letterBits_physical _).2

theorem readoutCoordinates_split (k : ℕ) (b : Bits (originalWireCount k)) :
    readoutCoordinates k b=
      (((pairwiseCoordinates (bellPairYield k)
          (suffixBits (castBits (register_split k).symm b))).1,
        (codePairCoordinates k (prefixBits (castBits (register_split k).symm b))).1),
       ((pairwiseCoordinates (bellPairYield k)
          (suffixBits (castBits (register_split k).symm b))).2,
        (codePairCoordinates k (prefixBits (castBits (register_split k).symm b))).2)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change suffixBits (castBits (local_register_split k).symm (pairwiseCoordinates k b).1) i=_
      simp only [suffixBits,castBits_apply,pairwiseCoordinates_alice]
      congr 1
      apply Fin.ext
      simp [aliceWire,codeWires,Nat.mul_add,Nat.add_assoc]
    · funext i
      change prefixBits (castBits (local_register_split k).symm (pairwiseCoordinates k b).1) i=
        (pairwiseCoordinates (encodingPairs k)
          (castBits (codeWires_eq_original k) (prefixBits (castBits (register_split k).symm b)))).1 i
      simp only [prefixBits,castBits_apply,pairwiseCoordinates_alice]
      congr 1
  · apply Prod.ext
    · funext i
      change suffixBits (castBits (local_register_split k).symm (pairwiseCoordinates k b).2) i=_
      simp only [suffixBits,castBits_apply,pairwiseCoordinates_bob]
      congr 1
      apply Fin.ext
      simp [bobWire,codeWires,Nat.mul_add]
    · funext i
      change prefixBits (castBits (local_register_split k).symm (pairwiseCoordinates k b).2) i=
        (pairwiseCoordinates (encodingPairs k)
          (castBits (codeWires_eq_original k) (prefixBits (castBits (register_split k).symm b)))).2 i
      simp only [prefixBits,castBits_apply,pairwiseCoordinates_bob]
      congr 1

end CircuitRecursion
