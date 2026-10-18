import CircuitNumerical.WordPacketInverse

namespace CircuitRecursion

structure NaturalWordFourProductResult where
  firstPair : NaturalWordMultiplicationResult
  secondPair : NaturalWordMultiplicationResult
  finalProduct : NaturalWordMultiplicationResult

def NaturalWordFourProductResult.bits (result : NaturalWordFourProductResult) : List Bool :=
  result.finalProduct.bits

def naturalFourProductProgram (as : List.Vector (List Bool) 4) : NaturalWordFourProductResult :=
  let first:=naturalMultiplyProgram (as.get 0) (as.get 1)
  let second:=naturalMultiplyProgram (as.get 2) (as.get 3)
  let final:=naturalMultiplyProgram first.bits second.bits
  ⟨first,second,final⟩

theorem naturalFourProductProgram_value (as : List.Vector (List Bool) 4) :
    binaryWordValue (naturalFourProductProgram as).bits=∏ i : Fin 4,binaryWordValue (as.get i) := by
  simp only [naturalFourProductProgram,NaturalWordFourProductResult.bits,naturalMultiplyProgram_value,
    Fin.prod_univ_four]
  ring

theorem naturalFourProductProgram_canonical (as : List.Vector (List Bool) 4) :
    BinaryWordCanonical (naturalFourProductProgram as).bits := naturalMultiplyProgram_canonical _ _

def NaturalWordFourProductResult.actions (result : NaturalWordFourProductResult) : ℕ :=
  result.firstPair.actions+result.secondPair.actions+result.finalProduct.actions+12

theorem naturalFourProductProgram_uniform_actions (as : List.Vector (List Bool) 4) (B : ℕ)
    (ha : ∀ i,(as.get i).length≤B) :
    (naturalFourProductProgram as).actions≤1200*(B+1)^2 := by
  have hf:=naturalMultiplyProgram_uniform_actions (as.get 0) (as.get 1) B (ha 0) (ha 1)
  have hs:=naturalMultiplyProgram_uniform_actions (as.get 2) (as.get 3) B (ha 2) (ha 3)
  have hfl:=naturalMultiplyProgram_length (as.get 0) (as.get 1)
  have hsl:=naturalMultiplyProgram_length (as.get 2) (as.get 3)
  have hfin:=naturalMultiplyProgram_uniform_actions
    (naturalMultiplyProgram (as.get 0) (as.get 1)).bits
    (naturalMultiplyProgram (as.get 2) (as.get 3)).bits (3*B)
    (by have h0:=ha 0;have h1:=ha 1;omega) (by have h2:=ha 2;have h3:=ha 3;omega)
  simp only [naturalFourProductProgram,NaturalWordFourProductResult.actions]
  calc
    _≤100*(B+1)^2+100*(B+1)^2+100*(3*B+1)^2+12 := by omega
    _≤(100*(B+1)^2+100*(B+1)^2+100*(3*B+1)^2+12)+
        (100*B^2+1400*B+888) := Nat.le_add_right _ _
    _=1200*(B+1)^2 := by ring

theorem naturalFourProductProgram_height (as : List.Vector (List Bool) 4) (B : ℕ)
    (ha : ∀ i,binaryWordValue (as.get i)≤2^B) :
    binaryWordValue (naturalFourProductProgram as).bits≤2^(4*B) := by
  rw [naturalFourProductProgram_value,Fin.prod_univ_four]
  calc
    _≤2^B*2^B*2^B*2^B := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (ha 0) (ha 1)) (ha 2)) (ha 3)
    _=2^(4*B) := by rw [←pow_add,←pow_add,←pow_add];congr 1;omega

theorem naturalProduct_replace_one (f : Fin 4 → ℕ) (i : Fin 4) :
    (∏ j : Fin 4,if j=i then 1 else f j)=∏ j∈Finset.univ.erase i,f j := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  congr 1
  ext j
  simp [Finset.mem_erase,ne_comm]

end CircuitRecursion
