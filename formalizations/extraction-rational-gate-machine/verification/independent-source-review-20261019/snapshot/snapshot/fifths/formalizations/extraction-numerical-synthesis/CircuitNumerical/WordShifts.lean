import CircuitNumerical.WordScalarReciprocal

namespace CircuitRecursion

inductive BinaryWordRawShiftTrace where
  | terminal : BinaryWordRawShiftTrace
  | step : BinaryWordRawShiftTrace → BinaryWordRawShiftTrace

structure BinaryWordRawShiftResult where
  bits : List Bool
  trace : BinaryWordRawShiftTrace

def binaryRawShiftProgram : ℕ → List Bool → BinaryWordRawShiftResult
  | 0,as => ⟨as,.terminal⟩
  | p+1,as =>
    let previous:=binaryRawShiftProgram p as
    ⟨false::previous.bits,.step previous.trace⟩

theorem binaryRawShiftProgram_value (p : ℕ) (as : List Bool) :
    binaryWordValue (binaryRawShiftProgram p as).bits=binaryWordValue as*2^p := by
  induction p with
  | zero => simp [binaryRawShiftProgram]
  | succ p ih => simp only [binaryRawShiftProgram,binaryWordValue,binaryBitValue,zero_add,ih,pow_succ];ring

theorem binaryRawShiftProgram_length (p : ℕ) (as : List Bool) :
    (binaryRawShiftProgram p as).bits.length=as.length+p := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [binaryRawShiftProgram,List.length_cons,ih];omega

def BinaryWordRawShiftTrace.actions : BinaryWordRawShiftTrace → ℕ
  | .terminal => 1
  | .step tail => tail.actions+2

theorem binaryRawShiftProgram_actions (p : ℕ) (as : List Bool) :
    (binaryRawShiftProgram p as).trace.actions=2*p+1 := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [binaryRawShiftProgram,BinaryWordRawShiftTrace.actions,ih];omega

structure BinaryWordShiftResult where
  bits : List Bool
  shiftTrace : BinaryWordRawShiftTrace
  trimTrace : BinaryWordTrimTrace

def binaryShiftProgram (p : ℕ) (as : List Bool) : BinaryWordShiftResult :=
  let shifted:=binaryRawShiftProgram p as
  let trimmed:=binaryTrimProgram shifted.bits
  ⟨trimmed.bits,shifted.trace,trimmed.trace⟩

theorem binaryShiftProgram_value (p : ℕ) (as : List Bool) :
    binaryWordValue (binaryShiftProgram p as).bits=binaryWordValue as*2^p := by
  simp only [binaryShiftProgram,binaryTrimProgram_value,binaryRawShiftProgram_value]

theorem binaryShiftProgram_canonical (p : ℕ) (as : List Bool) :
    BinaryWordCanonical (binaryShiftProgram p as).bits := binaryTrimProgram_canonical _

theorem binaryShiftProgram_length (p : ℕ) (as : List Bool) :
    (binaryShiftProgram p as).bits.length≤as.length+p := by
  have h:=binaryTrimProgram_length (binaryRawShiftProgram p as).bits
  simpa only [binaryShiftProgram,binaryRawShiftProgram_length] using h

def BinaryWordShiftResult.actions (result : BinaryWordShiftResult) : ℕ :=
  result.shiftTrace.actions+result.trimTrace.actions+4

theorem binaryShiftProgram_actions (p : ℕ) (as : List Bool) :
    (binaryShiftProgram p as).actions≤8*(as.length+p+1)+4 := by
  have ht:=binaryTrimProgram_actions (binaryRawShiftProgram p as).bits
  simp only [binaryRawShiftProgram_length] at ht
  simp only [binaryShiftProgram,BinaryWordShiftResult.actions,binaryRawShiftProgram_actions]
  omega

def binaryPowerTwoProgram (p : ℕ) : BinaryWordShiftResult := binaryShiftProgram p [true]

theorem binaryPowerTwoProgram_value (p : ℕ) :
    binaryWordValue (binaryPowerTwoProgram p).bits=2^p := by
  simpa only [binaryPowerTwoProgram,binaryWordValue,binaryBitValue,mul_zero,add_zero,one_mul] using
    binaryShiftProgram_value p [true]

theorem binaryPowerTwoProgram_canonical (p : ℕ) :
    BinaryWordCanonical (binaryPowerTwoProgram p).bits := binaryShiftProgram_canonical _ _

theorem binaryPowerTwoProgram_actions (p : ℕ) :
    (binaryPowerTwoProgram p).actions≤8*(p+2)+4 := by
  have h:=binaryShiftProgram_actions p [true]
  simp only [binaryPowerTwoProgram,List.length_cons,List.length_nil] at h ⊢
  omega

def SignedBinaryWord.positiveBits (a : SignedBinaryWord) : List Bool :=
  if a.negative then [] else a.bits

theorem SignedBinaryWord.positiveBits_value (a : SignedBinaryWord) :
    binaryWordValue a.positiveBits=a.value.toNat := by
  cases hs : a.negative <;> simp [positiveBits,value,hs,binaryWordValue]

theorem SignedBinaryWord.positiveBits_length (a : SignedBinaryWord) :
    a.positiveBits.length≤a.bits.length := by
  cases hs : a.negative <;> simp [positiveBits,hs]

end CircuitRecursion
