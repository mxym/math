import EffectiveEncoding.PreparedNativeInputs

#print EffectiveEncoding.unaryWordEncoding
#print EffectiveEncoding.nativeMergeInputProgram
#print EffectiveEncoding.prepareNativeSingleInput
#eval (EffectiveEncoding.unaryWordEncoding 13).bits
#eval (EffectiveEncoding.nativeMergeInputProgram 3 5 (by decide)).cosineInput.numerator.bits
#eval (EffectiveEncoding.nativeMergeInputProgram 3 5 (by decide)).cosineInput.denominator
#eval (EffectiveEncoding.nativeMergeInputProgram 3 5 (by decide)).leftEncoding.trace.incrementCount+
  (EffectiveEncoding.nativeMergeInputProgram 3 5 (by decide)).rightEncoding.trace.incrementCount
