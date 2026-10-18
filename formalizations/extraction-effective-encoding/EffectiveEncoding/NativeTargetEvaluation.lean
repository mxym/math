import EffectiveEncoding.FullyNativeExtraction

#print EffectiveEncoding.NativeSingleInput.packetExpression
#print EffectiveEncoding.nativeTargetDescriptorRun
#print EffectiveEncoding.fullyNativeExtractionRun
#eval ((EffectiveEncoding.prepareNativeSingleInput .hadamard).packetProgram 0).value.denominator
#eval (((EffectiveEncoding.prepareNativeSingleInput .hadamard).packetProgram 0).value.numerators.get 1).bits
