import EffectiveEncoding.FullyRetainedNativeExtraction

open CircuitRecursion EffectiveEncoding

-- Two actual cache requests retain their computed packet data and primitive
-- traces; this tiny example does not execute a large numerical synthesis.
#eval (buildNativeTargetPrograms NativeSingleInput.yBasis 1).toList.map
  (fun run => (run.value.denominator,run.trace.booleanActions))
