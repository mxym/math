import EffectiveEncoding.FullyInputNativeExtraction

open CircuitRecursion EffectiveEncoding

-- One real visited input-cache leaf; both numerical and list-read records
-- are returned by that same invocation. No large synthesis is evaluated.
#eval let cache : NativeCacheEnvironment 0 0 :=
        ⟨List.Vector.nil,List.Vector.ofFn (fun _ => wordPacketOne)⟩
      let run:=(InputPacketExpression.input NativeCacheLabel.target 0).inputRun cache
      (run.numerical.value.denominator,run.reads.length,
        (run.reads.map NativeCacheInputRead.actions).sum,run.numerical.trace.booleanActions)
