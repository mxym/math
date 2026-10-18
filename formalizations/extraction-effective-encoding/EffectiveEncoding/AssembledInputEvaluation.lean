import EffectiveEncoding.FullyAssembledInputExtraction

open CircuitRecursion EffectiveEncoding

-- Tiny depth-zero assembled recursion on a stored one-packet cache.
#eval let cache : NativeCacheEnvironment 0 0 :=
        ⟨List.Vector.nil,List.Vector.ofFn (fun _ => wordPacketOne)⟩
      let r:=assembledInputPairWord cache inputGateOracle (fun i => Fin.elim0 i)
        (fun _ : Fin 1 => []) 0 (inputTargetOracle 0)
      (r.program.word.length,r.trace.actions,r.trace.inverseCalls,r.program.readActions)
