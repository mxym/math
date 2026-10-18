import EffectiveEncoding.CandidateSerializedPolynomial

open CircuitRecursion EffectiveEncoding

-- New actual terminal smoke: no library/provider value can be queried.
#eval let entry : Fin 0 → NativePacketDataOracle:=fun i => Fin.elim0 i
      let r:=candidateSerializedRun entry (fun i => Fin.elim0 i) (fun _ : Fin 1 => []) 0 0 0
      (r.precision,r.generation.word.length,r.compilation.value.programs.length,
        r.stream.bits,r.decoded.length,r.accountedPrimitiveActions)
