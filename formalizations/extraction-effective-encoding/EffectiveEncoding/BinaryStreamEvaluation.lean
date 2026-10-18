import EffectiveEncoding.SerializedInputExtraction

open CircuitRecursion EffectiveEncoding

#eval let gates : List (LabelGate 2 2):=[.single 0 1,.cnot 0 1 (by decide),.single 1 0]
      let encoded:=binaryLabelStream gates
      (encoded.bits,encoded.trace.actions,
        (readBinaryLabelStream 2 2 (encoded.bits++[true,false,true])).map
          (fun p => (p.1.length,p.2)))

#eval let entry : Fin 0 → NativePacketDataOracle:=fun i => Fin.elim0 i
      let r:=serializedInputRun entry (fun i => Fin.elim0 i) (fun _ : Fin 1 => []) 0 0 0
      (r.stream.bits,r.stream.trace.actions,r.decoded.length)
