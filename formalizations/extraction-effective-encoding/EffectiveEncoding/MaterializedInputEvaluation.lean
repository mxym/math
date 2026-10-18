import EffectiveEncoding.FullyMaterializedInputExtraction

open CircuitRecursion EffectiveEncoding

#eval let mapped:=wireLabelProgram (0 : Fin 2) ([0,1,0] : List (Fin 2))
      let copied:=listAppendProgram mapped.word []
      (mapped.word.length,mapped.trace.actions,copied.value.length,copied.trace.actions)

#eval let entry : Fin 0 → NativePacketDataOracle:=fun i => Fin.elim0 i
      let run:=fullyMaterializedInputRun entry (fun i => Fin.elim0 i) (fun _ : Fin 1 => []) 0 0 0
      (run.compilation.value.word.length,run.compilation.trace.actions)
