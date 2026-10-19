import EffectiveEncoding.MaskedSerializedRun

open CircuitRecursion EffectiveEncoding

-- One genuine four-mask run, exercising stored increment/copy and plan construction.
#eval let r:=binaryMaskPlanProgram (by decide : 0<2)
      (r.outputs.map (fun output => output.bits.toList),r.plans.length,r.actions)
