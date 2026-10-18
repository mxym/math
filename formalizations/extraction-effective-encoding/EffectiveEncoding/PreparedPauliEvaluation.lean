import EffectiveEncoding.PreparedNativeExtraction

#print EffectiveEncoding.preparePauliPlan
#print EffectiveEncoding.preparedNativeOccupationRun
#eval (EffectiveEncoding.preparedMaskTable (by decide : 0<2)).length
#eval EffectiveEncoding.preparedMaskTablePayload (EffectiveEncoding.preparedMaskTable (by decide : 0<2))
#eval (EffectiveEncoding.preparedSwapCode (EffectiveEncoding.preparedMaskTable (by decide : 0<1))
  (fun _ => false) (fun _ => true)).length
