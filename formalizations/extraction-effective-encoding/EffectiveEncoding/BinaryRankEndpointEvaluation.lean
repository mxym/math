import EffectiveEncoding.NativeBinaryRankEndpoints

open EffectiveEncoding
#eval let r:=nativeBinaryRankProgram 2 (1,0,0) (by decide)
      (r.output.bits.toList,r.encodingActions)
