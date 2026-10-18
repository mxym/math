import EffectiveEncoding.BinaryNativeExtraction
import EffectiveEncoding.BinaryRankEndpointEvaluation

open EffectiveEncoding
#eval let r:=binaryNativeDescriptorRun 0
      (r.result.word.length,r.programs.length,r.encodingActions)
