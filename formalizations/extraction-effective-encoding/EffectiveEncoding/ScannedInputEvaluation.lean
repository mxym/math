import EffectiveEncoding.FullyScannedInputExtraction
import EffectiveEncoding.NativeBooleanRankEvaluation

open EffectiveEncoding
#eval let r:=scannedNativeDescriptorRun 0
      (r.result.result.word.length,r.scans.length,r.scanActions)
