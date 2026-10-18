import EffectiveEncoding.NativeBooleanRankProgram

open EffectiveEncoding
#eval let r:=nativeBooleanRankProgram 2 (1,0,0) (by decide)
      (r.ranked.index.val,r.scan.tests.length,r.booleanActions)
