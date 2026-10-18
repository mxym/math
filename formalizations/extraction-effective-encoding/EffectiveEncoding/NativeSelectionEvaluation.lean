import EffectiveEncoding.NativeRankExtraction

#print EffectiveEncoding.nativeSelected
#print EffectiveEncoding.nativeOccupiedFintype
#print EffectiveEncoding.nativeOccupiedPivot
#print EffectiveEncoding.nativeOccupationTable

#eval ((EffectiveEncoding.nativeOccupiedFintype
  (show EffectiveEncoding.NativeOccupation 3 from ⟨(1,0,1),by decide⟩)).elems.sort (·≤·)).map (fun a => a.1.val)
#eval (EffectiveEncoding.nativeOccupiedPivot
  (show EffectiveEncoding.NativeOccupation 3 from ⟨(0,1,1),by decide⟩)).1.val
#eval (EffectiveEncoding.nativeOccupationTable 1).map Subtype.val

#print EffectiveEncoding.nativeMass
#print EffectiveEncoding.nativeBranchEndpoint
#print EffectiveEncoding.nativeNextEndpoint
set_option pp.explicit true in
#print EffectiveEncoding.nativeBranchRun
#print EffectiveEncoding.nativeOccupationRun
#print EffectiveEncoding.nativeRankExtractionRun
#eval (EffectiveEncoding.nativeBranchRun
  (show EffectiveEncoding.NativeOccupation 1 from ⟨(0,1,0),by decide⟩)).word.length
#eval (EffectiveEncoding.nativePivotEndpoint
  (show EffectiveEncoding.NativeOccupation 1 from ⟨(0,1,0),by decide⟩)).point.toList
