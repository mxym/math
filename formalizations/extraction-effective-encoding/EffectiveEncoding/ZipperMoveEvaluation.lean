import EffectiveEncoding.PackedZipperMove

open CircuitRecursion EffectiveEncoding

-- A tiny actual zipper loop: the first difference is preserved as pivot,
-- the later difference is moved, and only needed states are reconstructed.
#eval let x : PackedBits 3:=⟨[true,false,true],rfl⟩
  let y : PackedBits 3:=⟨[true,true,false],rfl⟩
  let decision:=packedGrayScanProgram x y
  let r:=retainedPackedZipperMoveProgram [] x y decision rfl
  (r.program.word.length,r.program.final.toList,r.program.trace.actions,
    r.program.assemblies.map ZipperPackedUpdateResult.actions,r.program.actions)
