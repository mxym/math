import EffectiveEncoding.PackedGrayDecision

open CircuitRecursion EffectiveEncoding

-- Tiny stored-list scan only, without any descriptor/large word evaluation.
#eval let x : PackedBits 3:=⟨[true,false,true],rfl⟩
  let y : PackedBits 3:=⟨[true,true,false],rfl⟩
  let different:=packedGrayScanProgram x y
  let equal:=packedGrayScanProgram x x
  ((different.scan.first.map Fin.val,different.scan.others.map Fin.val,different.actions,
    different.left.bits,different.right.bits),
   (equal.scan.first.map Fin.val,equal.scan.others.map Fin.val,equal.actions))
