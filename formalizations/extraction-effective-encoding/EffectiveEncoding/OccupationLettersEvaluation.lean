import EffectiveEncoding.AcceptedOccupationLetters

open CircuitRecursion EffectiveEncoding

-- Tiny actual enumeration/selector smoke check, not a large descriptor eval.
#eval let r:=acceptedOccupationTableProgram 1
  (r.items.map (fun a => (a.native.1,a.letters.items.map Fin.val,a.letters.actions)),r.actions)
