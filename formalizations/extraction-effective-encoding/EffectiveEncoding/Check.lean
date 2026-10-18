import EffectiveEncoding.Extraction
import EffectiveEncoding.AngleEvaluation

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


/-- Small runtime smoke checks confirm executable code generation in
addition to the universally quantified kernel proofs above. -/
#eval (occupations 2).map toTriple
#eval ((extractionCode 0).length,(extractionCode 1).length,(extractionCode 2).length)
#eval ((AngleCode.mk (.merge 1 1 2) false 3).cosOracle 5,
  (AngleCode.mk (.merge 1 1 2) false 3).sinOracle 5)

end EffectiveEncoding

