import EffectiveEncoding.BinaryGeneratedRank

open CircuitCompletion CircuitRecursion
namespace EffectiveEncodingBinaryCandidateEvaluation

-- One genuinely executed tiny endpoint, including every rejected candidate.
#eval let r:=EffectiveEncoding.binaryGeneratedRankProgram 1 (1,0,0) (by decide)
  (r.index.val,r.candidates.range.items.map EffectiveEncoding.SavedCountWord.count,
    r.candidates.filtered.tests.length,r.candidates.filtered.items.map EffectiveEncoding.savedTripleCounts,
    r.output.bits.toList,r.actions)

end EffectiveEncodingBinaryCandidateEvaluation
