import APPT.Finite18Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term3Row04 : CoefficientMerge.Poly := [(428, 2), (429, 2), (430, 2), (431, 2), (752, 2), (753, 2), (754, 2), (755, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2), (1400, 2), (1401, 2), (1402, 2), (1403, 2), (1724, 2), (1725, 2), (1726, 2), (1727, 2), (1742, 2), (1743, 2), (1744, 2), (1745, 2), (1760, 2), (1761, 2), (1762, 2), (1763, 2), (1778, 2), (1779, 2), (1780, 2), (1781, 2), (1796, 2), (1797, 2), (1798, 2), (1799, 2), (1814, 2), (1815, 2), (1816, 2), (1817, 2), (1832, 2), (1833, 2), (1834, 2), (1835, 2), (1850, 2), (1851, 2), (1852, 2), (1853, 2), (1868, 2), (1869, 2), (1870, 2), (1871, 2), (1886, 2), (1887, 2), (1888, 2), (1889, 2)]
theorem det04Term3Row04_decode : SparsePolynomial.decodeCubic 18 det04Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row04 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row05 : CoefficientMerge.Poly := [(446, 2), (447, 2), (448, 2), (449, 2), (770, 2), (771, 2), (772, 2), (773, 2), (1094, 2), (1095, 2), (1096, 2), (1097, 2), (1418, 2), (1419, 2), (1420, 2), (1421, 2), (1742, 2), (1743, 2), (1744, 2), (1745, 2), (2066, 2), (2067, 2), (2068, 2), (2069, 2), (2084, 2), (2085, 2), (2086, 2), (2087, 2), (2102, 2), (2103, 2), (2104, 2), (2105, 2), (2120, 2), (2121, 2), (2122, 2), (2123, 2), (2138, 2), (2139, 2), (2140, 2), (2141, 2), (2156, 2), (2157, 2), (2158, 2), (2159, 2), (2174, 2), (2175, 2), (2176, 2), (2177, 2), (2192, 2), (2193, 2), (2194, 2), (2195, 2), (2210, 2), (2211, 2), (2212, 2), (2213, 2)]
theorem det04Term3Row05_decode : SparsePolynomial.decodeCubic 18 det04Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row05 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row06 : CoefficientMerge.Poly := [(464, 2), (465, 2), (466, 2), (467, 2), (788, 2), (789, 2), (790, 2), (791, 2), (1112, 2), (1113, 2), (1114, 2), (1115, 2), (1436, 2), (1437, 2), (1438, 2), (1439, 2), (1760, 2), (1761, 2), (1762, 2), (1763, 2), (2084, 2), (2085, 2), (2086, 2), (2087, 2), (2408, 2), (2409, 2), (2410, 2), (2411, 2), (2426, 2), (2427, 2), (2428, 2), (2429, 2), (2444, 2), (2445, 2), (2446, 2), (2447, 2), (2462, 2), (2463, 2), (2464, 2), (2465, 2), (2480, 2), (2481, 2), (2482, 2), (2483, 2), (2498, 2), (2499, 2), (2500, 2), (2501, 2), (2516, 2), (2517, 2), (2518, 2), (2519, 2), (2534, 2), (2535, 2), (2536, 2), (2537, 2)]
theorem det04Term3Row06_decode : SparsePolynomial.decodeCubic 18 det04Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row06 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row07 : CoefficientMerge.Poly := [(482, 2), (483, 2), (484, 2), (485, 2), (806, 2), (807, 2), (808, 2), (809, 2), (1130, 2), (1131, 2), (1132, 2), (1133, 2), (1454, 2), (1455, 2), (1456, 2), (1457, 2), (1778, 2), (1779, 2), (1780, 2), (1781, 2), (2102, 2), (2103, 2), (2104, 2), (2105, 2), (2426, 2), (2427, 2), (2428, 2), (2429, 2), (2750, 2), (2751, 2), (2752, 2), (2753, 2), (2768, 2), (2769, 2), (2770, 2), (2771, 2), (2786, 2), (2787, 2), (2788, 2), (2789, 2), (2804, 2), (2805, 2), (2806, 2), (2807, 2), (2822, 2), (2823, 2), (2824, 2), (2825, 2), (2840, 2), (2841, 2), (2842, 2), (2843, 2), (2858, 2), (2859, 2), (2860, 2), (2861, 2)]
theorem det04Term3Row07_decode : SparsePolynomial.decodeCubic 18 det04Term3Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row07 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
