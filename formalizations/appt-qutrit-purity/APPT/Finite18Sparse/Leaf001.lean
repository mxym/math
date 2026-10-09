import APPT.Finite18Sparse.Base05
import APPT.Finite18Sparse.Base06
import APPT.Finite18Sparse.Base07
import APPT.Finite18Sparse.Base08
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0015 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,0,12], -2), ([0,0,13], -2), ([0,0,14], -2), ([0,0,15], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -2), ([0,1,10], -2), ([0,1,11], -2), ([0,1,12], -2), ([0,1,13], -2), ([0,1,14], -2), ([0,1,15], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,2,7], -2), ([0,2,8], -2), ([0,2,9], -2), ([0,2,10], -2), ([0,2,11], -2), ([0,2,12], -2), ([0,2,13], -2), ([0,2,14], -2), ([0,2,15], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,3,7], -2), ([0,3,8], -2), ([0,3,9], -2), ([0,3,10], -2), ([0,3,11], -2), ([0,3,12], -2), ([0,3,13], -2), ([0,3,14], -2), ([0,3,15], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,4,7], -2), ([0,4,8], -2), ([0,4,9], -2), ([0,4,10], -2), ([0,4,11], -2), ([0,4,12], -2), ([0,4,13], -2), ([0,4,14], -2), ([0,4,15], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,7], -2), ([0,5,8], -2), ([0,5,9], -2), ([0,5,10], -2), ([0,5,11], -2), ([0,5,12], -2), ([0,5,13], -2), ([0,5,14], -2), ([0,5,15], -2), ([0,6,6], -1), ([0,6,7], -2), ([0,6,8], -2), ([0,6,9], -2), ([0,6,10], -2), ([0,6,11], -2), ([0,6,12], -2), ([0,6,13], -2), ([0,6,14], -2), ([0,6,15], -2), ([0,7,7], -1), ([0,7,8], -2), ([0,7,9], -2), ([0,7,10], -2), ([0,7,11], -2), ([0,7,12], -2), ([0,7,13], -2), ([0,7,14], -2), ([0,7,15], -2), ([0,8,8], -1), ([0,8,9], -2), ([0,8,10], -2), ([0,8,11], -2), ([0,8,12], -2), ([0,8,13], -2), ([0,8,14], -2), ([0,8,15], -2), ([0,9,9], -1), ([0,9,10], -2), ([0,9,11], -2), ([0,9,12], -2), ([0,9,13], -2), ([0,9,14], -2), ([0,9,15], -2), ([0,10,10], -1), ([0,10,11], -2), ([0,10,12], -2), ([0,10,13], -2), ([0,10,14], -2), ([0,10,15], -2), ([0,11,11], -1), ([0,11,12], -2), ([0,11,13], -2), ([0,11,14], -2), ([0,11,15], -2), ([0,12,12], -1), ([0,12,13], -2), ([0,12,14], -2), ([0,12,15], -2), ([0,13,13], -1), ([0,13,14], -2), ([0,13,15], -2), ([0,14,14], -1), ([0,14,15], -2), ([0,14,17], 4), ([0,15,15], -1), ([0,15,17], 4), ([0,16,17], 4), ([0,17,17], 4)]
theorem atom0015_data : atom0015 = SparsePolynomial.monoTimes [0] 1 base05 := by decide +kernel
theorem eval_atom0015 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0015 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0015_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120637440 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0015Coded : CoefficientMerge.Poly := [(0, -1), (1, -2), (2, -2), (3, -2), (4, -2), (5, -2), (6, -2), (7, -2), (8, -2), (9, -2), (10, -2), (11, -2), (12, -2), (13, -2), (14, -2), (15, -2), (19, -1), (20, -2), (21, -2), (22, -2), (23, -2), (24, -2), (25, -2), (26, -2), (27, -2), (28, -2), (29, -2), (30, -2), (31, -2), (32, -2), (33, -2), (38, -1), (39, -2), (40, -2), (41, -2), (42, -2), (43, -2), (44, -2), (45, -2), (46, -2), (47, -2), (48, -2), (49, -2), (50, -2), (51, -2), (57, -1), (58, -2), (59, -2), (60, -2), (61, -2), (62, -2), (63, -2), (64, -2), (65, -2), (66, -2), (67, -2), (68, -2), (69, -2), (76, -1), (77, -2), (78, -2), (79, -2), (80, -2), (81, -2), (82, -2), (83, -2), (84, -2), (85, -2), (86, -2), (87, -2), (95, -1), (96, -2), (97, -2), (98, -2), (99, -2), (100, -2), (101, -2), (102, -2), (103, -2), (104, -2), (105, -2), (114, -1), (115, -2), (116, -2), (117, -2), (118, -2), (119, -2), (120, -2), (121, -2), (122, -2), (123, -2), (133, -1), (134, -2), (135, -2), (136, -2), (137, -2), (138, -2), (139, -2), (140, -2), (141, -2), (152, -1), (153, -2), (154, -2), (155, -2), (156, -2), (157, -2), (158, -2), (159, -2), (171, -1), (172, -2), (173, -2), (174, -2), (175, -2), (176, -2), (177, -2), (190, -1), (191, -2), (192, -2), (193, -2), (194, -2), (195, -2), (209, -1), (210, -2), (211, -2), (212, -2), (213, -2), (228, -1), (229, -2), (230, -2), (231, -2), (247, -1), (248, -2), (249, -2), (266, -1), (267, -2), (269, 4), (285, -1), (287, 4), (305, 4), (323, 4)]
theorem atom0015Coded_decode : atom0015 = SparsePolynomial.decodeCubic 18 atom0015Coded := by decide +kernel
theorem atom0015Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (120637440 : Int) atom0015Coded) := by
  have h := atom0015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0016 : SparsePolynomial.Poly := [([0,0,8], -1), ([0,1,8], -2), ([0,2,8], -2), ([0,3,8], -2), ([0,4,8], -2), ([0,5,8], -2), ([0,6,8], -2), ([0,7,8], -2), ([0,8,8], -2), ([0,8,9], -2), ([0,8,10], -2), ([0,8,11], -2), ([0,8,12], -2), ([0,8,13], -2), ([0,8,14], -2), ([0,8,15], -2), ([1,1,8], -1), ([1,2,8], -2), ([1,3,8], -2), ([1,4,8], -2), ([1,5,8], -2), ([1,6,8], -2), ([1,7,8], -2), ([1,8,8], -2), ([1,8,9], -2), ([1,8,10], -2), ([1,8,11], -2), ([1,8,12], -2), ([1,8,13], -2), ([1,8,14], -2), ([1,8,15], -2), ([2,2,8], -1), ([2,3,8], -2), ([2,4,8], -2), ([2,5,8], -2), ([2,6,8], -2), ([2,7,8], -2), ([2,8,8], -2), ([2,8,9], -2), ([2,8,10], -2), ([2,8,11], -2), ([2,8,12], -2), ([2,8,13], -2), ([2,8,14], -2), ([2,8,15], -2), ([3,3,8], -1), ([3,4,8], -2), ([3,5,8], -2), ([3,6,8], -2), ([3,7,8], -2), ([3,8,8], -2), ([3,8,9], -2), ([3,8,10], -2), ([3,8,11], -2), ([3,8,12], -2), ([3,8,13], -2), ([3,8,14], -2), ([3,8,15], -2), ([4,4,8], -1), ([4,5,8], -2), ([4,6,8], -2), ([4,7,8], -2), ([4,8,8], -2), ([4,8,9], -2), ([4,8,10], -2), ([4,8,11], -2), ([4,8,12], -2), ([4,8,13], -2), ([4,8,14], -2), ([4,8,15], -2), ([5,5,8], -1), ([5,6,8], -2), ([5,7,8], -2), ([5,8,8], -2), ([5,8,9], -2), ([5,8,10], -2), ([5,8,11], -2), ([5,8,12], -2), ([5,8,13], -2), ([5,8,14], -2), ([5,8,15], -2), ([6,6,8], -1), ([6,7,8], -2), ([6,8,8], -2), ([6,8,9], -2), ([6,8,10], -2), ([6,8,11], -2), ([6,8,12], -2), ([6,8,13], -2), ([6,8,14], -2), ([6,8,15], -2), ([7,7,8], -1), ([7,8,8], -2), ([7,8,9], -2), ([7,8,10], -2), ([7,8,11], -2), ([7,8,12], -2), ([7,8,13], -2), ([7,8,14], -2), ([7,8,15], -2), ([8,8,8], -1), ([8,8,9], -2), ([8,8,10], -2), ([8,8,11], -2), ([8,8,12], -2), ([8,8,13], -2), ([8,8,14], -2), ([8,8,15], -2), ([8,9,9], -1), ([8,9,10], -2), ([8,9,11], -2), ([8,9,12], -2), ([8,9,13], -2), ([8,9,14], -2), ([8,9,15], -2), ([8,10,10], -1), ([8,10,11], -2), ([8,10,12], -2), ([8,10,13], -2), ([8,10,14], -2), ([8,10,15], -2), ([8,11,11], -1), ([8,11,12], -2), ([8,11,13], -2), ([8,11,14], -2), ([8,11,15], -2), ([8,12,12], -1), ([8,12,13], -2), ([8,12,14], -2), ([8,12,15], -2), ([8,13,13], -1), ([8,13,14], -2), ([8,13,15], -2), ([8,14,14], -1), ([8,14,15], -2), ([8,14,17], 4), ([8,15,15], -1), ([8,15,17], 4), ([8,16,17], 4), ([8,17,17], 4)]
theorem atom0016_data : atom0016 = SparsePolynomial.monoTimes [8] 1 base05 := by decide +kernel
theorem eval_atom0016 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0016 = (minorB (outer g) 0 1 * g 8) := by
  rw [atom0016_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0016_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51233280 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016Coded : CoefficientMerge.Poly := [(8, -1), (26, -2), (44, -2), (62, -2), (80, -2), (98, -2), (116, -2), (134, -2), (152, -2), (153, -2), (154, -2), (155, -2), (156, -2), (157, -2), (158, -2), (159, -2), (350, -1), (368, -2), (386, -2), (404, -2), (422, -2), (440, -2), (458, -2), (476, -2), (477, -2), (478, -2), (479, -2), (480, -2), (481, -2), (482, -2), (483, -2), (692, -1), (710, -2), (728, -2), (746, -2), (764, -2), (782, -2), (800, -2), (801, -2), (802, -2), (803, -2), (804, -2), (805, -2), (806, -2), (807, -2), (1034, -1), (1052, -2), (1070, -2), (1088, -2), (1106, -2), (1124, -2), (1125, -2), (1126, -2), (1127, -2), (1128, -2), (1129, -2), (1130, -2), (1131, -2), (1376, -1), (1394, -2), (1412, -2), (1430, -2), (1448, -2), (1449, -2), (1450, -2), (1451, -2), (1452, -2), (1453, -2), (1454, -2), (1455, -2), (1718, -1), (1736, -2), (1754, -2), (1772, -2), (1773, -2), (1774, -2), (1775, -2), (1776, -2), (1777, -2), (1778, -2), (1779, -2), (2060, -1), (2078, -2), (2096, -2), (2097, -2), (2098, -2), (2099, -2), (2100, -2), (2101, -2), (2102, -2), (2103, -2), (2402, -1), (2420, -2), (2421, -2), (2422, -2), (2423, -2), (2424, -2), (2425, -2), (2426, -2), (2427, -2), (2744, -1), (2745, -2), (2746, -2), (2747, -2), (2748, -2), (2749, -2), (2750, -2), (2751, -2), (2763, -1), (2764, -2), (2765, -2), (2766, -2), (2767, -2), (2768, -2), (2769, -2), (2782, -1), (2783, -2), (2784, -2), (2785, -2), (2786, -2), (2787, -2), (2801, -1), (2802, -2), (2803, -2), (2804, -2), (2805, -2), (2820, -1), (2821, -2), (2822, -2), (2823, -2), (2839, -1), (2840, -2), (2841, -2), (2858, -1), (2859, -2), (2861, 4), (2877, -1), (2879, 4), (2897, 4), (2915, 4)]
theorem atom0016Coded_decode : atom0016 = SparsePolynomial.decodeCubic 18 atom0016Coded := by decide +kernel
theorem atom0016Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (51233280 : Int) atom0016Coded) := by
  have h := atom0016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0017 : SparsePolynomial.Poly := [([0,0,9], -1), ([0,1,9], -2), ([0,2,9], -2), ([0,3,9], -2), ([0,4,9], -2), ([0,5,9], -2), ([0,6,9], -2), ([0,7,9], -2), ([0,8,9], -2), ([0,9,9], -2), ([0,9,10], -2), ([0,9,11], -2), ([0,9,12], -2), ([0,9,13], -2), ([0,9,14], -2), ([0,9,15], -2), ([1,1,9], -1), ([1,2,9], -2), ([1,3,9], -2), ([1,4,9], -2), ([1,5,9], -2), ([1,6,9], -2), ([1,7,9], -2), ([1,8,9], -2), ([1,9,9], -2), ([1,9,10], -2), ([1,9,11], -2), ([1,9,12], -2), ([1,9,13], -2), ([1,9,14], -2), ([1,9,15], -2), ([2,2,9], -1), ([2,3,9], -2), ([2,4,9], -2), ([2,5,9], -2), ([2,6,9], -2), ([2,7,9], -2), ([2,8,9], -2), ([2,9,9], -2), ([2,9,10], -2), ([2,9,11], -2), ([2,9,12], -2), ([2,9,13], -2), ([2,9,14], -2), ([2,9,15], -2), ([3,3,9], -1), ([3,4,9], -2), ([3,5,9], -2), ([3,6,9], -2), ([3,7,9], -2), ([3,8,9], -2), ([3,9,9], -2), ([3,9,10], -2), ([3,9,11], -2), ([3,9,12], -2), ([3,9,13], -2), ([3,9,14], -2), ([3,9,15], -2), ([4,4,9], -1), ([4,5,9], -2), ([4,6,9], -2), ([4,7,9], -2), ([4,8,9], -2), ([4,9,9], -2), ([4,9,10], -2), ([4,9,11], -2), ([4,9,12], -2), ([4,9,13], -2), ([4,9,14], -2), ([4,9,15], -2), ([5,5,9], -1), ([5,6,9], -2), ([5,7,9], -2), ([5,8,9], -2), ([5,9,9], -2), ([5,9,10], -2), ([5,9,11], -2), ([5,9,12], -2), ([5,9,13], -2), ([5,9,14], -2), ([5,9,15], -2), ([6,6,9], -1), ([6,7,9], -2), ([6,8,9], -2), ([6,9,9], -2), ([6,9,10], -2), ([6,9,11], -2), ([6,9,12], -2), ([6,9,13], -2), ([6,9,14], -2), ([6,9,15], -2), ([7,7,9], -1), ([7,8,9], -2), ([7,9,9], -2), ([7,9,10], -2), ([7,9,11], -2), ([7,9,12], -2), ([7,9,13], -2), ([7,9,14], -2), ([7,9,15], -2), ([8,8,9], -1), ([8,9,9], -2), ([8,9,10], -2), ([8,9,11], -2), ([8,9,12], -2), ([8,9,13], -2), ([8,9,14], -2), ([8,9,15], -2), ([9,9,9], -1), ([9,9,10], -2), ([9,9,11], -2), ([9,9,12], -2), ([9,9,13], -2), ([9,9,14], -2), ([9,9,15], -2), ([9,10,10], -1), ([9,10,11], -2), ([9,10,12], -2), ([9,10,13], -2), ([9,10,14], -2), ([9,10,15], -2), ([9,11,11], -1), ([9,11,12], -2), ([9,11,13], -2), ([9,11,14], -2), ([9,11,15], -2), ([9,12,12], -1), ([9,12,13], -2), ([9,12,14], -2), ([9,12,15], -2), ([9,13,13], -1), ([9,13,14], -2), ([9,13,15], -2), ([9,14,14], -1), ([9,14,15], -2), ([9,14,17], 4), ([9,15,15], -1), ([9,15,17], 4), ([9,16,17], 4), ([9,17,17], 4)]
theorem atom0017_data : atom0017 = SparsePolynomial.monoTimes [9] 1 base05 := by decide +kernel
theorem eval_atom0017 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0017 = (minorB (outer g) 0 1 * g 9) := by
  rw [atom0017_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0017_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42201600 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017Coded : CoefficientMerge.Poly := [(9, -1), (27, -2), (45, -2), (63, -2), (81, -2), (99, -2), (117, -2), (135, -2), (153, -2), (171, -2), (172, -2), (173, -2), (174, -2), (175, -2), (176, -2), (177, -2), (351, -1), (369, -2), (387, -2), (405, -2), (423, -2), (441, -2), (459, -2), (477, -2), (495, -2), (496, -2), (497, -2), (498, -2), (499, -2), (500, -2), (501, -2), (693, -1), (711, -2), (729, -2), (747, -2), (765, -2), (783, -2), (801, -2), (819, -2), (820, -2), (821, -2), (822, -2), (823, -2), (824, -2), (825, -2), (1035, -1), (1053, -2), (1071, -2), (1089, -2), (1107, -2), (1125, -2), (1143, -2), (1144, -2), (1145, -2), (1146, -2), (1147, -2), (1148, -2), (1149, -2), (1377, -1), (1395, -2), (1413, -2), (1431, -2), (1449, -2), (1467, -2), (1468, -2), (1469, -2), (1470, -2), (1471, -2), (1472, -2), (1473, -2), (1719, -1), (1737, -2), (1755, -2), (1773, -2), (1791, -2), (1792, -2), (1793, -2), (1794, -2), (1795, -2), (1796, -2), (1797, -2), (2061, -1), (2079, -2), (2097, -2), (2115, -2), (2116, -2), (2117, -2), (2118, -2), (2119, -2), (2120, -2), (2121, -2), (2403, -1), (2421, -2), (2439, -2), (2440, -2), (2441, -2), (2442, -2), (2443, -2), (2444, -2), (2445, -2), (2745, -1), (2763, -2), (2764, -2), (2765, -2), (2766, -2), (2767, -2), (2768, -2), (2769, -2), (3087, -1), (3088, -2), (3089, -2), (3090, -2), (3091, -2), (3092, -2), (3093, -2), (3106, -1), (3107, -2), (3108, -2), (3109, -2), (3110, -2), (3111, -2), (3125, -1), (3126, -2), (3127, -2), (3128, -2), (3129, -2), (3144, -1), (3145, -2), (3146, -2), (3147, -2), (3163, -1), (3164, -2), (3165, -2), (3182, -1), (3183, -2), (3185, 4), (3201, -1), (3203, 4), (3221, 4), (3239, 4)]
theorem atom0017Coded_decode : atom0017 = SparsePolynomial.decodeCubic 18 atom0017Coded := by decide +kernel
theorem atom0017Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (42201600 : Int) atom0017Coded) := by
  have h := atom0017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0018 : SparsePolynomial.Poly := [([0,0,10], -1), ([0,1,10], -2), ([0,2,10], -2), ([0,3,10], -2), ([0,4,10], -2), ([0,5,10], -2), ([0,6,10], -2), ([0,7,10], -2), ([0,8,10], -2), ([0,9,10], -2), ([0,10,10], -2), ([0,10,11], -2), ([0,10,12], -2), ([0,10,13], -2), ([0,10,14], -2), ([0,10,15], -2), ([1,1,10], -1), ([1,2,10], -2), ([1,3,10], -2), ([1,4,10], -2), ([1,5,10], -2), ([1,6,10], -2), ([1,7,10], -2), ([1,8,10], -2), ([1,9,10], -2), ([1,10,10], -2), ([1,10,11], -2), ([1,10,12], -2), ([1,10,13], -2), ([1,10,14], -2), ([1,10,15], -2), ([2,2,10], -1), ([2,3,10], -2), ([2,4,10], -2), ([2,5,10], -2), ([2,6,10], -2), ([2,7,10], -2), ([2,8,10], -2), ([2,9,10], -2), ([2,10,10], -2), ([2,10,11], -2), ([2,10,12], -2), ([2,10,13], -2), ([2,10,14], -2), ([2,10,15], -2), ([3,3,10], -1), ([3,4,10], -2), ([3,5,10], -2), ([3,6,10], -2), ([3,7,10], -2), ([3,8,10], -2), ([3,9,10], -2), ([3,10,10], -2), ([3,10,11], -2), ([3,10,12], -2), ([3,10,13], -2), ([3,10,14], -2), ([3,10,15], -2), ([4,4,10], -1), ([4,5,10], -2), ([4,6,10], -2), ([4,7,10], -2), ([4,8,10], -2), ([4,9,10], -2), ([4,10,10], -2), ([4,10,11], -2), ([4,10,12], -2), ([4,10,13], -2), ([4,10,14], -2), ([4,10,15], -2), ([5,5,10], -1), ([5,6,10], -2), ([5,7,10], -2), ([5,8,10], -2), ([5,9,10], -2), ([5,10,10], -2), ([5,10,11], -2), ([5,10,12], -2), ([5,10,13], -2), ([5,10,14], -2), ([5,10,15], -2), ([6,6,10], -1), ([6,7,10], -2), ([6,8,10], -2), ([6,9,10], -2), ([6,10,10], -2), ([6,10,11], -2), ([6,10,12], -2), ([6,10,13], -2), ([6,10,14], -2), ([6,10,15], -2), ([7,7,10], -1), ([7,8,10], -2), ([7,9,10], -2), ([7,10,10], -2), ([7,10,11], -2), ([7,10,12], -2), ([7,10,13], -2), ([7,10,14], -2), ([7,10,15], -2), ([8,8,10], -1), ([8,9,10], -2), ([8,10,10], -2), ([8,10,11], -2), ([8,10,12], -2), ([8,10,13], -2), ([8,10,14], -2), ([8,10,15], -2), ([9,9,10], -1), ([9,10,10], -2), ([9,10,11], -2), ([9,10,12], -2), ([9,10,13], -2), ([9,10,14], -2), ([9,10,15], -2), ([10,10,10], -1), ([10,10,11], -2), ([10,10,12], -2), ([10,10,13], -2), ([10,10,14], -2), ([10,10,15], -2), ([10,11,11], -1), ([10,11,12], -2), ([10,11,13], -2), ([10,11,14], -2), ([10,11,15], -2), ([10,12,12], -1), ([10,12,13], -2), ([10,12,14], -2), ([10,12,15], -2), ([10,13,13], -1), ([10,13,14], -2), ([10,13,15], -2), ([10,14,14], -1), ([10,14,15], -2), ([10,14,17], 4), ([10,15,15], -1), ([10,15,17], 4), ([10,16,17], 4), ([10,17,17], 4)]
theorem atom0018_data : atom0018 = SparsePolynomial.monoTimes [10] 1 base05 := by decide +kernel
theorem eval_atom0018 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = (minorB (outer g) 0 1 * g 10) := by
  rw [atom0018_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58329600 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018Coded : CoefficientMerge.Poly := [(10, -1), (28, -2), (46, -2), (64, -2), (82, -2), (100, -2), (118, -2), (136, -2), (154, -2), (172, -2), (190, -2), (191, -2), (192, -2), (193, -2), (194, -2), (195, -2), (352, -1), (370, -2), (388, -2), (406, -2), (424, -2), (442, -2), (460, -2), (478, -2), (496, -2), (514, -2), (515, -2), (516, -2), (517, -2), (518, -2), (519, -2), (694, -1), (712, -2), (730, -2), (748, -2), (766, -2), (784, -2), (802, -2), (820, -2), (838, -2), (839, -2), (840, -2), (841, -2), (842, -2), (843, -2), (1036, -1), (1054, -2), (1072, -2), (1090, -2), (1108, -2), (1126, -2), (1144, -2), (1162, -2), (1163, -2), (1164, -2), (1165, -2), (1166, -2), (1167, -2), (1378, -1), (1396, -2), (1414, -2), (1432, -2), (1450, -2), (1468, -2), (1486, -2), (1487, -2), (1488, -2), (1489, -2), (1490, -2), (1491, -2), (1720, -1), (1738, -2), (1756, -2), (1774, -2), (1792, -2), (1810, -2), (1811, -2), (1812, -2), (1813, -2), (1814, -2), (1815, -2), (2062, -1), (2080, -2), (2098, -2), (2116, -2), (2134, -2), (2135, -2), (2136, -2), (2137, -2), (2138, -2), (2139, -2), (2404, -1), (2422, -2), (2440, -2), (2458, -2), (2459, -2), (2460, -2), (2461, -2), (2462, -2), (2463, -2), (2746, -1), (2764, -2), (2782, -2), (2783, -2), (2784, -2), (2785, -2), (2786, -2), (2787, -2), (3088, -1), (3106, -2), (3107, -2), (3108, -2), (3109, -2), (3110, -2), (3111, -2), (3430, -1), (3431, -2), (3432, -2), (3433, -2), (3434, -2), (3435, -2), (3449, -1), (3450, -2), (3451, -2), (3452, -2), (3453, -2), (3468, -1), (3469, -2), (3470, -2), (3471, -2), (3487, -1), (3488, -2), (3489, -2), (3506, -1), (3507, -2), (3509, 4), (3525, -1), (3527, 4), (3545, 4), (3563, 4)]
theorem atom0018Coded_decode : atom0018 = SparsePolynomial.decodeCubic 18 atom0018Coded := by decide +kernel
theorem atom0018Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (58329600 : Int) atom0018Coded) := by
  have h := atom0018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0019 : SparsePolynomial.Poly := [([0,0,17], -2), ([0,1,17], -2), ([0,2,17], -2), ([0,3,17], -2), ([0,4,17], -2), ([0,5,17], -2), ([0,6,17], -2), ([0,7,17], -2), ([0,8,17], -2), ([0,9,17], -2), ([0,10,17], -2), ([0,11,17], -2), ([0,12,17], -2), ([0,13,17], -2), ([0,16,17], 2), ([0,17,17], 4)]
theorem atom0019_data : atom0019 = SparsePolynomial.monoTimes [0,17] 1 base06 := by decide +kernel
theorem eval_atom0019 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0019 = (quadB (outer g) ![1,1,0] * g 0 * g 17) := by
  rw [atom0019_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0019_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175472640 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019Coded : CoefficientMerge.Poly := [(17, -2), (35, -2), (53, -2), (71, -2), (89, -2), (107, -2), (125, -2), (143, -2), (161, -2), (179, -2), (197, -2), (215, -2), (233, -2), (251, -2), (305, 2), (323, 4)]
theorem atom0019Coded_decode : atom0019 = SparsePolynomial.decodeCubic 18 atom0019Coded := by decide +kernel
theorem atom0019Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (175472640 : Int) atom0019Coded) := by
  have h := atom0019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0020 : SparsePolynomial.Poly := [([0,2,16], -4), ([1,2,16], -8), ([2,2,16], -16), ([2,3,16], -16), ([2,4,16], -16), ([2,5,16], -16), ([2,6,16], -16), ([2,7,16], -16), ([2,8,16], -16), ([2,9,16], -16), ([2,10,16], -16), ([2,11,16], -16), ([2,12,16], -8), ([2,14,16], 8), ([2,15,16], 12), ([2,16,16], 16), ([2,16,17], 18)]
theorem atom0020_data : atom0020 = SparsePolynomial.monoTimes [2,16] 1 base07 := by decide +kernel
theorem eval_atom0020 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0020 = (quadB (outer g) ![1,2,2] * g 2 * g 16) := by
  rw [atom0020_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0020_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93744000 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020Coded : CoefficientMerge.Poly := [(52, -4), (376, -8), (700, -16), (718, -16), (736, -16), (754, -16), (772, -16), (790, -16), (808, -16), (826, -16), (844, -16), (862, -16), (880, -8), (916, 8), (934, 12), (952, 16), (953, 18)]
theorem atom0020Coded_decode : atom0020 = SparsePolynomial.decodeCubic 18 atom0020Coded := by decide +kernel
theorem atom0020Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (93744000 : Int) atom0020Coded) := by
  have h := atom0020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0021 : SparsePolynomial.Poly := [([0,3,11], -4), ([1,3,11], -8), ([2,3,11], -16), ([3,3,11], -16), ([3,4,11], -16), ([3,5,11], -16), ([3,6,11], -16), ([3,7,11], -16), ([3,8,11], -16), ([3,9,11], -16), ([3,10,11], -16), ([3,11,11], -16), ([3,11,12], -8), ([3,11,14], 8), ([3,11,15], 12), ([3,11,16], 16), ([3,11,17], 18)]
theorem atom0021_data : atom0021 = SparsePolynomial.monoTimes [3,11] 1 base07 := by decide +kernel
theorem eval_atom0021 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0021 = (quadB (outer g) ![1,2,2] * g 3 * g 11) := by
  rw [atom0021_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0021_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10080000 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021Coded : CoefficientMerge.Poly := [(65, -4), (389, -8), (713, -16), (1037, -16), (1055, -16), (1073, -16), (1091, -16), (1109, -16), (1127, -16), (1145, -16), (1163, -16), (1181, -16), (1182, -8), (1184, 8), (1185, 12), (1186, 16), (1187, 18)]
theorem atom0021Coded_decode : atom0021 = SparsePolynomial.decodeCubic 18 atom0021Coded := by decide +kernel
theorem atom0021Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10080000 : Int) atom0021Coded) := by
  have h := atom0021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0022 : SparsePolynomial.Poly := [([0,3,13], -4), ([1,3,13], -8), ([2,3,13], -16), ([3,3,13], -16), ([3,4,13], -16), ([3,5,13], -16), ([3,6,13], -16), ([3,7,13], -16), ([3,8,13], -16), ([3,9,13], -16), ([3,10,13], -16), ([3,11,13], -16), ([3,12,13], -8), ([3,13,14], 8), ([3,13,15], 12), ([3,13,16], 16), ([3,13,17], 18)]
theorem atom0022_data : atom0022 = SparsePolynomial.monoTimes [3,13] 1 base07 := by decide +kernel
theorem eval_atom0022 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0022 = (quadB (outer g) ![1,2,2] * g 3 * g 13) := by
  rw [atom0022_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0022_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24272640 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022Coded : CoefficientMerge.Poly := [(67, -4), (391, -8), (715, -16), (1039, -16), (1057, -16), (1075, -16), (1093, -16), (1111, -16), (1129, -16), (1147, -16), (1165, -16), (1183, -16), (1201, -8), (1220, 8), (1221, 12), (1222, 16), (1223, 18)]
theorem atom0022Coded_decode : atom0022 = SparsePolynomial.decodeCubic 18 atom0022Coded := by decide +kernel
theorem atom0022Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (24272640 : Int) atom0022Coded) := by
  have h := atom0022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0023 : SparsePolynomial.Poly := [([0,3,15], -4), ([1,3,15], -8), ([2,3,15], -16), ([3,3,15], -16), ([3,4,15], -16), ([3,5,15], -16), ([3,6,15], -16), ([3,7,15], -16), ([3,8,15], -16), ([3,9,15], -16), ([3,10,15], -16), ([3,11,15], -16), ([3,12,15], -8), ([3,14,15], 8), ([3,15,15], 12), ([3,15,16], 16), ([3,15,17], 18)]
theorem atom0023_data : atom0023 = SparsePolynomial.monoTimes [3,15] 1 base07 := by decide +kernel
theorem eval_atom0023 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0023 = (quadB (outer g) ![1,2,2] * g 3 * g 15) := by
  rw [atom0023_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0023_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38465280 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023Coded : CoefficientMerge.Poly := [(69, -4), (393, -8), (717, -16), (1041, -16), (1059, -16), (1077, -16), (1095, -16), (1113, -16), (1131, -16), (1149, -16), (1167, -16), (1185, -16), (1203, -8), (1239, 8), (1257, 12), (1258, 16), (1259, 18)]
theorem atom0023Coded_decode : atom0023 = SparsePolynomial.decodeCubic 18 atom0023Coded := by decide +kernel
theorem atom0023Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (38465280 : Int) atom0023Coded) := by
  have h := atom0023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0024 : SparsePolynomial.Poly := [([0,3,16], -4), ([1,3,16], -8), ([2,3,16], -16), ([3,3,16], -16), ([3,4,16], -16), ([3,5,16], -16), ([3,6,16], -16), ([3,7,16], -16), ([3,8,16], -16), ([3,9,16], -16), ([3,10,16], -16), ([3,11,16], -16), ([3,12,16], -8), ([3,14,16], 8), ([3,15,16], 12), ([3,16,16], 16), ([3,16,17], 18)]
theorem atom0024_data : atom0024 = SparsePolynomial.monoTimes [3,16] 1 base07 := by decide +kernel
theorem eval_atom0024 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = (quadB (outer g) ![1,2,2] * g 3 * g 16) := by
  rw [atom0024_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156602880 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024Coded : CoefficientMerge.Poly := [(70, -4), (394, -8), (718, -16), (1042, -16), (1060, -16), (1078, -16), (1096, -16), (1114, -16), (1132, -16), (1150, -16), (1168, -16), (1186, -16), (1204, -8), (1240, 8), (1258, 12), (1276, 16), (1277, 18)]
theorem atom0024Coded_decode : atom0024 = SparsePolynomial.decodeCubic 18 atom0024Coded := by decide +kernel
theorem atom0024Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (156602880 : Int) atom0024Coded) := by
  have h := atom0024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0025 : SparsePolynomial.Poly := [([0,3,17], -4), ([1,3,17], -8), ([2,3,17], -16), ([3,3,17], -16), ([3,4,17], -16), ([3,5,17], -16), ([3,6,17], -16), ([3,7,17], -16), ([3,8,17], -16), ([3,9,17], -16), ([3,10,17], -16), ([3,11,17], -16), ([3,12,17], -8), ([3,14,17], 8), ([3,15,17], 12), ([3,16,17], 16), ([3,17,17], 18)]
theorem atom0025_data : atom0025 = SparsePolynomial.monoTimes [3,17] 1 base07 := by decide +kernel
theorem eval_atom0025 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0025 = (quadB (outer g) ![1,2,2] * g 3 * g 17) := by
  rw [atom0025_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0025_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52657920 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025Coded : CoefficientMerge.Poly := [(71, -4), (395, -8), (719, -16), (1043, -16), (1061, -16), (1079, -16), (1097, -16), (1115, -16), (1133, -16), (1151, -16), (1169, -16), (1187, -16), (1205, -8), (1241, 8), (1259, 12), (1277, 16), (1295, 18)]
theorem atom0025Coded_decode : atom0025 = SparsePolynomial.decodeCubic 18 atom0025Coded := by decide +kernel
theorem atom0025Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (52657920 : Int) atom0025Coded) := by
  have h := atom0025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0026 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -16), ([4,5,10], -16), ([4,5,11], -16), ([4,5,12], -8), ([4,5,14], 8), ([4,5,15], 12), ([4,5,16], 16), ([4,5,17], 18)]
theorem atom0026_data : atom0026 = SparsePolynomial.monoTimes [4,5] 1 base07 := by decide +kernel
theorem eval_atom0026 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0026 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0026_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0026_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90171648 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026Coded : CoefficientMerge.Poly := [(77, -4), (401, -8), (725, -16), (1049, -16), (1373, -16), (1391, -16), (1392, -16), (1393, -16), (1394, -16), (1395, -16), (1396, -16), (1397, -16), (1398, -8), (1400, 8), (1401, 12), (1402, 16), (1403, 18)]
theorem atom0026Coded_decode : atom0026 = SparsePolynomial.decodeCubic 18 atom0026Coded := by decide +kernel
theorem atom0026Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (90171648 : Int) atom0026Coded) := by
  have h := atom0026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0027 : SparsePolynomial.Poly := [([0,4,6], -4), ([1,4,6], -8), ([2,4,6], -16), ([3,4,6], -16), ([4,4,6], -16), ([4,5,6], -16), ([4,6,6], -16), ([4,6,7], -16), ([4,6,8], -16), ([4,6,9], -16), ([4,6,10], -16), ([4,6,11], -16), ([4,6,12], -8), ([4,6,14], 8), ([4,6,15], 12), ([4,6,16], 16), ([4,6,17], 18)]
theorem atom0027_data : atom0027 = SparsePolynomial.monoTimes [4,6] 1 base07 := by decide +kernel
theorem eval_atom0027 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0027 = (quadB (outer g) ![1,2,2] * g 4 * g 6) := by
  rw [atom0027_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0027_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38064360 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027Coded : CoefficientMerge.Poly := [(78, -4), (402, -8), (726, -16), (1050, -16), (1374, -16), (1392, -16), (1410, -16), (1411, -16), (1412, -16), (1413, -16), (1414, -16), (1415, -16), (1416, -8), (1418, 8), (1419, 12), (1420, 16), (1421, 18)]
theorem atom0027Coded_decode : atom0027 = SparsePolynomial.decodeCubic 18 atom0027Coded := by decide +kernel
theorem atom0027Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (38064360 : Int) atom0027Coded) := by
  have h := atom0027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0028 : SparsePolynomial.Poly := [([0,4,7], -4), ([1,4,7], -8), ([2,4,7], -16), ([3,4,7], -16), ([4,4,7], -16), ([4,5,7], -16), ([4,6,7], -16), ([4,7,7], -16), ([4,7,8], -16), ([4,7,9], -16), ([4,7,10], -16), ([4,7,11], -16), ([4,7,12], -8), ([4,7,14], 8), ([4,7,15], 12), ([4,7,16], 16), ([4,7,17], 18)]
theorem atom0028_data : atom0028 = SparsePolynomial.monoTimes [4,7] 1 base07 := by decide +kernel
theorem eval_atom0028 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0028 = (quadB (outer g) ![1,2,2] * g 4 * g 7) := by
  rw [atom0028_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0028_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7113120 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028Coded : CoefficientMerge.Poly := [(79, -4), (403, -8), (727, -16), (1051, -16), (1375, -16), (1393, -16), (1411, -16), (1429, -16), (1430, -16), (1431, -16), (1432, -16), (1433, -16), (1434, -8), (1436, 8), (1437, 12), (1438, 16), (1439, 18)]
theorem atom0028Coded_decode : atom0028 = SparsePolynomial.decodeCubic 18 atom0028Coded := by decide +kernel
theorem atom0028Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7113120 : Int) atom0028Coded) := by
  have h := atom0028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0029 : SparsePolynomial.Poly := [([0,4,11], -4), ([1,4,11], -8), ([2,4,11], -16), ([3,4,11], -16), ([4,4,11], -16), ([4,5,11], -16), ([4,6,11], -16), ([4,7,11], -16), ([4,8,11], -16), ([4,9,11], -16), ([4,10,11], -16), ([4,11,11], -16), ([4,11,12], -8), ([4,11,14], 8), ([4,11,15], 12), ([4,11,16], 16), ([4,11,17], 18)]
theorem atom0029_data : atom0029 = SparsePolynomial.monoTimes [4,11] 1 base07 := by decide +kernel
theorem eval_atom0029 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = (quadB (outer g) ![1,2,2] * g 4 * g 11) := by
  rw [atom0029_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4653600 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029Coded : CoefficientMerge.Poly := [(83, -4), (407, -8), (731, -16), (1055, -16), (1379, -16), (1397, -16), (1415, -16), (1433, -16), (1451, -16), (1469, -16), (1487, -16), (1505, -16), (1506, -8), (1508, 8), (1509, 12), (1510, 16), (1511, 18)]
theorem atom0029Coded_decode : atom0029 = SparsePolynomial.decodeCubic 18 atom0029Coded := by decide +kernel
theorem atom0029Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4653600 : Int) atom0029Coded) := by
  have h := atom0029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0030 : SparsePolynomial.Poly := [([0,4,13], -4), ([1,4,13], -8), ([2,4,13], -16), ([3,4,13], -16), ([4,4,13], -16), ([4,5,13], -16), ([4,6,13], -16), ([4,7,13], -16), ([4,8,13], -16), ([4,9,13], -16), ([4,10,13], -16), ([4,11,13], -16), ([4,12,13], -8), ([4,13,14], 8), ([4,13,15], 12), ([4,13,16], 16), ([4,13,17], 18)]
theorem atom0030_data : atom0030 = SparsePolynomial.monoTimes [4,13] 1 base07 := by decide +kernel
theorem eval_atom0030 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0030 = (quadB (outer g) ![1,2,2] * g 4 * g 13) := by
  rw [atom0030_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0030_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35739060 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030Coded : CoefficientMerge.Poly := [(85, -4), (409, -8), (733, -16), (1057, -16), (1381, -16), (1399, -16), (1417, -16), (1435, -16), (1453, -16), (1471, -16), (1489, -16), (1507, -16), (1525, -8), (1544, 8), (1545, 12), (1546, 16), (1547, 18)]
theorem atom0030Coded_decode : atom0030 = SparsePolynomial.decodeCubic 18 atom0030Coded := by decide +kernel
theorem atom0030Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (35739060 : Int) atom0030Coded) := by
  have h := atom0030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0031 : SparsePolynomial.Poly := [([0,4,15], -4), ([1,4,15], -8), ([2,4,15], -16), ([3,4,15], -16), ([4,4,15], -16), ([4,5,15], -16), ([4,6,15], -16), ([4,7,15], -16), ([4,8,15], -16), ([4,9,15], -16), ([4,10,15], -16), ([4,11,15], -16), ([4,12,15], -8), ([4,14,15], 8), ([4,15,15], 12), ([4,15,16], 16), ([4,15,17], 18)]
theorem atom0031_data : atom0031 = SparsePolynomial.monoTimes [4,15] 1 base07 := by decide +kernel
theorem eval_atom0031 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0031 = (quadB (outer g) ![1,2,2] * g 4 * g 15) := by
  rw [atom0031_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0031_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95893980 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031Coded : CoefficientMerge.Poly := [(87, -4), (411, -8), (735, -16), (1059, -16), (1383, -16), (1401, -16), (1419, -16), (1437, -16), (1455, -16), (1473, -16), (1491, -16), (1509, -16), (1527, -8), (1563, 8), (1581, 12), (1582, 16), (1583, 18)]
theorem atom0031Coded_decode : atom0031 = SparsePolynomial.decodeCubic 18 atom0031Coded := by decide +kernel
theorem atom0031Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (95893980 : Int) atom0031Coded) := by
  have h := atom0031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0032 : SparsePolynomial.Poly := [([0,4,16], -4), ([1,4,16], -8), ([2,4,16], -16), ([3,4,16], -16), ([4,4,16], -16), ([4,5,16], -16), ([4,6,16], -16), ([4,7,16], -16), ([4,8,16], -16), ([4,9,16], -16), ([4,10,16], -16), ([4,11,16], -16), ([4,12,16], -8), ([4,14,16], 8), ([4,15,16], 12), ([4,16,16], 16), ([4,16,17], 18)]
theorem atom0032_data : atom0032 = SparsePolynomial.monoTimes [4,16] 1 base07 := by decide +kernel
theorem eval_atom0032 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0032 = (quadB (outer g) ![1,2,2] * g 4 * g 16) := by
  rw [atom0032_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0032_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164598700 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032Coded : CoefficientMerge.Poly := [(88, -4), (412, -8), (736, -16), (1060, -16), (1384, -16), (1402, -16), (1420, -16), (1438, -16), (1456, -16), (1474, -16), (1492, -16), (1510, -16), (1528, -8), (1564, 8), (1582, 12), (1600, 16), (1601, 18)]
theorem atom0032Coded_decode : atom0032 = SparsePolynomial.decodeCubic 18 atom0032Coded := by decide +kernel
theorem atom0032Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (164598700 : Int) atom0032Coded) := by
  have h := atom0032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0033 : SparsePolynomial.Poly := [([0,4,17], -4), ([1,4,17], -8), ([2,4,17], -16), ([3,4,17], -16), ([4,4,17], -16), ([4,5,17], -16), ([4,6,17], -16), ([4,7,17], -16), ([4,8,17], -16), ([4,9,17], -16), ([4,10,17], -16), ([4,11,17], -16), ([4,12,17], -8), ([4,14,17], 8), ([4,15,17], 12), ([4,16,17], 16), ([4,17,17], 18)]
theorem atom0033_data : atom0033 = SparsePolynomial.monoTimes [4,17] 1 base07 := by decide +kernel
theorem eval_atom0033 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = (quadB (outer g) ![1,2,2] * g 4 * g 17) := by
  rw [atom0033_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175428540 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033Coded : CoefficientMerge.Poly := [(89, -4), (413, -8), (737, -16), (1061, -16), (1385, -16), (1403, -16), (1421, -16), (1439, -16), (1457, -16), (1475, -16), (1493, -16), (1511, -16), (1529, -8), (1565, 8), (1583, 12), (1601, 16), (1619, 18)]
theorem atom0033Coded_decode : atom0033 = SparsePolynomial.decodeCubic 18 atom0033Coded := by decide +kernel
theorem atom0033Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (175428540 : Int) atom0033Coded) := by
  have h := atom0033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0034 : SparsePolynomial.Poly := [([0,5,6], -4), ([1,5,6], -8), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -8), ([5,6,14], 8), ([5,6,15], 12), ([5,6,16], 16), ([5,6,17], 18)]
theorem atom0034_data : atom0034 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0034 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0034 = (quadB (outer g) ![1,2,2] * g 5 * g 6) := by
  rw [atom0034_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0034_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90171648 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034Coded : CoefficientMerge.Poly := [(96, -4), (420, -8), (744, -16), (1068, -16), (1392, -16), (1716, -16), (1734, -16), (1735, -16), (1736, -16), (1737, -16), (1738, -16), (1739, -16), (1740, -8), (1742, 8), (1743, 12), (1744, 16), (1745, 18)]
theorem atom0034Coded_decode : atom0034 = SparsePolynomial.decodeCubic 18 atom0034Coded := by decide +kernel
theorem atom0034Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (90171648 : Int) atom0034Coded) := by
  have h := atom0034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0035 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -16), ([5,7,7], -16), ([5,7,8], -16), ([5,7,9], -16), ([5,7,10], -16), ([5,7,11], -16), ([5,7,12], -8), ([5,7,14], 8), ([5,7,15], 12), ([5,7,16], 16), ([5,7,17], 18)]
theorem atom0035_data : atom0035 = SparsePolynomial.monoTimes [5,7] 1 base07 := by decide +kernel
theorem eval_atom0035 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0035 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0035_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0035_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85822200 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035Coded : CoefficientMerge.Poly := [(97, -4), (421, -8), (745, -16), (1069, -16), (1393, -16), (1717, -16), (1735, -16), (1753, -16), (1754, -16), (1755, -16), (1756, -16), (1757, -16), (1758, -8), (1760, 8), (1761, 12), (1762, 16), (1763, 18)]
theorem atom0035Coded_decode : atom0035 = SparsePolynomial.decodeCubic 18 atom0035Coded := by decide +kernel
theorem atom0035Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (85822200 : Int) atom0035Coded) := by
  have h := atom0035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0036 : SparsePolynomial.Poly := [([0,5,8], -4), ([1,5,8], -8), ([2,5,8], -16), ([3,5,8], -16), ([4,5,8], -16), ([5,5,8], -16), ([5,6,8], -16), ([5,7,8], -16), ([5,8,8], -16), ([5,8,9], -16), ([5,8,10], -16), ([5,8,11], -16), ([5,8,12], -8), ([5,8,14], 8), ([5,8,15], 12), ([5,8,16], 16), ([5,8,17], 18)]
theorem atom0036_data : atom0036 = SparsePolynomial.monoTimes [5,8] 1 base07 := by decide +kernel
theorem eval_atom0036 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = (quadB (outer g) ![1,2,2] * g 5 * g 8) := by
  rw [atom0036_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72822360 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036Coded : CoefficientMerge.Poly := [(98, -4), (422, -8), (746, -16), (1070, -16), (1394, -16), (1718, -16), (1736, -16), (1754, -16), (1772, -16), (1773, -16), (1774, -16), (1775, -16), (1776, -8), (1778, 8), (1779, 12), (1780, 16), (1781, 18)]
theorem atom0036Coded_decode : atom0036 = SparsePolynomial.decodeCubic 18 atom0036Coded := by decide +kernel
theorem atom0036Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (72822360 : Int) atom0036Coded) := by
  have h := atom0036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0037 : SparsePolynomial.Poly := [([0,5,9], -4), ([1,5,9], -8), ([2,5,9], -16), ([3,5,9], -16), ([4,5,9], -16), ([5,5,9], -16), ([5,6,9], -16), ([5,7,9], -16), ([5,8,9], -16), ([5,9,9], -16), ([5,9,10], -16), ([5,9,11], -16), ([5,9,12], -8), ([5,9,14], 8), ([5,9,15], 12), ([5,9,16], 16), ([5,9,17], 18)]
theorem atom0037_data : atom0037 = SparsePolynomial.monoTimes [5,9] 1 base07 := by decide +kernel
theorem eval_atom0037 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0037 = (quadB (outer g) ![1,2,2] * g 5 * g 9) := by
  rw [atom0037_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0037_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60242520 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037Coded : CoefficientMerge.Poly := [(99, -4), (423, -8), (747, -16), (1071, -16), (1395, -16), (1719, -16), (1737, -16), (1755, -16), (1773, -16), (1791, -16), (1792, -16), (1793, -16), (1794, -8), (1796, 8), (1797, 12), (1798, 16), (1799, 18)]
theorem atom0037Coded_decode : atom0037 = SparsePolynomial.decodeCubic 18 atom0037Coded := by decide +kernel
theorem atom0037Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (60242520 : Int) atom0037Coded) := by
  have h := atom0037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0038 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -16), ([5,7,10], -16), ([5,8,10], -16), ([5,9,10], -16), ([5,10,10], -16), ([5,10,11], -16), ([5,10,12], -8), ([5,10,14], 8), ([5,10,15], 12), ([5,10,16], 16), ([5,10,17], 18)]
theorem atom0038_data : atom0038 = SparsePolynomial.monoTimes [5,10] 1 base07 := by decide +kernel
theorem eval_atom0038 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0038_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51009240 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038Coded : CoefficientMerge.Poly := [(100, -4), (424, -8), (748, -16), (1072, -16), (1396, -16), (1720, -16), (1738, -16), (1756, -16), (1774, -16), (1792, -16), (1810, -16), (1811, -16), (1812, -8), (1814, 8), (1815, 12), (1816, 16), (1817, 18)]
theorem atom0038Coded_decode : atom0038 = SparsePolynomial.decodeCubic 18 atom0038Coded := by decide +kernel
theorem atom0038Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (51009240 : Int) atom0038Coded) := by
  have h := atom0038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0039 : SparsePolynomial.Poly := [([0,5,11], -4), ([1,5,11], -8), ([2,5,11], -16), ([3,5,11], -16), ([4,5,11], -16), ([5,5,11], -16), ([5,6,11], -16), ([5,7,11], -16), ([5,8,11], -16), ([5,9,11], -16), ([5,10,11], -16), ([5,11,11], -16), ([5,11,12], -8), ([5,11,14], 8), ([5,11,15], 12), ([5,11,16], 16), ([5,11,17], 18)]
theorem atom0039_data : atom0039 = SparsePolynomial.monoTimes [5,11] 1 base07 := by decide +kernel
theorem eval_atom0039 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0039 = (quadB (outer g) ![1,2,2] * g 5 * g 11) := by
  rw [atom0039_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0039_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46429560 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039Coded : CoefficientMerge.Poly := [(101, -4), (425, -8), (749, -16), (1073, -16), (1397, -16), (1721, -16), (1739, -16), (1757, -16), (1775, -16), (1793, -16), (1811, -16), (1829, -16), (1830, -8), (1832, 8), (1833, 12), (1834, 16), (1835, 18)]
theorem atom0039Coded_decode : atom0039 = SparsePolynomial.decodeCubic 18 atom0039Coded := by decide +kernel
theorem atom0039Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (46429560 : Int) atom0039Coded) := by
  have h := atom0039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0040 : SparsePolynomial.Poly := [([0,5,13], -4), ([1,5,13], -8), ([2,5,13], -16), ([3,5,13], -16), ([4,5,13], -16), ([5,5,13], -16), ([5,6,13], -16), ([5,7,13], -16), ([5,8,13], -16), ([5,9,13], -16), ([5,10,13], -16), ([5,11,13], -16), ([5,12,13], -8), ([5,13,14], 8), ([5,13,15], 12), ([5,13,16], 16), ([5,13,17], 18)]
theorem atom0040_data : atom0040 = SparsePolynomial.monoTimes [5,13] 1 base07 := by decide +kernel
theorem eval_atom0040 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0040 = (quadB (outer g) ![1,2,2] * g 5 * g 13) := by
  rw [atom0040_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0040_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68360715 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040Coded : CoefficientMerge.Poly := [(103, -4), (427, -8), (751, -16), (1075, -16), (1399, -16), (1723, -16), (1741, -16), (1759, -16), (1777, -16), (1795, -16), (1813, -16), (1831, -16), (1849, -8), (1868, 8), (1869, 12), (1870, 16), (1871, 18)]
theorem atom0040Coded_decode : atom0040 = SparsePolynomial.decodeCubic 18 atom0040Coded := by decide +kernel
theorem atom0040Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (68360715 : Int) atom0040Coded) := by
  have h := atom0040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0041 : SparsePolynomial.Poly := [([0,5,15], -4), ([1,5,15], -8), ([2,5,15], -16), ([3,5,15], -16), ([4,5,15], -16), ([5,5,15], -16), ([5,6,15], -16), ([5,7,15], -16), ([5,8,15], -16), ([5,9,15], -16), ([5,10,15], -16), ([5,11,15], -16), ([5,12,15], -8), ([5,14,15], 8), ([5,15,15], 12), ([5,15,16], 16), ([5,15,17], 18)]
theorem atom0041_data : atom0041 = SparsePolynomial.monoTimes [5,15] 1 base07 := by decide +kernel
theorem eval_atom0041 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0041 = (quadB (outer g) ![1,2,2] * g 5 * g 15) := by
  rw [atom0041_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0041_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (128673585 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041Coded : CoefficientMerge.Poly := [(105, -4), (429, -8), (753, -16), (1077, -16), (1401, -16), (1725, -16), (1743, -16), (1761, -16), (1779, -16), (1797, -16), (1815, -16), (1833, -16), (1851, -8), (1887, 8), (1905, 12), (1906, 16), (1907, 18)]
theorem atom0041Coded_decode : atom0041 = SparsePolynomial.decodeCubic 18 atom0041Coded := by decide +kernel
theorem atom0041Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (128673585 : Int) atom0041Coded) := by
  have h := atom0041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0042 : SparsePolynomial.Poly := [([0,5,16], -4), ([1,5,16], -8), ([2,5,16], -16), ([3,5,16], -16), ([4,5,16], -16), ([5,5,16], -16), ([5,6,16], -16), ([5,7,16], -16), ([5,8,16], -16), ([5,9,16], -16), ([5,10,16], -16), ([5,11,16], -16), ([5,12,16], -8), ([5,14,16], 8), ([5,15,16], 12), ([5,16,16], 16), ([5,16,17], 18)]
theorem atom0042_data : atom0042 = SparsePolynomial.monoTimes [5,16] 1 base07 := by decide +kernel
theorem eval_atom0042 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0042 = (quadB (outer g) ![1,2,2] * g 5 * g 16) := by
  rw [atom0042_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0042_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219814845 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042Coded : CoefficientMerge.Poly := [(106, -4), (430, -8), (754, -16), (1078, -16), (1402, -16), (1726, -16), (1744, -16), (1762, -16), (1780, -16), (1798, -16), (1816, -16), (1834, -16), (1852, -8), (1888, 8), (1906, 12), (1924, 16), (1925, 18)]
theorem atom0042Coded_decode : atom0042 = SparsePolynomial.decodeCubic 18 atom0042Coded := by decide +kernel
theorem atom0042Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (219814845 : Int) atom0042Coded) := by
  have h := atom0042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0043 : SparsePolynomial.Poly := [([0,5,17], -4), ([1,5,17], -8), ([2,5,17], -16), ([3,5,17], -16), ([4,5,17], -16), ([5,5,17], -16), ([5,6,17], -16), ([5,7,17], -16), ([5,8,17], -16), ([5,9,17], -16), ([5,10,17], -16), ([5,11,17], -16), ([5,12,17], -8), ([5,14,17], 8), ([5,15,17], 12), ([5,16,17], 16), ([5,17,17], 18)]
theorem atom0043_data : atom0043 = SparsePolynomial.monoTimes [5,17] 1 base07 := by decide +kernel
theorem eval_atom0043 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0043 = (quadB (outer g) ![1,2,2] * g 5 * g 17) := by
  rw [atom0043_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0043_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214574265 : Int) atom0043) := by
  rw [SparsePolynomial.eval_scale, eval_atom0043]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0043Coded : CoefficientMerge.Poly := [(107, -4), (431, -8), (755, -16), (1079, -16), (1403, -16), (1727, -16), (1745, -16), (1763, -16), (1781, -16), (1799, -16), (1817, -16), (1835, -16), (1853, -8), (1889, 8), (1907, 12), (1925, 16), (1943, 18)]
theorem atom0043Coded_decode : atom0043 = SparsePolynomial.decodeCubic 18 atom0043Coded := by decide +kernel
theorem atom0043Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (214574265 : Int) atom0043Coded) := by
  have h := atom0043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0044 : SparsePolynomial.Poly := [([0,6,7], -4), ([1,6,7], -8), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -8), ([6,7,14], 8), ([6,7,15], 12), ([6,7,16], 16), ([6,7,17], 18)]
theorem atom0044_data : atom0044 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0044 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0044 = (quadB (outer g) ![1,2,2] * g 6 * g 7) := by
  rw [atom0044_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0044_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23254308 : Int) atom0044) := by
  rw [SparsePolynomial.eval_scale, eval_atom0044]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0044Coded : CoefficientMerge.Poly := [(115, -4), (439, -8), (763, -16), (1087, -16), (1411, -16), (1735, -16), (2059, -16), (2077, -16), (2078, -16), (2079, -16), (2080, -16), (2081, -16), (2082, -8), (2084, 8), (2085, 12), (2086, 16), (2087, 18)]
theorem atom0044Coded_decode : atom0044 = SparsePolynomial.decodeCubic 18 atom0044Coded := by decide +kernel
theorem atom0044Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (23254308 : Int) atom0044Coded) := by
  have h := atom0044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0045 : SparsePolynomial.Poly := [([0,6,8], -4), ([1,6,8], -8), ([2,6,8], -16), ([3,6,8], -16), ([4,6,8], -16), ([5,6,8], -16), ([6,6,8], -16), ([6,7,8], -16), ([6,8,8], -16), ([6,8,9], -16), ([6,8,10], -16), ([6,8,11], -16), ([6,8,12], -8), ([6,8,14], 8), ([6,8,15], 12), ([6,8,16], 16), ([6,8,17], 18)]
theorem atom0045_data : atom0045 = SparsePolynomial.monoTimes [6,8] 1 base07 := by decide +kernel
theorem eval_atom0045 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0045 = (quadB (outer g) ![1,2,2] * g 6 * g 8) := by
  rw [atom0045_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0045_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153341400 : Int) atom0045) := by
  rw [SparsePolynomial.eval_scale, eval_atom0045]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0045Coded : CoefficientMerge.Poly := [(116, -4), (440, -8), (764, -16), (1088, -16), (1412, -16), (1736, -16), (2060, -16), (2078, -16), (2096, -16), (2097, -16), (2098, -16), (2099, -16), (2100, -8), (2102, 8), (2103, 12), (2104, 16), (2105, 18)]
theorem atom0045Coded_decode : atom0045 = SparsePolynomial.decodeCubic 18 atom0045Coded := by decide +kernel
theorem atom0045Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (153341400 : Int) atom0045Coded) := by
  have h := atom0045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0046 : SparsePolynomial.Poly := [([0,6,9], -4), ([1,6,9], -8), ([2,6,9], -16), ([3,6,9], -16), ([4,6,9], -16), ([5,6,9], -16), ([6,6,9], -16), ([6,7,9], -16), ([6,8,9], -16), ([6,9,9], -16), ([6,9,10], -16), ([6,9,11], -16), ([6,9,12], -8), ([6,9,14], 8), ([6,9,15], 12), ([6,9,16], 16), ([6,9,17], 18)]
theorem atom0046_data : atom0046 = SparsePolynomial.monoTimes [6,9] 1 base07 := by decide +kernel
theorem eval_atom0046 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0046 = (quadB (outer g) ![1,2,2] * g 6 * g 9) := by
  rw [atom0046_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0046_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131729880 : Int) atom0046) := by
  rw [SparsePolynomial.eval_scale, eval_atom0046]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0046Coded : CoefficientMerge.Poly := [(117, -4), (441, -8), (765, -16), (1089, -16), (1413, -16), (1737, -16), (2061, -16), (2079, -16), (2097, -16), (2115, -16), (2116, -16), (2117, -16), (2118, -8), (2120, 8), (2121, 12), (2122, 16), (2123, 18)]
theorem atom0046Coded_decode : atom0046 = SparsePolynomial.decodeCubic 18 atom0046Coded := by decide +kernel
theorem atom0046Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (131729880 : Int) atom0046Coded) := by
  have h := atom0046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0047 : SparsePolynomial.Poly := [([0,6,10], -4), ([1,6,10], -8), ([2,6,10], -16), ([3,6,10], -16), ([4,6,10], -16), ([5,6,10], -16), ([6,6,10], -16), ([6,7,10], -16), ([6,8,10], -16), ([6,9,10], -16), ([6,10,10], -16), ([6,10,11], -16), ([6,10,12], -8), ([6,10,14], 8), ([6,10,15], 12), ([6,10,16], 16), ([6,10,17], 18)]
theorem atom0047_data : atom0047 = SparsePolynomial.monoTimes [6,10] 1 base07 := by decide +kernel
theorem eval_atom0047 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0047 = (quadB (outer g) ![1,2,2] * g 6 * g 10) := by
  rw [atom0047_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0047_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110118360 : Int) atom0047) := by
  rw [SparsePolynomial.eval_scale, eval_atom0047]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0047Coded : CoefficientMerge.Poly := [(118, -4), (442, -8), (766, -16), (1090, -16), (1414, -16), (1738, -16), (2062, -16), (2080, -16), (2098, -16), (2116, -16), (2134, -16), (2135, -16), (2136, -8), (2138, 8), (2139, 12), (2140, 16), (2141, 18)]
theorem atom0047Coded_decode : atom0047 = SparsePolynomial.decodeCubic 18 atom0047Coded := by decide +kernel
theorem atom0047Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (110118360 : Int) atom0047Coded) := by
  have h := atom0047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0048 : SparsePolynomial.Poly := [([0,6,11], -4), ([1,6,11], -8), ([2,6,11], -16), ([3,6,11], -16), ([4,6,11], -16), ([5,6,11], -16), ([6,6,11], -16), ([6,7,11], -16), ([6,8,11], -16), ([6,9,11], -16), ([6,10,11], -16), ([6,11,11], -16), ([6,11,12], -8), ([6,11,14], 8), ([6,11,15], 12), ([6,11,16], 16), ([6,11,17], 18)]
theorem atom0048_data : atom0048 = SparsePolynomial.monoTimes [6,11] 1 base07 := by decide +kernel
theorem eval_atom0048 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0048 = (quadB (outer g) ![1,2,2] * g 6 * g 11) := by
  rw [atom0048_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0048_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93160440 : Int) atom0048) := by
  rw [SparsePolynomial.eval_scale, eval_atom0048]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0048Coded : CoefficientMerge.Poly := [(119, -4), (443, -8), (767, -16), (1091, -16), (1415, -16), (1739, -16), (2063, -16), (2081, -16), (2099, -16), (2117, -16), (2135, -16), (2153, -16), (2154, -8), (2156, 8), (2157, 12), (2158, 16), (2159, 18)]
theorem atom0048Coded_decode : atom0048 = SparsePolynomial.decodeCubic 18 atom0048Coded := by decide +kernel
theorem atom0048Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (93160440 : Int) atom0048Coded) := by
  have h := atom0048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0049 : SparsePolynomial.Poly := [([0,6,13], -4), ([1,6,13], -8), ([2,6,13], -16), ([3,6,13], -16), ([4,6,13], -16), ([5,6,13], -16), ([6,6,13], -16), ([6,7,13], -16), ([6,8,13], -16), ([6,9,13], -16), ([6,10,13], -16), ([6,11,13], -16), ([6,12,13], -8), ([6,13,14], 8), ([6,13,15], 12), ([6,13,16], 16), ([6,13,17], 18)]
theorem atom0049_data : atom0049 = SparsePolynomial.monoTimes [6,13] 1 base07 := by decide +kernel
theorem eval_atom0049 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0049 = (quadB (outer g) ![1,2,2] * g 6 * g 13) := by
  rw [atom0049_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0049_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95732955 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049Coded : CoefficientMerge.Poly := [(121, -4), (445, -8), (769, -16), (1093, -16), (1417, -16), (1741, -16), (2065, -16), (2083, -16), (2101, -16), (2119, -16), (2137, -16), (2155, -16), (2173, -8), (2192, 8), (2193, 12), (2194, 16), (2195, 18)]
theorem atom0049Coded_decode : atom0049 = SparsePolynomial.decodeCubic 18 atom0049Coded := by decide +kernel
theorem atom0049Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (95732955 : Int) atom0049Coded) := by
  have h := atom0049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0050 : SparsePolynomial.Poly := [([0,6,15], -4), ([1,6,15], -8), ([2,6,15], -16), ([3,6,15], -16), ([4,6,15], -16), ([5,6,15], -16), ([6,6,15], -16), ([6,7,15], -16), ([6,8,15], -16), ([6,9,15], -16), ([6,10,15], -16), ([6,11,15], -16), ([6,12,15], -8), ([6,14,15], 8), ([6,15,15], 12), ([6,15,16], 16), ([6,15,17], 18)]
theorem atom0050_data : atom0050 = SparsePolynomial.monoTimes [6,15] 1 base07 := by decide +kernel
theorem eval_atom0050 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0050 = (quadB (outer g) ![1,2,2] * g 6 * g 15) := by
  rw [atom0050_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0050_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142085025 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050Coded : CoefficientMerge.Poly := [(123, -4), (447, -8), (771, -16), (1095, -16), (1419, -16), (1743, -16), (2067, -16), (2085, -16), (2103, -16), (2121, -16), (2139, -16), (2157, -16), (2175, -8), (2211, 8), (2229, 12), (2230, 16), (2231, 18)]
theorem atom0050Coded_decode : atom0050 = SparsePolynomial.decodeCubic 18 atom0050Coded := by decide +kernel
theorem atom0050Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (142085025 : Int) atom0050Coded) := by
  have h := atom0050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0051 : SparsePolynomial.Poly := [([0,6,16], -4), ([1,6,16], -8), ([2,6,16], -16), ([3,6,16], -16), ([4,6,16], -16), ([5,6,16], -16), ([6,6,16], -16), ([6,7,16], -16), ([6,8,16], -16), ([6,9,16], -16), ([6,10,16], -16), ([6,11,16], -16), ([6,12,16], -8), ([6,14,16], 8), ([6,15,16], 12), ([6,16,16], 16), ([6,16,17], 18)]
theorem atom0051_data : atom0051 = SparsePolynomial.monoTimes [6,16] 1 base07 := by decide +kernel
theorem eval_atom0051 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0051 = (quadB (outer g) ![1,2,2] * g 6 * g 16) := by
  rw [atom0051_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0051_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290895525 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051Coded : CoefficientMerge.Poly := [(124, -4), (448, -8), (772, -16), (1096, -16), (1420, -16), (1744, -16), (2068, -16), (2086, -16), (2104, -16), (2122, -16), (2140, -16), (2158, -16), (2176, -8), (2212, 8), (2230, 12), (2248, 16), (2249, 18)]
theorem atom0051Coded_decode : atom0051 = SparsePolynomial.decodeCubic 18 atom0051Coded := by decide +kernel
theorem atom0051Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (290895525 : Int) atom0051Coded) := by
  have h := atom0051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0052 : SparsePolynomial.Poly := [([0,6,17], -4), ([1,6,17], -8), ([2,6,17], -16), ([3,6,17], -16), ([4,6,17], -16), ([5,6,17], -16), ([6,6,17], -16), ([6,7,17], -16), ([6,8,17], -16), ([6,9,17], -16), ([6,10,17], -16), ([6,11,17], -16), ([6,12,17], -8), ([6,14,17], 8), ([6,15,17], 12), ([6,16,17], 16), ([6,17,17], 18)]
theorem atom0052_data : atom0052 = SparsePolynomial.monoTimes [6,17] 1 base07 := by decide +kernel
theorem eval_atom0052 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0052 = (quadB (outer g) ![1,2,2] * g 6 * g 17) := by
  rw [atom0052_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0052_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217623465 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052Coded : CoefficientMerge.Poly := [(125, -4), (449, -8), (773, -16), (1097, -16), (1421, -16), (1745, -16), (2069, -16), (2087, -16), (2105, -16), (2123, -16), (2141, -16), (2159, -16), (2177, -8), (2213, 8), (2231, 12), (2249, 16), (2267, 18)]
theorem atom0052Coded_decode : atom0052 = SparsePolynomial.decodeCubic 18 atom0052Coded := by decide +kernel
theorem atom0052Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (217623465 : Int) atom0052Coded) := by
  have h := atom0052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0053 : SparsePolynomial.Poly := [([0,7,8], -4), ([1,7,8], -8), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -8), ([7,8,14], 8), ([7,8,15], 12), ([7,8,16], 16), ([7,8,17], 18)]
theorem atom0053_data : atom0053 = SparsePolynomial.monoTimes [7,8] 1 base07 := by decide +kernel
theorem eval_atom0053 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0053 = (quadB (outer g) ![1,2,2] * g 7 * g 8) := by
  rw [atom0053_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0053_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90171648 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053Coded : CoefficientMerge.Poly := [(134, -4), (458, -8), (782, -16), (1106, -16), (1430, -16), (1754, -16), (2078, -16), (2402, -16), (2420, -16), (2421, -16), (2422, -16), (2423, -16), (2424, -8), (2426, 8), (2427, 12), (2428, 16), (2429, 18)]
theorem atom0053Coded_decode : atom0053 = SparsePolynomial.decodeCubic 18 atom0053Coded := by decide +kernel
theorem atom0053Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (90171648 : Int) atom0053Coded) := by
  have h := atom0053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0054 : SparsePolynomial.Poly := [([0,7,9], -4), ([1,7,9], -8), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -8), ([7,9,14], 8), ([7,9,15], 12), ([7,9,16], 16), ([7,9,17], 18)]
theorem atom0054_data : atom0054 = SparsePolynomial.monoTimes [7,9] 1 base07 := by decide +kernel
theorem eval_atom0054 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0054 = (quadB (outer g) ![1,2,2] * g 7 * g 9) := by
  rw [atom0054_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0054_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188799600 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054Coded : CoefficientMerge.Poly := [(135, -4), (459, -8), (783, -16), (1107, -16), (1431, -16), (1755, -16), (2079, -16), (2403, -16), (2421, -16), (2439, -16), (2440, -16), (2441, -16), (2442, -8), (2444, 8), (2445, 12), (2446, 16), (2447, 18)]
theorem atom0054Coded_decode : atom0054 = SparsePolynomial.decodeCubic 18 atom0054Coded := by decide +kernel
theorem atom0054Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (188799600 : Int) atom0054Coded) := by
  have h := atom0054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0055 : SparsePolynomial.Poly := [([0,7,10], -4), ([1,7,10], -8), ([2,7,10], -16), ([3,7,10], -16), ([4,7,10], -16), ([5,7,10], -16), ([6,7,10], -16), ([7,7,10], -16), ([7,8,10], -16), ([7,9,10], -16), ([7,10,10], -16), ([7,10,11], -16), ([7,10,12], -8), ([7,10,14], 8), ([7,10,15], 12), ([7,10,16], 16), ([7,10,17], 18)]
theorem atom0055_data : atom0055 = SparsePolynomial.monoTimes [7,10] 1 base07 := by decide +kernel
theorem eval_atom0055 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0055 = (quadB (outer g) ![1,2,2] * g 7 * g 10) := by
  rw [atom0055_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0055_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151664880 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055Coded : CoefficientMerge.Poly := [(136, -4), (460, -8), (784, -16), (1108, -16), (1432, -16), (1756, -16), (2080, -16), (2404, -16), (2422, -16), (2440, -16), (2458, -16), (2459, -16), (2460, -8), (2462, 8), (2463, 12), (2464, 16), (2465, 18)]
theorem atom0055Coded_decode : atom0055 = SparsePolynomial.decodeCubic 18 atom0055Coded := by decide +kernel
theorem atom0055Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (151664880 : Int) atom0055Coded) := by
  have h := atom0055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0056 : SparsePolynomial.Poly := [([0,7,11], -4), ([1,7,11], -8), ([2,7,11], -16), ([3,7,11], -16), ([4,7,11], -16), ([5,7,11], -16), ([6,7,11], -16), ([7,7,11], -16), ([7,8,11], -16), ([7,9,11], -16), ([7,10,11], -16), ([7,11,11], -16), ([7,11,12], -8), ([7,11,14], 8), ([7,11,15], 12), ([7,11,16], 16), ([7,11,17], 18)]
theorem atom0056_data : atom0056 = SparsePolynomial.monoTimes [7,11] 1 base07 := by decide +kernel
theorem eval_atom0056 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0056 = (quadB (outer g) ![1,2,2] * g 7 * g 11) := by
  rw [atom0056_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0056_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119183760 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056Coded : CoefficientMerge.Poly := [(137, -4), (461, -8), (785, -16), (1109, -16), (1433, -16), (1757, -16), (2081, -16), (2405, -16), (2423, -16), (2441, -16), (2459, -16), (2477, -16), (2478, -8), (2480, 8), (2481, 12), (2482, 16), (2483, 18)]
theorem atom0056Coded_decode : atom0056 = SparsePolynomial.decodeCubic 18 atom0056Coded := by decide +kernel
theorem atom0056Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (119183760 : Int) atom0056Coded) := by
  have h := atom0056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0057 : SparsePolynomial.Poly := [([0,7,13], -4), ([1,7,13], -8), ([2,7,13], -16), ([3,7,13], -16), ([4,7,13], -16), ([5,7,13], -16), ([6,7,13], -16), ([7,7,13], -16), ([7,8,13], -16), ([7,9,13], -16), ([7,10,13], -16), ([7,11,13], -16), ([7,12,13], -8), ([7,13,14], 8), ([7,13,15], 12), ([7,13,16], 16), ([7,13,17], 18)]
theorem atom0057_data : atom0057 = SparsePolynomial.monoTimes [7,13] 1 base07 := by decide +kernel
theorem eval_atom0057 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0057 = (quadB (outer g) ![1,2,2] * g 7 * g 13) := by
  rw [atom0057_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0057_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101816730 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057Coded : CoefficientMerge.Poly := [(139, -4), (463, -8), (787, -16), (1111, -16), (1435, -16), (1759, -16), (2083, -16), (2407, -16), (2425, -16), (2443, -16), (2461, -16), (2479, -16), (2497, -8), (2516, 8), (2517, 12), (2518, 16), (2519, 18)]
theorem atom0057Coded_decode : atom0057 = SparsePolynomial.decodeCubic 18 atom0057Coded := by decide +kernel
theorem atom0057Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (101816730 : Int) atom0057Coded) := by
  have h := atom0057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0058 : SparsePolynomial.Poly := [([0,7,15], -4), ([1,7,15], -8), ([2,7,15], -16), ([3,7,15], -16), ([4,7,15], -16), ([5,7,15], -16), ([6,7,15], -16), ([7,7,15], -16), ([7,8,15], -16), ([7,9,15], -16), ([7,10,15], -16), ([7,11,15], -16), ([7,12,15], -8), ([7,14,15], 8), ([7,15,15], 12), ([7,15,16], 16), ([7,15,17], 18)]
theorem atom0058_data : atom0058 = SparsePolynomial.monoTimes [7,15] 1 base07 := by decide +kernel
theorem eval_atom0058 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0058 = (quadB (outer g) ![1,2,2] * g 7 * g 15) := by
  rw [atom0058_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0058_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139336110 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058Coded : CoefficientMerge.Poly := [(141, -4), (465, -8), (789, -16), (1113, -16), (1437, -16), (1761, -16), (2085, -16), (2409, -16), (2427, -16), (2445, -16), (2463, -16), (2481, -16), (2499, -8), (2535, 8), (2553, 12), (2554, 16), (2555, 18)]
theorem atom0058Coded_decode : atom0058 = SparsePolynomial.decodeCubic 18 atom0058Coded := by decide +kernel
theorem atom0058Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (139336110 : Int) atom0058Coded) := by
  have h := atom0058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0059 : SparsePolynomial.Poly := [([0,7,16], -4), ([1,7,16], -8), ([2,7,16], -16), ([3,7,16], -16), ([4,7,16], -16), ([5,7,16], -16), ([6,7,16], -16), ([7,7,16], -16), ([7,8,16], -16), ([7,9,16], -16), ([7,10,16], -16), ([7,11,16], -16), ([7,12,16], -8), ([7,14,16], 8), ([7,15,16], 12), ([7,16,16], 16), ([7,16,17], 18)]
theorem atom0059_data : atom0059 = SparsePolynomial.monoTimes [7,16] 1 base07 := by decide +kernel
theorem eval_atom0059 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0059 = (quadB (outer g) ![1,2,2] * g 7 * g 16) := by
  rw [atom0059_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0059_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287432550 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059Coded : CoefficientMerge.Poly := [(142, -4), (466, -8), (790, -16), (1114, -16), (1438, -16), (1762, -16), (2086, -16), (2410, -16), (2428, -16), (2446, -16), (2464, -16), (2482, -16), (2500, -8), (2536, 8), (2554, 12), (2572, 16), (2573, 18)]
theorem atom0059Coded_decode : atom0059 = SparsePolynomial.decodeCubic 18 atom0059Coded := by decide +kernel
theorem atom0059Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (287432550 : Int) atom0059Coded) := by
  have h := atom0059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0060 : SparsePolynomial.Poly := [([0,7,17], -4), ([1,7,17], -8), ([2,7,17], -16), ([3,7,17], -16), ([4,7,17], -16), ([5,7,17], -16), ([6,7,17], -16), ([7,7,17], -16), ([7,8,17], -16), ([7,9,17], -16), ([7,10,17], -16), ([7,11,17], -16), ([7,12,17], -8), ([7,14,17], 8), ([7,15,17], 12), ([7,16,17], 16), ([7,17,17], 18)]
theorem atom0060_data : atom0060 = SparsePolynomial.monoTimes [7,17] 1 base07 := by decide +kernel
theorem eval_atom0060 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0060 = (quadB (outer g) ![1,2,2] * g 7 * g 17) := by
  rw [atom0060_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0060_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213446430 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060Coded : CoefficientMerge.Poly := [(143, -4), (467, -8), (791, -16), (1115, -16), (1439, -16), (1763, -16), (2087, -16), (2411, -16), (2429, -16), (2447, -16), (2465, -16), (2483, -16), (2501, -8), (2537, 8), (2555, 12), (2573, 16), (2591, 18)]
theorem atom0060Coded_decode : atom0060 = SparsePolynomial.decodeCubic 18 atom0060Coded := by decide +kernel
theorem atom0060Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (213446430 : Int) atom0060Coded) := by
  have h := atom0060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0061 : SparsePolynomial.Poly := [([0,8,9], -4), ([1,8,9], -8), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -8), ([8,9,14], 8), ([8,9,15], 12), ([8,9,16], 16), ([8,9,17], 18)]
theorem atom0061_data : atom0061 = SparsePolynomial.monoTimes [8,9] 1 base07 := by decide +kernel
theorem eval_atom0061 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0061 = (quadB (outer g) ![1,2,2] * g 8 * g 9) := by
  rw [atom0061_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0061_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63799680 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061Coded : CoefficientMerge.Poly := [(153, -4), (477, -8), (801, -16), (1125, -16), (1449, -16), (1773, -16), (2097, -16), (2421, -16), (2745, -16), (2763, -16), (2764, -16), (2765, -16), (2766, -8), (2768, 8), (2769, 12), (2770, 16), (2771, 18)]
theorem atom0061Coded_decode : atom0061 = SparsePolynomial.decodeCubic 18 atom0061Coded := by decide +kernel
theorem atom0061Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (63799680 : Int) atom0061Coded) := by
  have h := atom0061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0062 : SparsePolynomial.Poly := [([0,8,10], -4), ([1,8,10], -8), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -8), ([8,10,14], 8), ([8,10,15], 12), ([8,10,16], 16), ([8,10,17], 18)]
theorem atom0062_data : atom0062 = SparsePolynomial.monoTimes [8,10] 1 base07 := by decide +kernel
theorem eval_atom0062 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0062 = (quadB (outer g) ![1,2,2] * g 8 * g 10) := by
  rw [atom0062_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0062_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185764032 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062Coded : CoefficientMerge.Poly := [(154, -4), (478, -8), (802, -16), (1126, -16), (1450, -16), (1774, -16), (2098, -16), (2422, -16), (2746, -16), (2764, -16), (2782, -16), (2783, -16), (2784, -8), (2786, 8), (2787, 12), (2788, 16), (2789, 18)]
theorem atom0062Coded_decode : atom0062 = SparsePolynomial.decodeCubic 18 atom0062Coded := by decide +kernel
theorem atom0062Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (185764032 : Int) atom0062Coded) := by
  have h := atom0062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0063 : SparsePolynomial.Poly := [([0,8,11], -4), ([1,8,11], -8), ([2,8,11], -16), ([3,8,11], -16), ([4,8,11], -16), ([5,8,11], -16), ([6,8,11], -16), ([7,8,11], -16), ([8,8,11], -16), ([8,9,11], -16), ([8,10,11], -16), ([8,11,11], -16), ([8,11,12], -8), ([8,11,14], 8), ([8,11,15], 12), ([8,11,16], 16), ([8,11,17], 18)]
theorem atom0063_data : atom0063 = SparsePolynomial.monoTimes [8,11] 1 base07 := by decide +kernel
theorem eval_atom0063 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0063 = (quadB (outer g) ![1,2,2] * g 8 * g 11) := by
  rw [atom0063_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0063_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145341120 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063Coded : CoefficientMerge.Poly := [(155, -4), (479, -8), (803, -16), (1127, -16), (1451, -16), (1775, -16), (2099, -16), (2423, -16), (2747, -16), (2765, -16), (2783, -16), (2801, -16), (2802, -8), (2804, 8), (2805, 12), (2806, 16), (2807, 18)]
theorem atom0063Coded_decode : atom0063 = SparsePolynomial.decodeCubic 18 atom0063Coded := by decide +kernel
theorem atom0063Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (145341120 : Int) atom0063Coded) := by
  have h := atom0063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0064 : SparsePolynomial.Poly := [([0,8,13], -4), ([1,8,13], -8), ([2,8,13], -16), ([3,8,13], -16), ([4,8,13], -16), ([5,8,13], -16), ([6,8,13], -16), ([7,8,13], -16), ([8,8,13], -16), ([8,9,13], -16), ([8,10,13], -16), ([8,11,13], -16), ([8,12,13], -8), ([8,13,14], 8), ([8,13,15], 12), ([8,13,16], 16), ([8,13,17], 18)]
theorem atom0064_data : atom0064 = SparsePolynomial.monoTimes [8,13] 1 base07 := by decide +kernel
theorem eval_atom0064 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0064 = (quadB (outer g) ![1,2,2] * g 8 * g 13) := by
  rw [atom0064_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0064_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97236480 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064Coded : CoefficientMerge.Poly := [(157, -4), (481, -8), (805, -16), (1129, -16), (1453, -16), (1777, -16), (2101, -16), (2425, -16), (2749, -16), (2767, -16), (2785, -16), (2803, -16), (2821, -8), (2840, 8), (2841, 12), (2842, 16), (2843, 18)]
theorem atom0064Coded_decode : atom0064 = SparsePolynomial.decodeCubic 18 atom0064Coded := by decide +kernel
theorem atom0064Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (97236480 : Int) atom0064Coded) := by
  have h := atom0064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0065 : SparsePolynomial.Poly := [([0,8,15], -4), ([1,8,15], -8), ([2,8,15], -16), ([3,8,15], -16), ([4,8,15], -16), ([5,8,15], -16), ([6,8,15], -16), ([7,8,15], -16), ([8,8,15], -16), ([8,9,15], -16), ([8,10,15], -16), ([8,11,15], -16), ([8,12,15], -8), ([8,14,15], 8), ([8,15,15], 12), ([8,15,16], 16), ([8,15,17], 18)]
theorem atom0065_data : atom0065 = SparsePolynomial.monoTimes [8,15] 1 base07 := by decide +kernel
theorem eval_atom0065 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0065 = (quadB (outer g) ![1,2,2] * g 8 * g 15) := by
  rw [atom0065_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0065_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110616960 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065Coded : CoefficientMerge.Poly := [(159, -4), (483, -8), (807, -16), (1131, -16), (1455, -16), (1779, -16), (2103, -16), (2427, -16), (2751, -16), (2769, -16), (2787, -16), (2805, -16), (2823, -8), (2859, 8), (2877, 12), (2878, 16), (2879, 18)]
theorem atom0065Coded_decode : atom0065 = SparsePolynomial.decodeCubic 18 atom0065Coded := by decide +kernel
theorem atom0065Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (110616960 : Int) atom0065Coded) := by
  have h := atom0065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0066 : SparsePolynomial.Poly := [([0,8,16], -4), ([1,8,16], -8), ([2,8,16], -16), ([3,8,16], -16), ([4,8,16], -16), ([5,8,16], -16), ([6,8,16], -16), ([7,8,16], -16), ([8,8,16], -16), ([8,9,16], -16), ([8,10,16], -16), ([8,11,16], -16), ([8,12,16], -8), ([8,14,16], 8), ([8,15,16], 12), ([8,16,16], 16), ([8,16,17], 18)]
theorem atom0066_data : atom0066 = SparsePolynomial.monoTimes [8,16] 1 base07 := by decide +kernel
theorem eval_atom0066 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0066 = (quadB (outer g) ![1,2,2] * g 8 * g 16) := by
  rw [atom0066_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0066_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (255247680 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066Coded : CoefficientMerge.Poly := [(160, -4), (484, -8), (808, -16), (1132, -16), (1456, -16), (1780, -16), (2104, -16), (2428, -16), (2752, -16), (2770, -16), (2788, -16), (2806, -16), (2824, -8), (2860, 8), (2878, 12), (2896, 16), (2897, 18)]
theorem atom0066Coded_decode : atom0066 = SparsePolynomial.decodeCubic 18 atom0066Coded := by decide +kernel
theorem atom0066Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (255247680 : Int) atom0066Coded) := by
  have h := atom0066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0067 : SparsePolynomial.Poly := [([0,8,17], -4), ([1,8,17], -8), ([2,8,17], -16), ([3,8,17], -16), ([4,8,17], -16), ([5,8,17], -16), ([6,8,17], -16), ([7,8,17], -16), ([8,8,17], -16), ([8,9,17], -16), ([8,10,17], -16), ([8,11,17], -16), ([8,12,17], -8), ([8,14,17], 8), ([8,15,17], 12), ([8,16,17], 16), ([8,17,17], 18)]
theorem atom0067_data : atom0067 = SparsePolynomial.monoTimes [8,17] 1 base07 := by decide +kernel
theorem eval_atom0067 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0067 = (quadB (outer g) ![1,2,2] * g 8 * g 17) := by
  rw [atom0067_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0067_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171391680 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067Coded : CoefficientMerge.Poly := [(161, -4), (485, -8), (809, -16), (1133, -16), (1457, -16), (1781, -16), (2105, -16), (2429, -16), (2753, -16), (2771, -16), (2789, -16), (2807, -16), (2825, -8), (2861, 8), (2879, 12), (2897, 16), (2915, 18)]
theorem atom0067Coded_decode : atom0067 = SparsePolynomial.decodeCubic 18 atom0067Coded := by decide +kernel
theorem atom0067Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (171391680 : Int) atom0067Coded) := by
  have h := atom0067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0068 : SparsePolynomial.Poly := [([0,9,10], -4), ([1,9,10], -8), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -8), ([9,10,14], 8), ([9,10,15], 12), ([9,10,16], 16), ([9,10,17], 18)]
theorem atom0068_data : atom0068 = SparsePolynomial.monoTimes [9,10] 1 base07 := by decide +kernel
theorem eval_atom0068 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0068 = (quadB (outer g) ![1,2,2] * g 9 * g 10) := by
  rw [atom0068_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0068_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48652800 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068Coded : CoefficientMerge.Poly := [(172, -4), (496, -8), (820, -16), (1144, -16), (1468, -16), (1792, -16), (2116, -16), (2440, -16), (2764, -16), (3088, -16), (3106, -16), (3107, -16), (3108, -8), (3110, 8), (3111, 12), (3112, 16), (3113, 18)]
theorem atom0068Coded_decode : atom0068 = SparsePolynomial.decodeCubic 18 atom0068Coded := by decide +kernel
theorem atom0068Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (48652800 : Int) atom0068Coded) := by
  have h := atom0068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0069 : SparsePolynomial.Poly := [([0,9,11], -4), ([1,9,11], -8), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -8), ([9,11,14], 8), ([9,11,15], 12), ([9,11,16], 16), ([9,11,17], 18)]
theorem atom0069_data : atom0069 = SparsePolynomial.monoTimes [9,11] 1 base07 := by decide +kernel
theorem eval_atom0069 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0069 = (quadB (outer g) ![1,2,2] * g 9 * g 11) := by
  rw [atom0069_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0069_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132585600 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069Coded : CoefficientMerge.Poly := [(173, -4), (497, -8), (821, -16), (1145, -16), (1469, -16), (1793, -16), (2117, -16), (2441, -16), (2765, -16), (3089, -16), (3107, -16), (3125, -16), (3126, -8), (3128, 8), (3129, 12), (3130, 16), (3131, 18)]
theorem atom0069Coded_decode : atom0069 = SparsePolynomial.decodeCubic 18 atom0069Coded := by decide +kernel
theorem atom0069Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (132585600 : Int) atom0069Coded) := by
  have h := atom0069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0070 : SparsePolynomial.Poly := [([0,9,12], -4), ([1,9,12], -8), ([2,9,12], -16), ([3,9,12], -16), ([4,9,12], -16), ([5,9,12], -16), ([6,9,12], -16), ([7,9,12], -16), ([8,9,12], -16), ([9,9,12], -16), ([9,10,12], -16), ([9,11,12], -16), ([9,12,12], -8), ([9,12,14], 8), ([9,12,15], 12), ([9,12,16], 16), ([9,12,17], 18)]
theorem atom0070_data : atom0070 = SparsePolynomial.monoTimes [9,12] 1 base07 := by decide +kernel
theorem eval_atom0070 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0070 = (quadB (outer g) ![1,2,2] * g 9 * g 12) := by
  rw [atom0070_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0070_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13571460 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070Coded : CoefficientMerge.Poly := [(174, -4), (498, -8), (822, -16), (1146, -16), (1470, -16), (1794, -16), (2118, -16), (2442, -16), (2766, -16), (3090, -16), (3108, -16), (3126, -16), (3144, -8), (3146, 8), (3147, 12), (3148, 16), (3149, 18)]
theorem atom0070Coded_decode : atom0070 = SparsePolynomial.decodeCubic 18 atom0070Coded := by decide +kernel
theorem atom0070Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13571460 : Int) atom0070Coded) := by
  have h := atom0070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0071 : SparsePolynomial.Poly := [([0,9,13], -4), ([1,9,13], -8), ([2,9,13], -16), ([3,9,13], -16), ([4,9,13], -16), ([5,9,13], -16), ([6,9,13], -16), ([7,9,13], -16), ([8,9,13], -16), ([9,9,13], -16), ([9,10,13], -16), ([9,11,13], -16), ([9,12,13], -8), ([9,13,14], 8), ([9,13,15], 12), ([9,13,16], 16), ([9,13,17], 18)]
theorem atom0071_data : atom0071 = SparsePolynomial.monoTimes [9,13] 1 base07 := by decide +kernel
theorem eval_atom0071 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0071 = (quadB (outer g) ![1,2,2] * g 9 * g 13) := by
  rw [atom0071_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0071_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91971660 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071Coded : CoefficientMerge.Poly := [(175, -4), (499, -8), (823, -16), (1147, -16), (1471, -16), (1795, -16), (2119, -16), (2443, -16), (2767, -16), (3091, -16), (3109, -16), (3127, -16), (3145, -8), (3164, 8), (3165, 12), (3166, 16), (3167, 18)]
theorem atom0071Coded_decode : atom0071 = SparsePolynomial.decodeCubic 18 atom0071Coded := by decide +kernel
theorem atom0071Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (91971660 : Int) atom0071Coded) := by
  have h := atom0071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0072 : SparsePolynomial.Poly := [([0,9,15], -4), ([1,9,15], -8), ([2,9,15], -16), ([3,9,15], -16), ([4,9,15], -16), ([5,9,15], -16), ([6,9,15], -16), ([7,9,15], -16), ([8,9,15], -16), ([9,9,15], -16), ([9,10,15], -16), ([9,11,15], -16), ([9,12,15], -8), ([9,14,15], 8), ([9,15,15], 12), ([9,15,16], 16), ([9,15,17], 18)]
theorem atom0072_data : atom0072 = SparsePolynomial.monoTimes [9,15] 1 base07 := by decide +kernel
theorem eval_atom0072 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0072 = (quadB (outer g) ![1,2,2] * g 9 * g 15) := by
  rw [atom0072_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0072_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70656420 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072Coded : CoefficientMerge.Poly := [(177, -4), (501, -8), (825, -16), (1149, -16), (1473, -16), (1797, -16), (2121, -16), (2445, -16), (2769, -16), (3093, -16), (3111, -16), (3129, -16), (3147, -8), (3183, 8), (3201, 12), (3202, 16), (3203, 18)]
theorem atom0072Coded_decode : atom0072 = SparsePolynomial.decodeCubic 18 atom0072Coded := by decide +kernel
theorem atom0072Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (70656420 : Int) atom0072Coded) := by
  have h := atom0072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0073 : SparsePolynomial.Poly := [([0,9,16], -4), ([1,9,16], -8), ([2,9,16], -16), ([3,9,16], -16), ([4,9,16], -16), ([5,9,16], -16), ([6,9,16], -16), ([7,9,16], -16), ([8,9,16], -16), ([9,9,16], -16), ([9,10,16], -16), ([9,11,16], -16), ([9,12,16], -8), ([9,14,16], 8), ([9,15,16], 12), ([9,16,16], 16), ([9,16,17], 18)]
theorem atom0073_data : atom0073 = SparsePolynomial.monoTimes [9,16] 1 base07 := by decide +kernel
theorem eval_atom0073 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0073 = (quadB (outer g) ![1,2,2] * g 9 * g 16) := by
  rw [atom0073_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0073_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198298740 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073Coded : CoefficientMerge.Poly := [(178, -4), (502, -8), (826, -16), (1150, -16), (1474, -16), (1798, -16), (2122, -16), (2446, -16), (2770, -16), (3094, -16), (3112, -16), (3130, -16), (3148, -8), (3184, 8), (3202, 12), (3220, 16), (3221, 18)]
theorem atom0073Coded_decode : atom0073 = SparsePolynomial.decodeCubic 18 atom0073Coded := by decide +kernel
theorem atom0073Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (198298740 : Int) atom0073Coded) := by
  have h := atom0073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0074 : SparsePolynomial.Poly := [([0,9,17], -4), ([1,9,17], -8), ([2,9,17], -16), ([3,9,17], -16), ([4,9,17], -16), ([5,9,17], -16), ([6,9,17], -16), ([7,9,17], -16), ([8,9,17], -16), ([9,9,17], -16), ([9,10,17], -16), ([9,11,17], -16), ([9,12,17], -8), ([9,14,17], 8), ([9,15,17], 12), ([9,16,17], 16), ([9,17,17], 18)]
theorem atom0074_data : atom0074 = SparsePolynomial.monoTimes [9,17] 1 base07 := by decide +kernel
theorem eval_atom0074 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0074 = (quadB (outer g) ![1,2,2] * g 9 * g 17) := by
  rw [atom0074_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0074_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98583300 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074Coded : CoefficientMerge.Poly := [(179, -4), (503, -8), (827, -16), (1151, -16), (1475, -16), (1799, -16), (2123, -16), (2447, -16), (2771, -16), (3095, -16), (3113, -16), (3131, -16), (3149, -8), (3185, 8), (3203, 12), (3221, 16), (3239, 18)]
theorem atom0074Coded_decode : atom0074 = SparsePolynomial.decodeCubic 18 atom0074Coded := by decide +kernel
theorem atom0074Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (98583300 : Int) atom0074Coded) := by
  have h := atom0074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0075 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -8), ([10,12,14], 8), ([10,12,15], 12), ([10,12,16], 16), ([10,12,17], 18)]
theorem atom0075_data : atom0075 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0075 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0075 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0075_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0075_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30609180 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075Coded : CoefficientMerge.Poly := [(192, -4), (516, -8), (840, -16), (1164, -16), (1488, -16), (1812, -16), (2136, -16), (2460, -16), (2784, -16), (3108, -16), (3432, -16), (3450, -16), (3468, -8), (3470, 8), (3471, 12), (3472, 16), (3473, 18)]
theorem atom0075Coded_decode : atom0075 = SparsePolynomial.decodeCubic 18 atom0075Coded := by decide +kernel
theorem atom0075Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (30609180 : Int) atom0075Coded) := by
  have h := atom0075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0076 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -8), ([10,13,14], 8), ([10,13,15], 12), ([10,13,16], 16), ([10,13,17], 18)]
theorem atom0076_data : atom0076 = SparsePolynomial.monoTimes [10,13] 1 base07 := by decide +kernel
theorem eval_atom0076 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0076 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0076_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0076_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82673940 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076Coded : CoefficientMerge.Poly := [(193, -4), (517, -8), (841, -16), (1165, -16), (1489, -16), (1813, -16), (2137, -16), (2461, -16), (2785, -16), (3109, -16), (3433, -16), (3451, -16), (3469, -8), (3488, 8), (3489, 12), (3490, 16), (3491, 18)]
theorem atom0076Coded_decode : atom0076 = SparsePolynomial.decodeCubic 18 atom0076Coded := by decide +kernel
theorem atom0076Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (82673940 : Int) atom0076Coded) := by
  have h := atom0076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0077 : SparsePolynomial.Poly := [([0,10,15], -4), ([1,10,15], -8), ([2,10,15], -16), ([3,10,15], -16), ([4,10,15], -16), ([5,10,15], -16), ([6,10,15], -16), ([7,10,15], -16), ([8,10,15], -16), ([9,10,15], -16), ([10,10,15], -16), ([10,11,15], -16), ([10,12,15], -8), ([10,14,15], 8), ([10,15,15], 12), ([10,15,16], 16), ([10,15,17], 18)]
theorem atom0077_data : atom0077 = SparsePolynomial.monoTimes [10,15] 1 base07 := by decide +kernel
theorem eval_atom0077 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0077 = (quadB (outer g) ![1,2,2] * g 10 * g 15) := by
  rw [atom0077_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0077_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7310460 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077Coded : CoefficientMerge.Poly := [(195, -4), (519, -8), (843, -16), (1167, -16), (1491, -16), (1815, -16), (2139, -16), (2463, -16), (2787, -16), (3111, -16), (3435, -16), (3453, -16), (3471, -8), (3507, 8), (3525, 12), (3526, 16), (3527, 18)]
theorem atom0077Coded_decode : atom0077 = SparsePolynomial.decodeCubic 18 atom0077Coded := by decide +kernel
theorem atom0077Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7310460 : Int) atom0077Coded) := by
  have h := atom0077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0078 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -8), ([10,14,16], 8), ([10,15,16], 12), ([10,16,16], 16), ([10,16,17], 18)]
theorem atom0078_data : atom0078 = SparsePolynomial.monoTimes [10,16] 1 base07 := by decide +kernel
theorem eval_atom0078 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0078 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0078_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0078_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109255980 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078Coded : CoefficientMerge.Poly := [(196, -4), (520, -8), (844, -16), (1168, -16), (1492, -16), (1816, -16), (2140, -16), (2464, -16), (2788, -16), (3112, -16), (3436, -16), (3454, -16), (3472, -8), (3508, 8), (3526, 12), (3544, 16), (3545, 18)]
theorem atom0078Coded_decode : atom0078 = SparsePolynomial.decodeCubic 18 atom0078Coded := by decide +kernel
theorem atom0078Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (109255980 : Int) atom0078Coded) := by
  have h := atom0078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0079 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -8), ([11,12,14], 8), ([11,12,15], 12), ([11,12,16], 16), ([11,12,17], 18)]
theorem atom0079_data : atom0079 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0079 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0079 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0079_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0079_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30159360 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079Coded : CoefficientMerge.Poly := [(210, -4), (534, -8), (858, -16), (1182, -16), (1506, -16), (1830, -16), (2154, -16), (2478, -16), (2802, -16), (3126, -16), (3450, -16), (3774, -16), (3792, -8), (3794, 8), (3795, 12), (3796, 16), (3797, 18)]
theorem atom0079Coded_decode : atom0079 = SparsePolynomial.decodeCubic 18 atom0079Coded := by decide +kernel
theorem atom0079Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (30159360 : Int) atom0079Coded) := by
  have h := atom0079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0080 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -8), ([11,13,14], 8), ([11,13,15], 12), ([11,13,16], 16), ([11,13,17], 18)]
theorem atom0080_data : atom0080 = SparsePolynomial.monoTimes [11,13] 1 base07 := by decide +kernel
theorem eval_atom0080 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0080_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69914880 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080Coded : CoefficientMerge.Poly := [(211, -4), (535, -8), (859, -16), (1183, -16), (1507, -16), (1831, -16), (2155, -16), (2479, -16), (2803, -16), (3127, -16), (3451, -16), (3775, -16), (3793, -8), (3812, 8), (3813, 12), (3814, 16), (3815, 18)]
theorem atom0080Coded_decode : atom0080 = SparsePolynomial.decodeCubic 18 atom0080Coded := by decide +kernel
theorem atom0080Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (69914880 : Int) atom0080Coded) := by
  have h := atom0080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0081 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -14), ([0,1,13], -10), ([0,1,14], -2), ([0,1,15], 2), ([0,1,16], 10), ([0,1,17], 18)]
theorem atom0081_data : atom0081 = SparsePolynomial.monoTimes [0,1] 1 base08 := by decide +kernel
theorem eval_atom0081 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0081_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28062720 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081Coded : CoefficientMerge.Poly := [(1, -8), (19, -12), (20, -16), (21, -16), (22, -16), (23, -16), (24, -16), (25, -16), (26, -16), (27, -16), (28, -16), (29, -16), (30, -14), (31, -10), (32, -2), (33, 2), (34, 10), (35, 18)]
theorem atom0081Coded_decode : atom0081 = SparsePolynomial.decodeCubic 18 atom0081Coded := by decide +kernel
theorem atom0081Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (28062720 : Int) atom0081Coded) := by
  have h := atom0081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0082 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -14), ([0,2,13], -10), ([0,2,14], -2), ([0,2,15], 2), ([0,2,16], 10), ([0,2,17], 18)]
theorem atom0082_data : atom0082 = SparsePolynomial.monoTimes [0,2] 1 base08 := by decide +kernel
theorem eval_atom0082 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0082_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41045760 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082Coded : CoefficientMerge.Poly := [(2, -8), (20, -12), (38, -16), (39, -16), (40, -16), (41, -16), (42, -16), (43, -16), (44, -16), (45, -16), (46, -16), (47, -16), (48, -14), (49, -10), (50, -2), (51, 2), (52, 10), (53, 18)]
theorem atom0082Coded_decode : atom0082 = SparsePolynomial.decodeCubic 18 atom0082Coded := by decide +kernel
theorem atom0082Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (41045760 : Int) atom0082Coded) := by
  have h := atom0082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0083 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -14), ([0,3,13], -10), ([0,3,14], -2), ([0,3,15], 2), ([0,3,16], 10), ([0,3,17], 18)]
theorem atom0083_data : atom0083 = SparsePolynomial.monoTimes [0,3] 1 base08 := by decide +kernel
theorem eval_atom0083 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0083_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54028800 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083Coded : CoefficientMerge.Poly := [(3, -8), (21, -12), (39, -16), (57, -16), (58, -16), (59, -16), (60, -16), (61, -16), (62, -16), (63, -16), (64, -16), (65, -16), (66, -14), (67, -10), (68, -2), (69, 2), (70, 10), (71, 18)]
theorem atom0083Coded_decode : atom0083 = SparsePolynomial.decodeCubic 18 atom0083Coded := by decide +kernel
theorem atom0083Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (54028800 : Int) atom0083Coded) := by
  have h := atom0083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0084 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -14), ([0,4,13], -10), ([0,4,14], -2), ([0,4,15], 2), ([0,4,16], 10), ([0,4,17], 18)]
theorem atom0084_data : atom0084 = SparsePolynomial.monoTimes [0,4] 1 base08 := by decide +kernel
theorem eval_atom0084 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0084_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67011840 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084Coded : CoefficientMerge.Poly := [(4, -8), (22, -12), (40, -16), (58, -16), (76, -16), (77, -16), (78, -16), (79, -16), (80, -16), (81, -16), (82, -16), (83, -16), (84, -14), (85, -10), (86, -2), (87, 2), (88, 10), (89, 18)]
theorem atom0084Coded_decode : atom0084 = SparsePolynomial.decodeCubic 18 atom0084Coded := by decide +kernel
theorem atom0084Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (67011840 : Int) atom0084Coded) := by
  have h := atom0084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0085 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -14), ([0,5,13], -10), ([0,5,14], -2), ([0,5,15], 2), ([0,5,16], 10), ([0,5,17], 18)]
theorem atom0085_data : atom0085 = SparsePolynomial.monoTimes [0,5] 1 base08 := by decide +kernel
theorem eval_atom0085 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0085_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79994880 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085Coded : CoefficientMerge.Poly := [(5, -8), (23, -12), (41, -16), (59, -16), (77, -16), (95, -16), (96, -16), (97, -16), (98, -16), (99, -16), (100, -16), (101, -16), (102, -14), (103, -10), (104, -2), (105, 2), (106, 10), (107, 18)]
theorem atom0085Coded_decode : atom0085 = SparsePolynomial.decodeCubic 18 atom0085Coded := by decide +kernel
theorem atom0085Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (79994880 : Int) atom0085Coded) := by
  have h := atom0085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0086 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -14), ([0,6,13], -10), ([0,6,14], -2), ([0,6,15], 2), ([0,6,16], 10), ([0,6,17], 18)]
theorem atom0086_data : atom0086 = SparsePolynomial.monoTimes [0,6] 1 base08 := by decide +kernel
theorem eval_atom0086 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0086_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (92977920 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086Coded : CoefficientMerge.Poly := [(6, -8), (24, -12), (42, -16), (60, -16), (78, -16), (96, -16), (114, -16), (115, -16), (116, -16), (117, -16), (118, -16), (119, -16), (120, -14), (121, -10), (122, -2), (123, 2), (124, 10), (125, 18)]
theorem atom0086Coded_decode : atom0086 = SparsePolynomial.decodeCubic 18 atom0086Coded := by decide +kernel
theorem atom0086Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (92977920 : Int) atom0086Coded) := by
  have h := atom0086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0087 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -14), ([0,7,13], -10), ([0,7,14], -2), ([0,7,15], 2), ([0,7,16], 10), ([0,7,17], 18)]
theorem atom0087_data : atom0087 = SparsePolynomial.monoTimes [0,7] 1 base08 := by decide +kernel
theorem eval_atom0087 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0087_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105960960 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087Coded : CoefficientMerge.Poly := [(7, -8), (25, -12), (43, -16), (61, -16), (79, -16), (97, -16), (115, -16), (133, -16), (134, -16), (135, -16), (136, -16), (137, -16), (138, -14), (139, -10), (140, -2), (141, 2), (142, 10), (143, 18)]
theorem atom0087Coded_decode : atom0087 = SparsePolynomial.decodeCubic 18 atom0087Coded := by decide +kernel
theorem atom0087Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (105960960 : Int) atom0087Coded) := by
  have h := atom0087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0088 : SparsePolynomial.Poly := [([0,0,8], -8), ([0,1,8], -12), ([0,2,8], -16), ([0,3,8], -16), ([0,4,8], -16), ([0,5,8], -16), ([0,6,8], -16), ([0,7,8], -16), ([0,8,8], -16), ([0,8,9], -16), ([0,8,10], -16), ([0,8,11], -16), ([0,8,12], -14), ([0,8,13], -10), ([0,8,14], -2), ([0,8,15], 2), ([0,8,16], 10), ([0,8,17], 18)]
theorem atom0088_data : atom0088 = SparsePolynomial.monoTimes [0,8] 1 base08 := by decide +kernel
theorem eval_atom0088 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = (quadB (outer g) ![2,2,1] * g 0 * g 8) := by
  rw [atom0088_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112539840 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088Coded : CoefficientMerge.Poly := [(8, -8), (26, -12), (44, -16), (62, -16), (80, -16), (98, -16), (116, -16), (134, -16), (152, -16), (153, -16), (154, -16), (155, -16), (156, -14), (157, -10), (158, -2), (159, 2), (160, 10), (161, 18)]
theorem atom0088Coded_decode : atom0088 = SparsePolynomial.decodeCubic 18 atom0088Coded := by decide +kernel
theorem atom0088Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (112539840 : Int) atom0088Coded) := by
  have h := atom0088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0089 : SparsePolynomial.Poly := [([0,0,9], -8), ([0,1,9], -12), ([0,2,9], -16), ([0,3,9], -16), ([0,4,9], -16), ([0,5,9], -16), ([0,6,9], -16), ([0,7,9], -16), ([0,8,9], -16), ([0,9,9], -16), ([0,9,10], -16), ([0,9,11], -16), ([0,9,12], -14), ([0,9,13], -10), ([0,9,14], -2), ([0,9,15], 2), ([0,9,16], 10), ([0,9,17], 18)]
theorem atom0089_data : atom0089 = SparsePolynomial.monoTimes [0,9] 1 base08 := by decide +kernel
theorem eval_atom0089 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = (quadB (outer g) ![2,2,1] * g 0 * g 9) := by
  rw [atom0089_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126651840 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089Coded : CoefficientMerge.Poly := [(9, -8), (27, -12), (45, -16), (63, -16), (81, -16), (99, -16), (117, -16), (135, -16), (153, -16), (171, -16), (172, -16), (173, -16), (174, -14), (175, -10), (176, -2), (177, 2), (178, 10), (179, 18)]
theorem atom0089Coded_decode : atom0089 = SparsePolynomial.decodeCubic 18 atom0089Coded := by decide +kernel
theorem atom0089Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (126651840 : Int) atom0089Coded) := by
  have h := atom0089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0090 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -16), ([0,7,10], -16), ([0,8,10], -16), ([0,9,10], -16), ([0,10,10], -16), ([0,10,11], -16), ([0,10,12], -14), ([0,10,13], -10), ([0,10,14], -2), ([0,10,15], 2), ([0,10,16], 10), ([0,10,17], 18)]
theorem atom0090_data : atom0090 = SparsePolynomial.monoTimes [0,10] 1 base08 := by decide +kernel
theorem eval_atom0090 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0090_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137618880 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090Coded : CoefficientMerge.Poly := [(10, -8), (28, -12), (46, -16), (64, -16), (82, -16), (100, -16), (118, -16), (136, -16), (154, -16), (172, -16), (190, -16), (191, -16), (192, -14), (193, -10), (194, -2), (195, 2), (196, 10), (197, 18)]
theorem atom0090Coded_decode : atom0090 = SparsePolynomial.decodeCubic 18 atom0090Coded := by decide +kernel
theorem atom0090Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (137618880 : Int) atom0090Coded) := by
  have h := atom0090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0091 : SparsePolynomial.Poly := [([0,0,11], -8), ([0,1,11], -12), ([0,2,11], -16), ([0,3,11], -16), ([0,4,11], -16), ([0,5,11], -16), ([0,6,11], -16), ([0,7,11], -16), ([0,8,11], -16), ([0,9,11], -16), ([0,10,11], -16), ([0,11,11], -16), ([0,11,12], -14), ([0,11,13], -10), ([0,11,14], -2), ([0,11,15], 2), ([0,11,16], 10), ([0,11,17], 18)]
theorem atom0091_data : atom0091 = SparsePolynomial.monoTimes [0,11] 1 base08 := by decide +kernel
theorem eval_atom0091 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = (quadB (outer g) ![2,2,1] * g 0 * g 11) := by
  rw [atom0091_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157893120 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091Coded : CoefficientMerge.Poly := [(11, -8), (29, -12), (47, -16), (65, -16), (83, -16), (101, -16), (119, -16), (137, -16), (155, -16), (173, -16), (191, -16), (209, -16), (210, -14), (211, -10), (212, -2), (213, 2), (214, 10), (215, 18)]
theorem atom0091Coded_decode : atom0091 = SparsePolynomial.decodeCubic 18 atom0091Coded := by decide +kernel
theorem atom0091Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (157893120 : Int) atom0091Coded) := by
  have h := atom0091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0092 : SparsePolynomial.Poly := [([0,0,16], -8), ([0,1,16], -12), ([0,2,16], -16), ([0,3,16], -16), ([0,4,16], -16), ([0,5,16], -16), ([0,6,16], -16), ([0,7,16], -16), ([0,8,16], -16), ([0,9,16], -16), ([0,10,16], -16), ([0,11,16], -16), ([0,12,16], -14), ([0,13,16], -10), ([0,14,16], -2), ([0,15,16], 2), ([0,16,16], 10), ([0,16,17], 18)]
theorem atom0092_data : atom0092 = SparsePolynomial.monoTimes [0,16] 1 base08 := by decide +kernel
theorem eval_atom0092 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = (quadB (outer g) ![2,2,1] * g 0 * g 16) := by
  rw [atom0092_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30885120 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092Coded : CoefficientMerge.Poly := [(16, -8), (34, -12), (52, -16), (70, -16), (88, -16), (106, -16), (124, -16), (142, -16), (160, -16), (178, -16), (196, -16), (214, -16), (232, -14), (250, -10), (268, -2), (286, 2), (304, 10), (305, 18)]
theorem atom0092Coded_decode : atom0092 = SparsePolynomial.decodeCubic 18 atom0092Coded := by decide +kernel
theorem atom0092Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (30885120 : Int) atom0092Coded) := by
  have h := atom0092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0093 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -14), ([1,1,13], -10), ([1,1,14], -2), ([1,1,15], 2), ([1,1,16], 10), ([1,1,17], 18)]
theorem atom0093_data : atom0093 = SparsePolynomial.monoTimes [1,1] 1 base08 := by decide +kernel
theorem eval_atom0093 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0093_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58044000 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093Coded : CoefficientMerge.Poly := [(19, -8), (343, -12), (344, -16), (345, -16), (346, -16), (347, -16), (348, -16), (349, -16), (350, -16), (351, -16), (352, -16), (353, -16), (354, -14), (355, -10), (356, -2), (357, 2), (358, 10), (359, 18)]
theorem atom0093Coded_decode : atom0093 = SparsePolynomial.decodeCubic 18 atom0093Coded := by decide +kernel
theorem atom0093Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (58044000 : Int) atom0093Coded) := by
  have h := atom0093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0094 : SparsePolynomial.Poly := [([0,1,17], -8), ([1,1,17], -12), ([1,2,17], -16), ([1,3,17], -16), ([1,4,17], -16), ([1,5,17], -16), ([1,6,17], -16), ([1,7,17], -16), ([1,8,17], -16), ([1,9,17], -16), ([1,10,17], -16), ([1,11,17], -16), ([1,12,17], -14), ([1,13,17], -10), ([1,14,17], -2), ([1,15,17], 2), ([1,16,17], 10), ([1,17,17], 18)]
theorem atom0094_data : atom0094 = SparsePolynomial.monoTimes [1,17] 1 base08 := by decide +kernel
theorem eval_atom0094 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = (quadB (outer g) ![2,2,1] * g 1 * g 17) := by
  rw [atom0094_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3519600 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094Coded : CoefficientMerge.Poly := [(35, -8), (359, -12), (377, -16), (395, -16), (413, -16), (431, -16), (449, -16), (467, -16), (485, -16), (503, -16), (521, -16), (539, -16), (557, -14), (575, -10), (593, -2), (611, 2), (629, 10), (647, 18)]
theorem atom0094Coded_decode : atom0094 = SparsePolynomial.decodeCubic 18 atom0094Coded := by decide +kernel
theorem atom0094Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3519600 : Int) atom0094Coded) := by
  have h := atom0094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block001 : CoefficientMerge.Poly := [(0, -120637440), (1, -465776640), (2, -569640960), (3, -673505280), (4, -777369600), (5, -881233920), (6, -985098240), (7, -1088962560), (8, -1192826880), (9, -1296691200), (10, -1400555520), (11, -1504419840), (12, -241274880), (13, -241274880), (14, -241274880), (15, -241274880), (16, -247080960), (17, -350945280), (19, -921742080), (20, -1182827520), (21, -1338624000), (22, -1494420480), (23, -1650216960), (24, -1806013440), (25, -1961809920), (26, -2143223040), (27, -2294503680), (28, -2458364160), (29, -2584995840), (30, -634152960), (31, -521902080), (32, -297400320), (33, -185149440), (34, -89994240), (35, 126026880), (38, -777369600), (39, -1762467840), (40, -1970196480), (41, -2177925120), (42, -2385653760), (43, -2593382400), (44, -2801111040), (45, -3008839680), (46, -3216568320), (47, -3424296960), (48, -815915520), (49, -651732480), (50, -323366400), (51, -159183360), (52, -458680320), (53, 387878400), (57, -985098240), (58, -2177925120), (59, -2385653760), (60, -2593382400), (61, -2801111040), (62, -3008839680), (63, -3216568320), (64, -3424296960), (65, -3672345600), (66, -997678080), (67, -878653440), (68, -349332480), (69, -287078400), (70, -580285440), (71, 410941440), (76, -1192826880), (77, -2954068992), (78, -2953368480), (79, -3037292160), (80, -3216568320), (81, -3424296960), (82, -3632025600), (83, -3858368640), (84, -1179440640), (85, -1054349520), (86, -375298560), (87, -490827120), (88, -482438320), (89, 153553680), (95, -1400555520), (96, -3369526272), (97, -3559857120), (98, -3715586400), (99, -3872995680), (100, -4043791200), (101, -4233201120), (102, -1361203200), (103, -1314666540), (104, -401264640), (105, -595979460), (106, -573472500), (107, 230665500), (114, -1608284160), (115, -3517314192), (116, -4245391200), (117, -4366673760), (118, -4487956320), (119, -4627853280), (120, -1542965760), (121, -1553985900), (122, -427230720), (123, -623659140), (124, -727964820), (125, 452163420), (133, -1816012800), (134, -4200440832), (135, -4802681280), (136, -4861871040), (137, -4939675200), (138, -1724728320), (139, -1708151400), (140, -453196800), (141, -586697400), (142, -584282520), (143, 702566280), (152, -2023741440), (153, -4510410240), (154, -5205996288), (155, -5252033280), (156, -1919299200), (157, -1858085760), (158, -568821120), (159, -561129600), (160, -389754240), (161, 989205120), (171, -2231470080), (172, -4865280000), (173, -5408739840), (174, -2153089680), (175, -1960083120), (176, -578981760), (177, -355000080), (178, -20838480), (179, 1534454640), (190, -2439198720), (191, -5086126080), (192, -2407035120), (193, -2064818640), (194, -633171840), (195, -111938160), (196, 445002960), (197, 2126194560), (209, -2646927360), (210, -2572416000), (211, -2099865600), (212, -557061120), (213, 74511360), (214, 1084769280), (215, 2491130880), (228, -120637440), (229, -241274880), (230, -241274880), (231, -241274880), (232, -432391680), (233, -350945280), (247, -120637440), (248, -241274880), (249, -241274880), (250, -308851200), (251, -350945280), (266, -120637440), (267, -241274880), (268, -61770240), (269, 482549760), (285, -120637440), (286, 61770240), (287, 482549760), (304, 308851200), (305, 1389427200), (323, 1184440320), (343, -696528000), (344, -928704000), (345, -928704000), (346, -928704000), (347, -928704000), (348, -928704000), (349, -928704000), (350, -979937280), (351, -970905600), (352, -987033600), (353, -928704000), (354, -812616000), (355, -580440000), (356, -116088000), (357, 116088000), (358, 580440000), (359, 1002556800), (368, -102466560), (369, -84403200), (370, -116659200), (376, -749952000), (377, -56313600), (386, -102466560), (387, -84403200), (388, -116659200), (389, -80640000), (391, -194181120), (393, -307722240), (394, -1252823040), (395, -477576960), (401, -721373184), (402, -304514880), (403, -56904960), (404, -102466560), (405, -84403200), (406, -116659200), (407, -37228800), (409, -285912480), (411, -767151840), (412, -1316789600), (413, -1459741920), (420, -721373184), (421, -686577600), (422, -685045440), (423, -566343360), (424, -524733120), (425, -371436480), (427, -546885720), (429, -1029388680), (430, -1758518760), (431, -1772907720), (439, -186034464), (440, -1329197760), (441, -1138242240), (442, -997606080), (443, -745283520), (445, -765863640), (447, -1136680200), (448, -2327164200), (449, -1797301320), (458, -823839744), (459, -1594800000), (460, -1329978240), (461, -953470080), (463, -814533840), (465, -1114688880), (466, -2299460400), (467, -1763885040), (476, -102466560), (477, -697267200), (478, -1705238016), (479, -1265195520), (480, -102466560), (481, -880358400), (482, -102466560), (483, -987402240), (484, -2041981440), (485, -1427447040), (495, -84403200), (496, -590284800), (497, -1145088000), (498, -192974880), (499, -820176480), (500, -84403200), (501, -649654560), (502, -1586389920), (503, -844980000), (514, -116659200), (515, -116659200), (516, -361532640), (517, -778050720), (518, -116659200), (519, -175142880), (520, -874047840), (521, -56313600), (534, -241274880), (535, -559319040), (539, -56313600), (557, -49274400), (575, -35196000), (593, -7039200), (611, 7039200), (629, 35196000), (647, 63352800), (692, -51233280), (693, -42201600), (694, -58329600), (700, -1499904000), (710, -102466560), (711, -84403200), (712, -116659200), (713, -161280000), (715, -388362240), (717, -615444480), (718, -4005550080), (719, -842526720), (725, -1442746368), (726, -609029760), (727, -113809920), (728, -102466560), (729, -84403200), (730, -116659200), (731, -74457600), (733, -571824960), (735, -1534303680), (736, -4133483200), (737, -2806856640), (744, -1442746368), (745, -1373155200), (746, -1267624320), (747, -1048283520), (748, -932807040), (749, -742872960), (751, -1093771440), (753, -2058777360), (754, -5016941520), (755, -3433188240), (763, -372068928), (764, -2555928960), (765, -2192081280), (766, -1878552960), (767, -1490567040), (769, -1531727280), (771, -2273360400), (772, -6154232400), (773, -3481975440), (782, -1545212928), (783, -3105196800), (784, -2543297280), (785, -1906940160), (787, -1629067680), (789, -2229377760), (790, -6098824800), (791, -3415142880), (800, -102466560), (801, -1207664640), (802, -3191350272), (803, -2427924480), (804, -102466560), (805, -1658250240), (806, -102466560), (807, -1872337920), (808, -5583866880), (809, -2742266880), (819, -84403200), (820, -979507200), (821, -2205772800), (822, -301546560), (823, -1555949760), (824, -84403200), (825, -1214905920), (826, -4672683840), (827, -1577332800), (838, -116659200), (839, -116659200), (840, -606406080), (841, -1439442240), (842, -116659200), (843, -233626560), (844, -3247999680), (858, -482549760), (859, -1118638080), (862, -1499904000), (880, -749952000), (916, 749952000), (934, 1124928000), (952, 1499904000), (953, 1687392000), (1034, -51233280), (1035, -42201600), (1036, -58329600), (1037, -161280000), (1039, -388362240), (1041, -615444480), (1042, -2505646080), (1043, -842526720), (1049, -1442746368), (1050, -609029760), (1051, -113809920), (1052, -102466560), (1053, -84403200), (1054, -116659200), (1055, -235737600), (1057, -960187200), (1059, -2149748160), (1060, -5139225280), (1061, -3649383360), (1068, -1442746368), (1069, -1373155200), (1070, -1267624320), (1071, -1048283520), (1072, -932807040), (1073, -904152960), (1075, -1482133680), (1077, -2674221840), (1078, -6022683600), (1079, -4275714960), (1087, -372068928), (1088, -2555928960), (1089, -2192081280), (1090, -1878552960), (1091, -1651847040), (1093, -1920089520), (1095, -2888804880), (1096, -7159974480), (1097, -4324502160), (1106, -1545212928), (1107, -3105196800), (1108, -2543297280), (1109, -2068220160), (1111, -2017429920), (1113, -2844822240), (1114, -7104566880), (1115, -4257669600), (1124, -102466560), (1125, -1207664640), (1126, -3191350272), (1127, -2589204480), (1128, -102466560), (1129, -2046612480), (1130, -102466560), (1131, -2487782400), (1132, -6589608960), (1133, -3584793600), (1143, -84403200), (1144, -979507200), (1145, -2367052800), (1146, -301546560), (1147, -1944312000), (1148, -84403200), (1149, -1830350400), (1150, -5678425920), (1151, -2419859520), (1162, -116659200), (1163, -277939200), (1164, -606406080), (1165, -1827804480), (1166, -116659200), (1167, -849071040), (1168, -4253741760), (1169, -842526720), (1181, -161280000), (1182, -563189760), (1183, -1507000320), (1184, 80640000), (1185, -494484480), (1186, -2344366080), (1187, -661086720), (1201, -194181120), (1203, -307722240), (1204, -1252823040), (1205, -421263360), (1220, 194181120), (1221, 291271680), (1222, 388362240), (1223, 436907520), (1239, 307722240), (1240, 1252823040), (1241, 421263360), (1257, 461583360), (1258, 2494679040), (1259, 1324270080), (1276, 2505646080), (1277, 3661378560), (1295, 947842560), (1373, -1442746368), (1374, -609029760), (1375, -113809920), (1376, -51233280), (1377, -42201600), (1378, -58329600), (1379, -74457600), (1381, -571824960), (1383, -1534303680), (1384, -2633579200), (1385, -2806856640), (1391, -1442746368), (1392, -3494522496), (1393, -2929711488), (1394, -2710370688), (1395, -2491029888), (1396, -2375553408), (1397, -2260076928), (1398, -721373184), (1399, -1665596400), (1400, 721373184), (1401, -2511021264), (1402, -4707870352), (1403, -4616955216), (1410, -609029760), (1411, -1094908608), (1412, -3164958720), (1413, -2801111040), (1414, -2487582720), (1415, -2174054400), (1416, -304514880), (1417, -2103552240), (1418, 304514880), (1419, -3350891760), (1420, -6678877840), (1421, -5603673600), (1429, -113809920), (1430, -1659022848), (1431, -3219006720), (1432, -2657107200), (1433, -2095207680), (1434, -56904960), (1435, -2200892640), (1436, 56904960), (1437, -3678324000), (1438, -7118690080), (1439, -6093963360), (1448, -102466560), (1449, -1207664640), (1450, -3191350272), (1451, -2502382080), (1452, -102466560), (1453, -2230075200), (1454, -102466560), (1455, -3406641600), (1456, -6717542080), (1457, -5549123520), (1467, -84403200), (1468, -979507200), (1469, -2280230400), (1470, -301546560), (1471, -2127774720), (1472, -84403200), (1473, -2749209600), (1474, -5806359040), (1475, -4384189440), (1486, -116659200), (1487, -191116800), (1488, -606406080), (1489, -2011267200), (1490, -116659200), (1491, -1767930240), (1492, -4381674880), (1493, -2806856640), (1505, -74457600), (1506, -519778560), (1507, -1690463040), (1508, 37228800), (1509, -1478460480), (1510, -2559121600), (1511, -2723091840), (1525, -285912480), (1527, -767151840), (1528, -1316789600), (1529, -1403428320), (1544, 285912480), (1545, 428868720), (1546, 571824960), (1547, 643303080), (1563, 767151840), (1564, 1316789600), (1565, 1403428320), (1581, 1150727760), (1582, 3509488080), (1583, 3831234120), (1600, 2633579200), (1601, 5769633240), (1619, 3157713720), (1716, -1442746368), (1717, -1373155200), (1718, -1216391040), (1719, -1006081920), (1720, -874477440), (1721, -742872960), (1723, -1093771440), (1725, -2058777360), (1726, -3517037520), (1727, -3433188240), (1734, -1442746368), (1735, -3187970496), (1736, -5163833088), (1737, -4598707968), (1738, -4137447168), (1739, -3676186368), (1740, -721373184), (1741, -2625498720), (1742, 721373184), (1743, -3250077984), (1744, -6728619552), (1745, -5292074016), (1753, -1373155200), (1754, -4083525888), (1755, -5442232320), (1756, -4732600320), (1757, -4022968320), (1758, -686577600), (1759, -2722839120), (1760, 686577600), (1761, -3258288720), (1762, -6742803120), (1763, -5303531520), (1772, -1267624320), (1773, -3336702720), (1774, -5172655872), (1775, -4335955200), (1776, -685045440), (1777, -2752021680), (1778, 480112320), (1779, -3057246960), (1780, -6435842640), (1781, -4864652640), (1791, -1048283520), (1792, -2759535360), (1793, -3912526080), (1794, -783486720), (1795, -2649721200), (1796, 397536960), (1797, -2550773040), (1798, -5725937040), (1799, -3926155680), (1810, -932807040), (1811, -1675680000), (1812, -1014480000), (1813, -2533213680), (1814, 291414720), (1815, -1680293040), (1816, -4448985360), (1817, -2515021920), (1829, -742872960), (1830, -853986240), (1831, -2212409520), (1832, 371436480), (1833, -1501622640), (1834, -2774164560), (1835, -2597456160), (1849, -546885720), (1851, -1029388680), (1852, -1758518760), (1853, -1716594120), (1868, 546885720), (1869, 820328580), (1870, 1093771440), (1871, 1230492870), (1887, 1029388680), (1888, 1758518760), (1889, 1716594120), (1905, 1544083020), (1906, 4696555500), (1907, 4891015710), (1924, 3517037520), (1925, 7389855450), (1943, 3862336770), (2059, -372068928), (2060, -2504695680), (2061, -2149879680), (2062, -1820223360), (2063, -1490567040), (2065, -1531727280), (2067, -2273360400), (2068, -4654328400), (2069, -3481975440), (2077, -372068928), (2078, -4370744256), (2079, -5584943808), (2080, -4677259968), (2081, -3769576128), (2082, -186034464), (2083, -3160794960), (2084, 186034464), (2085, -4223686464), (2086, -8881180272), (2087, -6478540776), (2096, -2555928960), (2097, -5768805120), (2098, -7406706432), (2099, -6371953920), (2100, -1329197760), (2101, -3189977520), (2102, 1124264640), (2103, -2305601520), (2104, -6284828880), (2105, -3464097120), (2115, -2192081280), (2116, -4849079040), (2117, -5804017920), (2118, -1355385600), (2119, -3087677040), (2120, 969435840), (2121, -1907507760), (2122, -5719430160), (2123, -2688170400), (2134, -1878552960), (2135, -3369120000), (2136, -1487352960), (2137, -2971169520), (2138, 764287680), (2139, -1185566640), (2140, -4640530320), (2141, -1499844960), (2153, -1490567040), (2154, -1227833280), (2155, -2650365360), (2156, 745283520), (2157, -1155435120), (2158, -3163761360), (2159, -1805087520), (2173, -765863640), (2175, -1136680200), (2176, -2327164200), (2177, -1740987720), (2192, 765863640), (2193, 1148795460), (2194, 1531727280), (2195, 1723193190), (2211, 1136680200), (2212, 2327164200), (2213, 1740987720), (2229, 1705020300), (2230, 5764106700), (2231, 5169012030), (2248, 4654328400), (2249, 8718094890), (2267, 3917222370), (2402, -1493979648), (2403, -3062995200), (2404, -2484967680), (2405, -1906940160), (2407, -1629067680), (2409, -2229377760), (2410, -4598920800), (2411, -3415142880), (2420, -1545212928), (2421, -5671204608), (2422, -7060734720), (2423, -5777611008), (2424, -823839744), (2425, -3287317920), (2426, 618906624), (2427, -3019655904), (2428, -7240137312), (2429, -4534320096), (2439, -3105196800), (2440, -6426938880), (2441, -7133506560), (2442, -1811943360), (2443, -3185017440), (2444, 1425993600), (2445, -1178688480), (2446, -4750907040), (2447, -1594082880), (2458, -2543297280), (2459, -4450237440), (2460, -1819725120), (2461, -3068509920), (2462, 1096659840), (2463, -643025760), (2464, -3920378400), (2465, -685175040), (2477, -1906940160), (2478, -1436019840), (2479, -2747705760), (2480, 953470080), (2481, -799172640), (2482, -2691980640), (2483, -1269835200), (2497, -814533840), (2499, -1114688880), (2500, -2299460400), (2501, -1707571440), (2516, 814533840), (2517, 1221800760), (2518, 1629067680), (2519, 1832701140), (2535, 1114688880), (2536, 2299460400), (2537, 1707571440), (2553, 1672033320), (2554, 5678568360), (2555, 5069407140), (2572, 4598920800), (2573, 8588928780), (2591, 3842035740), (2744, -51233280), (2745, -1165463040), (2746, -3133020672), (2747, -2427924480), (2748, -102466560), (2749, -1658250240), (2750, -102466560), (2751, -1872337920), (2752, -4083962880), (2753, -2742266880), (2763, -1156431360), (2764, -5074993152), (2765, -5654492160), (2766, -914410560), (2767, -3214200000), (2768, 323527680), (2769, -2321647680), (2770, -6235947840), (2771, -3171205440), (2782, -3140116992), (2783, -5516808192), (2784, -2194984896), (2785, -3097692480), (2786, 1266986496), (2787, 123203904), (2788, -2859834048), (2789, 601485696), (2801, -2376691200), (2802, -1747745280), (2803, -2776888320), (2804, 1060262400), (2805, -128244480), (2806, -1758504960), (2807, -126126720), (2820, -51233280), (2821, -880358400), (2822, -102466560), (2823, -987402240), (2824, -2041981440), (2825, -1371133440), (2839, -51233280), (2840, 675425280), (2841, 1064371200), (2842, 1555783680), (2843, 1750256640), (2858, -51233280), (2859, 782469120), (2860, 2041981440), (2861, 1576066560), (2877, 1276170240), (2878, 4832843520), (2879, 4252738560), (2896, 4083962880), (2897, 7541658240), (2915, 3289983360), (3087, -42201600), (3088, -921177600), (3089, -2205772800), (3090, -301546560), (3091, -1555949760), (3092, -84403200), (3093, -1214905920), (3094, -3172779840), (3095, -1577332800), (3106, -937305600), (3107, -3100876800), (3108, -1297175040), (3109, -2995392000), (3110, 188160000), (3111, -864698880), (3112, -4142430720), (3113, -701582400), (3125, -2163571200), (3126, -1844781120), (3127, -2674587840), (3128, 976281600), (3129, 376121280), (3130, -1051410240), (3131, 809208000), (3144, -150773280), (3145, -820176480), (3146, 24168480), (3147, -486797040), (3148, -1369246560), (3149, -544380120), (3163, -42201600), (3164, 651370080), (3165, 1019256720), (3166, 1471546560), (3167, 1655489880), (3182, -42201600), (3183, 480848160), (3184, 1586389920), (3185, 957472800), (3201, 805675440), (3202, 3510087600), (3203, 2623621560), (3220, 3172779840), (3221, 5315516520), (3239, 1943305800), (3430, -58329600), (3431, -116659200), (3432, -606406080), (3433, -1439442240), (3434, -116659200), (3435, -233626560), (3436, -1748095680), (3449, -58329600), (3450, -1088955840), (3451, -2558080320), (3452, -116659200), (3453, -233626560), (3454, -1748095680), (3468, -303203040), (3469, -778050720), (3470, 128214240), (3471, 192167280), (3472, -384300960), (3473, 550965240), (3487, -58329600), (3488, 544732320), (3489, 875428080), (3490, 1322783040), (3491, 1488130920), (3506, -58329600), (3507, -58175520), (3508, 874047840), (3509, 233318400), (3525, 29395920), (3526, 1428039120), (3527, 364906680), (3544, 1748095680), (3545, 2199926040), (3563, 233318400), (3774, -482549760), (3775, -1118638080), (3792, -241274880), (3793, -559319040), (3794, 241274880), (3795, 361912320), (3796, 482549760), (3797, 542868480), (3812, 559319040), (3813, 838978560), (3814, 1118638080), (3815, 1258467840)]
theorem block001_data : block001 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120637440 : Int) atom0015Coded) (CoefficientMerge.scale (51233280 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42201600 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329600 : Int) atom0018Coded) (CoefficientMerge.scale (175472640 : Int) atom0019Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93744000 : Int) atom0020Coded) (CoefficientMerge.scale (10080000 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24272640 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38465280 : Int) atom0023Coded) (CoefficientMerge.scale (156602880 : Int) atom0024Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52657920 : Int) atom0025Coded) (CoefficientMerge.scale (90171648 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38064360 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7113120 : Int) atom0028Coded) (CoefficientMerge.scale (4653600 : Int) atom0029Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35739060 : Int) atom0030Coded) (CoefficientMerge.scale (95893980 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164598700 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175428540 : Int) atom0033Coded) (CoefficientMerge.scale (90171648 : Int) atom0034Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85822200 : Int) atom0035Coded) (CoefficientMerge.scale (72822360 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60242520 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51009240 : Int) atom0038Coded) (CoefficientMerge.scale (46429560 : Int) atom0039Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68360715 : Int) atom0040Coded) (CoefficientMerge.scale (128673585 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219814845 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214574265 : Int) atom0043Coded) (CoefficientMerge.scale (23254308 : Int) atom0044Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153341400 : Int) atom0045Coded) (CoefficientMerge.scale (131729880 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110118360 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93160440 : Int) atom0048Coded) (CoefficientMerge.scale (95732955 : Int) atom0049Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142085025 : Int) atom0050Coded) (CoefficientMerge.scale (290895525 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217623465 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90171648 : Int) atom0053Coded) (CoefficientMerge.scale (188799600 : Int) atom0054Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151664880 : Int) atom0055Coded) (CoefficientMerge.scale (119183760 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101816730 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139336110 : Int) atom0058Coded) (CoefficientMerge.scale (287432550 : Int) atom0059Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213446430 : Int) atom0060Coded) (CoefficientMerge.scale (63799680 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185764032 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145341120 : Int) atom0063Coded) (CoefficientMerge.scale (97236480 : Int) atom0064Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110616960 : Int) atom0065Coded) (CoefficientMerge.scale (255247680 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171391680 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48652800 : Int) atom0068Coded) (CoefficientMerge.scale (132585600 : Int) atom0069Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13571460 : Int) atom0070Coded) (CoefficientMerge.scale (91971660 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70656420 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (198298740 : Int) atom0073Coded) (CoefficientMerge.scale (98583300 : Int) atom0074Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30609180 : Int) atom0075Coded) (CoefficientMerge.scale (82673940 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7310460 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109255980 : Int) atom0078Coded) (CoefficientMerge.scale (30159360 : Int) atom0079Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69914880 : Int) atom0080Coded) (CoefficientMerge.scale (28062720 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41045760 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54028800 : Int) atom0083Coded) (CoefficientMerge.scale (67011840 : Int) atom0084Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79994880 : Int) atom0085Coded) (CoefficientMerge.scale (92977920 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105960960 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112539840 : Int) atom0088Coded) (CoefficientMerge.scale (126651840 : Int) atom0089Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137618880 : Int) atom0090Coded) (CoefficientMerge.scale (157893120 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30885120 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58044000 : Int) atom0093Coded) (CoefficientMerge.scale (3519600 : Int) atom0094Coded)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block001 := by
  rw [block001_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0015Coded_nonneg g hg hA hB) (atom0016Coded_nonneg g hg hA hB)) (add_nonneg (atom0017Coded_nonneg g hg hA hB) (add_nonneg (atom0018Coded_nonneg g hg hA hB) (atom0019Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0020Coded_nonneg g hg hA hB) (atom0021Coded_nonneg g hg hA hB)) (add_nonneg (atom0022Coded_nonneg g hg hA hB) (add_nonneg (atom0023Coded_nonneg g hg hA hB) (atom0024Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0025Coded_nonneg g hg hA hB) (atom0026Coded_nonneg g hg hA hB)) (add_nonneg (atom0027Coded_nonneg g hg hA hB) (add_nonneg (atom0028Coded_nonneg g hg hA hB) (atom0029Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0030Coded_nonneg g hg hA hB) (atom0031Coded_nonneg g hg hA hB)) (add_nonneg (atom0032Coded_nonneg g hg hA hB) (add_nonneg (atom0033Coded_nonneg g hg hA hB) (atom0034Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0035Coded_nonneg g hg hA hB) (atom0036Coded_nonneg g hg hA hB)) (add_nonneg (atom0037Coded_nonneg g hg hA hB) (add_nonneg (atom0038Coded_nonneg g hg hA hB) (atom0039Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0040Coded_nonneg g hg hA hB) (atom0041Coded_nonneg g hg hA hB)) (add_nonneg (atom0042Coded_nonneg g hg hA hB) (add_nonneg (atom0043Coded_nonneg g hg hA hB) (atom0044Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0045Coded_nonneg g hg hA hB) (atom0046Coded_nonneg g hg hA hB)) (add_nonneg (atom0047Coded_nonneg g hg hA hB) (add_nonneg (atom0048Coded_nonneg g hg hA hB) (atom0049Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0050Coded_nonneg g hg hA hB) (atom0051Coded_nonneg g hg hA hB)) (add_nonneg (atom0052Coded_nonneg g hg hA hB) (add_nonneg (atom0053Coded_nonneg g hg hA hB) (atom0054Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0055Coded_nonneg g hg hA hB) (atom0056Coded_nonneg g hg hA hB)) (add_nonneg (atom0057Coded_nonneg g hg hA hB) (add_nonneg (atom0058Coded_nonneg g hg hA hB) (atom0059Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0060Coded_nonneg g hg hA hB) (atom0061Coded_nonneg g hg hA hB)) (add_nonneg (atom0062Coded_nonneg g hg hA hB) (add_nonneg (atom0063Coded_nonneg g hg hA hB) (atom0064Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0065Coded_nonneg g hg hA hB) (atom0066Coded_nonneg g hg hA hB)) (add_nonneg (atom0067Coded_nonneg g hg hA hB) (add_nonneg (atom0068Coded_nonneg g hg hA hB) (atom0069Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0070Coded_nonneg g hg hA hB) (atom0071Coded_nonneg g hg hA hB)) (add_nonneg (atom0072Coded_nonneg g hg hA hB) (add_nonneg (atom0073Coded_nonneg g hg hA hB) (atom0074Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0075Coded_nonneg g hg hA hB) (atom0076Coded_nonneg g hg hA hB)) (add_nonneg (atom0077Coded_nonneg g hg hA hB) (add_nonneg (atom0078Coded_nonneg g hg hA hB) (atom0079Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0080Coded_nonneg g hg hA hB) (atom0081Coded_nonneg g hg hA hB)) (add_nonneg (atom0082Coded_nonneg g hg hA hB) (add_nonneg (atom0083Coded_nonneg g hg hA hB) (atom0084Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0085Coded_nonneg g hg hA hB) (atom0086Coded_nonneg g hg hA hB)) (add_nonneg (atom0087Coded_nonneg g hg hA hB) (add_nonneg (atom0088Coded_nonneg g hg hA hB) (atom0089Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0090Coded_nonneg g hg hA hB) (atom0091Coded_nonneg g hg hA hB)) (add_nonneg (atom0092Coded_nonneg g hg hA hB) (add_nonneg (atom0093Coded_nonneg g hg hA hB) (atom0094Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
