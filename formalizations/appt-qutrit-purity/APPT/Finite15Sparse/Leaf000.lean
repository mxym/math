import APPT.Finite15Sparse.Base00
import APPT.Finite15Sparse.Base01
import APPT.Finite15Sparse.Base02
import APPT.Finite15Sparse.Base03
import APPT.Finite15Sparse.Base04
import APPT.Finite15Sparse.Base05
import APPT.Finite15Sparse.Base06
import APPT.Finite15Sparse.Base07
import APPT.Finite15Sparse.Base08
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0000 : SparsePolynomial.Poly := [([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,0,12], -2), ([0,0,13], -2), ([0,0,14], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -6), ([0,1,10], -4), ([0,1,11], -4), ([0,1,12], -4), ([0,1,13], -4), ([0,1,14], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,2,9], -8), ([0,2,10], -6), ([0,2,11], -4), ([0,2,12], -4), ([0,2,13], -4), ([0,2,14], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -4), ([0,3,7], -4), ([0,3,8], -4), ([0,3,9], -8), ([0,3,10], -6), ([0,3,11], -4), ([0,3,12], -4), ([0,3,13], -4), ([0,3,14], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -4), ([0,4,7], -4), ([0,4,8], -4), ([0,4,9], -8), ([0,4,10], -6), ([0,4,11], -4), ([0,4,12], -4), ([0,4,13], -4), ([0,4,14], -4), ([0,5,5], -2), ([0,5,6], -4), ([0,5,7], -4), ([0,5,8], -4), ([0,5,9], -8), ([0,5,10], -6), ([0,5,11], -4), ([0,5,12], -4), ([0,5,13], -4), ([0,5,14], -4), ([0,6,6], -2), ([0,6,7], -4), ([0,6,8], -4), ([0,6,9], -8), ([0,6,10], -6), ([0,6,11], -4), ([0,6,12], -4), ([0,6,13], -4), ([0,6,14], -4), ([0,7,7], -2), ([0,7,8], -4), ([0,7,9], -8), ([0,7,10], -6), ([0,7,11], -4), ([0,7,12], -4), ([0,7,13], -4), ([0,7,14], -4), ([0,8,8], -2), ([0,8,9], -8), ([0,8,10], -6), ([0,8,11], -4), ([0,8,12], -4), ([0,8,13], -4), ([0,8,14], -4), ([0,9,9], -6), ([0,9,10], -10), ([0,9,11], -8), ([0,9,12], -8), ([0,9,13], -4), ([0,9,14], -4), ([0,10,10], -4), ([0,10,11], -8), ([0,10,12], -8), ([0,10,13], -4), ([0,10,14], -4), ([0,11,11], -4), ([0,11,12], -8), ([0,11,13], -4), ([0,11,14], -4), ([0,12,12], -4), ([0,12,13], -4), ([0,12,14], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -2), ([1,1,7], -2), ([1,1,8], -2), ([1,1,9], -4), ([1,1,10], -2), ([1,1,11], -2), ([1,1,12], -4), ([1,1,13], -4), ([1,1,14], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -8), ([1,2,7], -8), ([1,2,8], -8), ([1,2,9], -12), ([1,2,10], -8), ([1,2,11], -6), ([1,2,12], -10), ([1,2,13], -8), ([1,2,14], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -8), ([1,3,7], -8), ([1,3,8], -8), ([1,3,9], -12), ([1,3,10], -8), ([1,3,11], -6), ([1,3,12], -10), ([1,3,13], -8), ([1,3,14], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -8), ([1,4,7], -8), ([1,4,8], -8), ([1,4,9], -12), ([1,4,10], -8), ([1,4,11], -6), ([1,4,12], -10), ([1,4,13], -8), ([1,4,14], -8), ([1,5,5], -4), ([1,5,6], -8), ([1,5,7], -8), ([1,5,8], -8), ([1,5,9], -12), ([1,5,10], -8), ([1,5,11], -6), ([1,5,12], -10), ([1,5,13], -8), ([1,5,14], -8), ([1,6,6], -4), ([1,6,7], -8), ([1,6,8], -8), ([1,6,9], -12), ([1,6,10], -8), ([1,6,11], -6), ([1,6,12], -10), ([1,6,13], -8), ([1,6,14], -8), ([1,7,7], -4), ([1,7,8], -8), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -6), ([1,7,12], -10), ([1,7,13], -8), ([1,7,14], -8), ([1,8,8], -4), ([1,8,9], -12), ([1,8,10], -8), ([1,8,11], -6), ([1,8,12], -10), ([1,8,13], -8), ([1,8,14], -8), ([1,9,9], -8), ([1,9,10], -12), ([1,9,11], -10), ([1,9,12], -14), ([1,9,13], -8), ([1,9,14], -8), ([1,10,10], -4), ([1,10,11], -8), ([1,10,12], -12), ([1,10,13], -8), ([1,10,14], -8), ([1,11,11], -4), ([1,11,12], -8), ([1,11,13], -4), ([1,11,14], -4), ([1,12,12], -4), ([1,12,13], -4), ([1,12,14], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -6), ([2,2,7], -6), ([2,2,8], -6), ([2,2,9], -8), ([2,2,10], -6), ([2,2,11], -4), ([2,2,12], -6), ([2,2,13], -4), ([2,2,14], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -12), ([2,3,7], -12), ([2,3,8], -12), ([2,3,9], -16), ([2,3,10], -12), ([2,3,11], -8), ([2,3,12], -12), ([2,3,13], -8), ([2,3,14], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -12), ([2,4,7], -12), ([2,4,8], -12), ([2,4,9], -16), ([2,4,10], -12), ([2,4,11], -8), ([2,4,12], -12), ([2,4,13], -8), ([2,4,14], -12), ([2,5,5], -6), ([2,5,6], -12), ([2,5,7], -12), ([2,5,8], -12), ([2,5,9], -16), ([2,5,10], -12), ([2,5,11], -8), ([2,5,12], -12), ([2,5,13], -8), ([2,5,14], -12), ([2,6,6], -6), ([2,6,7], -12), ([2,6,8], -12), ([2,6,9], -16), ([2,6,10], -12), ([2,6,11], -8), ([2,6,12], -12), ([2,6,13], -8), ([2,6,14], -12), ([2,7,7], -6), ([2,7,8], -12), ([2,7,9], -16), ([2,7,10], -12), ([2,7,11], -8), ([2,7,12], -12), ([2,7,13], -8), ([2,7,14], -12), ([2,8,8], -6), ([2,8,9], -16), ([2,8,10], -12), ([2,8,11], -8), ([2,8,12], -12), ([2,8,13], -8), ([2,8,14], -12), ([2,9,9], -10), ([2,9,10], -16), ([2,9,11], -12), ([2,9,12], -16), ([2,9,13], -8), ([2,9,14], -12), ([2,10,10], -6), ([2,10,11], -10), ([2,10,12], -14), ([2,10,13], -8), ([2,10,14], -8), ([2,11,11], -4), ([2,11,12], -8), ([2,11,13], -4), ([2,11,14], -4), ([2,12,12], -4), ([2,12,13], -4), ([2,12,14], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -6), ([3,3,7], -6), ([3,3,8], -6), ([3,3,9], -8), ([3,3,10], -6), ([3,3,11], -4), ([3,3,12], -6), ([3,3,13], -4), ([3,3,14], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -12), ([3,4,7], -12), ([3,4,8], -12), ([3,4,9], -16), ([3,4,10], -12), ([3,4,11], -8), ([3,4,12], -12), ([3,4,13], -8), ([3,4,14], -12), ([3,5,5], -6), ([3,5,6], -12), ([3,5,7], -12), ([3,5,8], -12), ([3,5,9], -16), ([3,5,10], -12), ([3,5,11], -8), ([3,5,12], -12), ([3,5,13], -8), ([3,5,14], -12), ([3,6,6], -6), ([3,6,7], -12), ([3,6,8], -12), ([3,6,9], -16), ([3,6,10], -12), ([3,6,11], -8), ([3,6,12], -12), ([3,6,13], -8), ([3,6,14], -12), ([3,7,7], -6), ([3,7,8], -12), ([3,7,9], -16), ([3,7,10], -12), ([3,7,11], -8), ([3,7,12], -12), ([3,7,13], -8), ([3,7,14], -12), ([3,8,8], -6), ([3,8,9], -16), ([3,8,10], -12), ([3,8,11], -8), ([3,8,12], -12), ([3,8,13], -8), ([3,8,14], -12), ([3,9,9], -10), ([3,9,10], -16), ([3,9,11], -12), ([3,9,12], -16), ([3,9,13], -8), ([3,9,14], -12), ([3,10,10], -6), ([3,10,11], -10), ([3,10,12], -14), ([3,10,13], -8), ([3,10,14], -8), ([3,11,11], -4), ([3,11,12], -8), ([3,11,13], -4), ([3,11,14], -4), ([3,12,12], -4), ([3,12,13], -4), ([3,12,14], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -6), ([4,4,7], -6), ([4,4,8], -6), ([4,4,9], -8), ([4,4,10], -6), ([4,4,11], -4), ([4,4,12], -6), ([4,4,13], -4), ([4,4,14], -6), ([4,5,5], -6), ([4,5,6], -12), ([4,5,7], -12), ([4,5,8], -12), ([4,5,9], -16), ([4,5,10], -12), ([4,5,11], -8), ([4,5,12], -12), ([4,5,13], -8), ([4,5,14], -12), ([4,6,6], -6), ([4,6,7], -12), ([4,6,8], -12), ([4,6,9], -16), ([4,6,10], -12), ([4,6,11], -8), ([4,6,12], -12), ([4,6,13], -8), ([4,6,14], -12), ([4,7,7], -6), ([4,7,8], -12), ([4,7,9], -16), ([4,7,10], -12), ([4,7,11], -8), ([4,7,12], -12), ([4,7,13], -8), ([4,7,14], -12), ([4,8,8], -6), ([4,8,9], -16), ([4,8,10], -12), ([4,8,11], -8), ([4,8,12], -12), ([4,8,13], -8), ([4,8,14], -12), ([4,9,9], -10), ([4,9,10], -16), ([4,9,11], -12), ([4,9,12], -16), ([4,9,13], -8), ([4,9,14], -12), ([4,10,10], -6), ([4,10,11], -10), ([4,10,12], -14), ([4,10,13], -8), ([4,10,14], -8), ([4,11,11], -4), ([4,11,12], -8), ([4,11,13], -4), ([4,11,14], -4), ([4,12,12], -4), ([4,12,13], -4), ([4,12,14], -4), ([5,5,5], -2), ([5,5,6], -6), ([5,5,7], -6), ([5,5,8], -6), ([5,5,9], -8), ([5,5,10], -6), ([5,5,11], -4), ([5,5,12], -6), ([5,5,13], -4), ([5,5,14], -6), ([5,6,6], -6), ([5,6,7], -12), ([5,6,8], -12), ([5,6,9], -16), ([5,6,10], -12), ([5,6,11], -8), ([5,6,12], -12), ([5,6,13], -8), ([5,6,14], -12), ([5,7,7], -6), ([5,7,8], -12), ([5,7,9], -16), ([5,7,10], -12), ([5,7,11], -8), ([5,7,12], -12), ([5,7,13], -8), ([5,7,14], -12), ([5,8,8], -6), ([5,8,9], -16), ([5,8,10], -12), ([5,8,11], -8), ([5,8,12], -12), ([5,8,13], -8), ([5,8,14], -12), ([5,9,9], -10), ([5,9,10], -16), ([5,9,11], -12), ([5,9,12], -16), ([5,9,13], -8), ([5,9,14], -12), ([5,10,10], -6), ([5,10,11], -10), ([5,10,12], -14), ([5,10,13], -8), ([5,10,14], -8), ([5,11,11], -4), ([5,11,12], -8), ([5,11,13], -4), ([5,11,14], -4), ([5,12,12], -4), ([5,12,13], -4), ([5,12,14], -4), ([6,6,6], -2), ([6,6,7], -6), ([6,6,8], -6), ([6,6,9], -8), ([6,6,10], -6), ([6,6,11], -4), ([6,6,12], -6), ([6,6,13], -4), ([6,6,14], -6), ([6,7,7], -6), ([6,7,8], -12), ([6,7,9], -16), ([6,7,10], -12), ([6,7,11], -8), ([6,7,12], -12), ([6,7,13], -8), ([6,7,14], -12), ([6,8,8], -6), ([6,8,9], -16), ([6,8,10], -12), ([6,8,11], -8), ([6,8,12], -12), ([6,8,13], -8), ([6,8,14], -12), ([6,9,9], -10), ([6,9,10], -16), ([6,9,11], -12), ([6,9,12], -16), ([6,9,13], -8), ([6,9,14], -12), ([6,10,10], -6), ([6,10,11], -10), ([6,10,12], -14), ([6,10,13], -8), ([6,10,14], -8), ([6,11,11], -4), ([6,11,12], -8), ([6,11,13], -4), ([6,11,14], -4), ([6,12,12], -4), ([6,12,13], -4), ([6,12,14], -4), ([7,7,7], -2), ([7,7,8], -6), ([7,7,9], -8), ([7,7,10], -6), ([7,7,11], -4), ([7,7,12], -6), ([7,7,13], -4), ([7,7,14], -6), ([7,8,8], -6), ([7,8,9], -16), ([7,8,10], -12), ([7,8,11], -8), ([7,8,12], -12), ([7,8,13], -8), ([7,8,14], -12), ([7,9,9], -10), ([7,9,10], -16), ([7,9,11], -12), ([7,9,12], -16), ([7,9,13], -8), ([7,9,14], -12), ([7,10,10], -6), ([7,10,11], -10), ([7,10,12], -14), ([7,10,13], -8), ([7,10,14], -8), ([7,11,11], -4), ([7,11,12], -8), ([7,11,13], -4), ([7,11,14], -4), ([7,12,12], -4), ([7,12,13], -4), ([7,12,14], -4), ([8,8,8], -2), ([8,8,9], -8), ([8,8,10], -6), ([8,8,11], -4), ([8,8,12], -6), ([8,8,13], -4), ([8,8,14], -6), ([8,9,9], -10), ([8,9,10], -16), ([8,9,11], -12), ([8,9,12], -16), ([8,9,13], -8), ([8,9,14], -12), ([8,10,10], -6), ([8,10,11], -10), ([8,10,12], -14), ([8,10,13], -8), ([8,10,14], -8), ([8,11,11], -4), ([8,11,12], -8), ([8,11,13], -4), ([8,11,14], -4), ([8,12,12], -4), ([8,12,13], -4), ([8,12,14], -4), ([9,9,9], -4), ([9,9,10], -10), ([9,9,11], -8), ([9,9,12], -10), ([9,9,13], -4), ([9,9,14], -6), ([9,10,10], -8), ([9,10,11], -14), ([9,10,12], -18), ([9,10,13], -8), ([9,10,14], -8), ([9,11,11], -6), ([9,11,12], -12), ([9,11,13], -4), ([9,11,14], -4), ([9,12,12], -6), ([9,12,13], -4), ([9,12,14], 4), ([9,13,14], 8), ([9,14,14], 8), ([10,10,10], -2), ([10,10,11], -6), ([10,10,12], -8), ([10,10,13], -4), ([10,10,14], -4), ([10,11,11], -6), ([10,11,12], -12), ([10,11,13], -4), ([10,11,14], -4), ([10,12,12], -6), ([10,12,13], -4), ([10,12,14], 4), ([10,13,14], 8), ([10,14,14], 8), ([11,11,11], -2), ([11,11,12], -6), ([11,11,13], -2), ([11,11,14], -2), ([11,12,12], -6), ([11,12,13], -4), ([11,12,14], 4), ([11,13,14], 8), ([11,14,14], 8), ([12,12,12], -2), ([12,12,13], -2), ([12,12,14], 6), ([12,13,14], 16), ([12,14,14], 16), ([13,13,14], 8), ([13,14,14], 16), ([14,14,14], 8)]
theorem atom0000_data : atom0000 = SparsePolynomial.monoTimes [] 1 base00 := by decide +kernel
theorem eval_atom0000 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0000 = (detA (outer g)) := by
  rw [atom0000_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0000_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3621780 : Int) atom0000) := by
  rw [SparsePolynomial.eval_scale, eval_atom0000]
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (detA (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0000Coded : CoefficientMerge.Poly := [(9, -2), (10, -2), (11, -2), (12, -2), (13, -2), (14, -2), (17, -2), (18, -2), (19, -2), (20, -2), (21, -2), (22, -2), (23, -2), (24, -6), (25, -4), (26, -4), (27, -4), (28, -4), (29, -4), (32, -2), (33, -4), (34, -4), (35, -4), (36, -4), (37, -4), (38, -4), (39, -8), (40, -6), (41, -4), (42, -4), (43, -4), (44, -4), (48, -2), (49, -4), (50, -4), (51, -4), (52, -4), (53, -4), (54, -8), (55, -6), (56, -4), (57, -4), (58, -4), (59, -4), (64, -2), (65, -4), (66, -4), (67, -4), (68, -4), (69, -8), (70, -6), (71, -4), (72, -4), (73, -4), (74, -4), (80, -2), (81, -4), (82, -4), (83, -4), (84, -8), (85, -6), (86, -4), (87, -4), (88, -4), (89, -4), (96, -2), (97, -4), (98, -4), (99, -8), (100, -6), (101, -4), (102, -4), (103, -4), (104, -4), (112, -2), (113, -4), (114, -8), (115, -6), (116, -4), (117, -4), (118, -4), (119, -4), (128, -2), (129, -8), (130, -6), (131, -4), (132, -4), (133, -4), (134, -4), (144, -6), (145, -10), (146, -8), (147, -8), (148, -4), (149, -4), (160, -4), (161, -8), (162, -8), (163, -4), (164, -4), (176, -4), (177, -8), (178, -4), (179, -4), (192, -4), (193, -4), (194, -4), (242, -2), (243, -2), (244, -2), (245, -2), (246, -2), (247, -2), (248, -2), (249, -4), (250, -2), (251, -2), (252, -4), (253, -4), (254, -4), (257, -4), (258, -8), (259, -8), (260, -8), (261, -8), (262, -8), (263, -8), (264, -12), (265, -8), (266, -6), (267, -10), (268, -8), (269, -8), (273, -4), (274, -8), (275, -8), (276, -8), (277, -8), (278, -8), (279, -12), (280, -8), (281, -6), (282, -10), (283, -8), (284, -8), (289, -4), (290, -8), (291, -8), (292, -8), (293, -8), (294, -12), (295, -8), (296, -6), (297, -10), (298, -8), (299, -8), (305, -4), (306, -8), (307, -8), (308, -8), (309, -12), (310, -8), (311, -6), (312, -10), (313, -8), (314, -8), (321, -4), (322, -8), (323, -8), (324, -12), (325, -8), (326, -6), (327, -10), (328, -8), (329, -8), (337, -4), (338, -8), (339, -12), (340, -8), (341, -6), (342, -10), (343, -8), (344, -8), (353, -4), (354, -12), (355, -8), (356, -6), (357, -10), (358, -8), (359, -8), (369, -8), (370, -12), (371, -10), (372, -14), (373, -8), (374, -8), (385, -4), (386, -8), (387, -12), (388, -8), (389, -8), (401, -4), (402, -8), (403, -4), (404, -4), (417, -4), (418, -4), (419, -4), (482, -2), (483, -6), (484, -6), (485, -6), (486, -6), (487, -6), (488, -6), (489, -8), (490, -6), (491, -4), (492, -6), (493, -4), (494, -6), (498, -6), (499, -12), (500, -12), (501, -12), (502, -12), (503, -12), (504, -16), (505, -12), (506, -8), (507, -12), (508, -8), (509, -12), (514, -6), (515, -12), (516, -12), (517, -12), (518, -12), (519, -16), (520, -12), (521, -8), (522, -12), (523, -8), (524, -12), (530, -6), (531, -12), (532, -12), (533, -12), (534, -16), (535, -12), (536, -8), (537, -12), (538, -8), (539, -12), (546, -6), (547, -12), (548, -12), (549, -16), (550, -12), (551, -8), (552, -12), (553, -8), (554, -12), (562, -6), (563, -12), (564, -16), (565, -12), (566, -8), (567, -12), (568, -8), (569, -12), (578, -6), (579, -16), (580, -12), (581, -8), (582, -12), (583, -8), (584, -12), (594, -10), (595, -16), (596, -12), (597, -16), (598, -8), (599, -12), (610, -6), (611, -10), (612, -14), (613, -8), (614, -8), (626, -4), (627, -8), (628, -4), (629, -4), (642, -4), (643, -4), (644, -4), (723, -2), (724, -6), (725, -6), (726, -6), (727, -6), (728, -6), (729, -8), (730, -6), (731, -4), (732, -6), (733, -4), (734, -6), (739, -6), (740, -12), (741, -12), (742, -12), (743, -12), (744, -16), (745, -12), (746, -8), (747, -12), (748, -8), (749, -12), (755, -6), (756, -12), (757, -12), (758, -12), (759, -16), (760, -12), (761, -8), (762, -12), (763, -8), (764, -12), (771, -6), (772, -12), (773, -12), (774, -16), (775, -12), (776, -8), (777, -12), (778, -8), (779, -12), (787, -6), (788, -12), (789, -16), (790, -12), (791, -8), (792, -12), (793, -8), (794, -12), (803, -6), (804, -16), (805, -12), (806, -8), (807, -12), (808, -8), (809, -12), (819, -10), (820, -16), (821, -12), (822, -16), (823, -8), (824, -12), (835, -6), (836, -10), (837, -14), (838, -8), (839, -8), (851, -4), (852, -8), (853, -4), (854, -4), (867, -4), (868, -4), (869, -4), (964, -2), (965, -6), (966, -6), (967, -6), (968, -6), (969, -8), (970, -6), (971, -4), (972, -6), (973, -4), (974, -6), (980, -6), (981, -12), (982, -12), (983, -12), (984, -16), (985, -12), (986, -8), (987, -12), (988, -8), (989, -12), (996, -6), (997, -12), (998, -12), (999, -16), (1000, -12), (1001, -8), (1002, -12), (1003, -8), (1004, -12), (1012, -6), (1013, -12), (1014, -16), (1015, -12), (1016, -8), (1017, -12), (1018, -8), (1019, -12), (1028, -6), (1029, -16), (1030, -12), (1031, -8), (1032, -12), (1033, -8), (1034, -12), (1044, -10), (1045, -16), (1046, -12), (1047, -16), (1048, -8), (1049, -12), (1060, -6), (1061, -10), (1062, -14), (1063, -8), (1064, -8), (1076, -4), (1077, -8), (1078, -4), (1079, -4), (1092, -4), (1093, -4), (1094, -4), (1205, -2), (1206, -6), (1207, -6), (1208, -6), (1209, -8), (1210, -6), (1211, -4), (1212, -6), (1213, -4), (1214, -6), (1221, -6), (1222, -12), (1223, -12), (1224, -16), (1225, -12), (1226, -8), (1227, -12), (1228, -8), (1229, -12), (1237, -6), (1238, -12), (1239, -16), (1240, -12), (1241, -8), (1242, -12), (1243, -8), (1244, -12), (1253, -6), (1254, -16), (1255, -12), (1256, -8), (1257, -12), (1258, -8), (1259, -12), (1269, -10), (1270, -16), (1271, -12), (1272, -16), (1273, -8), (1274, -12), (1285, -6), (1286, -10), (1287, -14), (1288, -8), (1289, -8), (1301, -4), (1302, -8), (1303, -4), (1304, -4), (1317, -4), (1318, -4), (1319, -4), (1446, -2), (1447, -6), (1448, -6), (1449, -8), (1450, -6), (1451, -4), (1452, -6), (1453, -4), (1454, -6), (1462, -6), (1463, -12), (1464, -16), (1465, -12), (1466, -8), (1467, -12), (1468, -8), (1469, -12), (1478, -6), (1479, -16), (1480, -12), (1481, -8), (1482, -12), (1483, -8), (1484, -12), (1494, -10), (1495, -16), (1496, -12), (1497, -16), (1498, -8), (1499, -12), (1510, -6), (1511, -10), (1512, -14), (1513, -8), (1514, -8), (1526, -4), (1527, -8), (1528, -4), (1529, -4), (1542, -4), (1543, -4), (1544, -4), (1687, -2), (1688, -6), (1689, -8), (1690, -6), (1691, -4), (1692, -6), (1693, -4), (1694, -6), (1703, -6), (1704, -16), (1705, -12), (1706, -8), (1707, -12), (1708, -8), (1709, -12), (1719, -10), (1720, -16), (1721, -12), (1722, -16), (1723, -8), (1724, -12), (1735, -6), (1736, -10), (1737, -14), (1738, -8), (1739, -8), (1751, -4), (1752, -8), (1753, -4), (1754, -4), (1767, -4), (1768, -4), (1769, -4), (1928, -2), (1929, -8), (1930, -6), (1931, -4), (1932, -6), (1933, -4), (1934, -6), (1944, -10), (1945, -16), (1946, -12), (1947, -16), (1948, -8), (1949, -12), (1960, -6), (1961, -10), (1962, -14), (1963, -8), (1964, -8), (1976, -4), (1977, -8), (1978, -4), (1979, -4), (1992, -4), (1993, -4), (1994, -4), (2169, -4), (2170, -10), (2171, -8), (2172, -10), (2173, -4), (2174, -6), (2185, -8), (2186, -14), (2187, -18), (2188, -8), (2189, -8), (2201, -6), (2202, -12), (2203, -4), (2204, -4), (2217, -6), (2218, -4), (2219, 4), (2234, 8), (2249, 8), (2410, -2), (2411, -6), (2412, -8), (2413, -4), (2414, -4), (2426, -6), (2427, -12), (2428, -4), (2429, -4), (2442, -6), (2443, -4), (2444, 4), (2459, 8), (2474, 8), (2651, -2), (2652, -6), (2653, -2), (2654, -2), (2667, -6), (2668, -4), (2669, 4), (2684, 8), (2699, 8), (2892, -2), (2893, -2), (2894, 6), (2909, 16), (2924, 16), (3134, 8), (3149, 16), (3374, 8)]
theorem atom0000Coded_decode : atom0000 = SparsePolynomial.decodeCubic 15 atom0000Coded := by decide +kernel
theorem atom0000Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3621780 : Int) atom0000Coded) := by
  have h := atom0000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0001 : SparsePolynomial.Poly := [([0,5,6], -4), ([1,5,6], -8), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -8), ([5,6,11], 4), ([5,6,12], 12), ([5,6,13], 16), ([5,6,14], 18)]
theorem atom0001_data : atom0001 = SparsePolynomial.monoTimes [5,6] 1 base01 := by decide +kernel
theorem eval_atom0001 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0001 = (quadA (outer g) ![1,2,2] * g 5 * g 6) := by
  rw [atom0001_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0001_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96912 : Int) atom0001) := by
  rw [SparsePolynomial.eval_scale, eval_atom0001]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0001Coded : CoefficientMerge.Poly := [(81, -4), (306, -8), (531, -16), (756, -16), (981, -16), (1206, -16), (1221, -16), (1222, -16), (1223, -16), (1224, -8), (1226, 4), (1227, 12), (1228, 16), (1229, 18)]
theorem atom0001Coded_decode : atom0001 = SparsePolynomial.decodeCubic 15 atom0001Coded := by decide +kernel
theorem atom0001Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (96912 : Int) atom0001Coded) := by
  have h := atom0001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0002 : SparsePolynomial.Poly := [([0,1,8], -4), ([1,1,8], -12), ([1,2,8], -16), ([1,3,8], -16), ([1,4,8], -16), ([1,5,8], -16), ([1,6,8], -16), ([1,7,8], -16), ([1,8,8], -16), ([1,8,9], -8), ([1,8,10], -4), ([1,8,11], 4), ([1,8,12], 6), ([1,8,13], 10), ([1,8,14], 18)]
theorem atom0002_data : atom0002 = SparsePolynomial.monoTimes [1,8] 1 base02 := by decide +kernel
theorem eval_atom0002 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0002 = (quadA (outer g) ![2,1,2] * g 1 * g 8) := by
  rw [atom0002_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0002_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217440 : Int) atom0002) := by
  rw [SparsePolynomial.eval_scale, eval_atom0002]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0002Coded : CoefficientMerge.Poly := [(23, -4), (248, -12), (263, -16), (278, -16), (293, -16), (308, -16), (323, -16), (338, -16), (353, -16), (354, -8), (355, -4), (356, 4), (357, 6), (358, 10), (359, 18)]
theorem atom0002Coded_decode : atom0002 = SparsePolynomial.decodeCubic 15 atom0002Coded := by decide +kernel
theorem atom0002Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (217440 : Int) atom0002Coded) := by
  have h := atom0002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0003 : SparsePolynomial.Poly := [([0,1,10], -4), ([1,1,10], -12), ([1,2,10], -16), ([1,3,10], -16), ([1,4,10], -16), ([1,5,10], -16), ([1,6,10], -16), ([1,7,10], -16), ([1,8,10], -16), ([1,9,10], -8), ([1,10,10], -4), ([1,10,11], 4), ([1,10,12], 6), ([1,10,13], 10), ([1,10,14], 18)]
theorem atom0003_data : atom0003 = SparsePolynomial.monoTimes [1,10] 1 base02 := by decide +kernel
theorem eval_atom0003 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0003 = (quadA (outer g) ![2,1,2] * g 1 * g 10) := by
  rw [atom0003_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0003_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1078380 : Int) atom0003) := by
  rw [SparsePolynomial.eval_scale, eval_atom0003]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0003Coded : CoefficientMerge.Poly := [(25, -4), (250, -12), (265, -16), (280, -16), (295, -16), (310, -16), (325, -16), (340, -16), (355, -16), (370, -8), (385, -4), (386, 4), (387, 6), (388, 10), (389, 18)]
theorem atom0003Coded_decode : atom0003 = SparsePolynomial.decodeCubic 15 atom0003Coded := by decide +kernel
theorem atom0003Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1078380 : Int) atom0003Coded) := by
  have h := atom0003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0004 : SparsePolynomial.Poly := [([0,1,12], -4), ([1,1,12], -12), ([1,2,12], -16), ([1,3,12], -16), ([1,4,12], -16), ([1,5,12], -16), ([1,6,12], -16), ([1,7,12], -16), ([1,8,12], -16), ([1,9,12], -8), ([1,10,12], -4), ([1,11,12], 4), ([1,12,12], 6), ([1,12,13], 10), ([1,12,14], 18)]
theorem atom0004_data : atom0004 = SparsePolynomial.monoTimes [1,12] 1 base02 := by decide +kernel
theorem eval_atom0004 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0004 = (quadA (outer g) ![2,1,2] * g 1 * g 12) := by
  rw [atom0004_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0004_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97380 : Int) atom0004) := by
  rw [SparsePolynomial.eval_scale, eval_atom0004]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0004Coded : CoefficientMerge.Poly := [(27, -4), (252, -12), (267, -16), (282, -16), (297, -16), (312, -16), (327, -16), (342, -16), (357, -16), (372, -8), (387, -4), (402, 4), (417, 6), (418, 10), (419, 18)]
theorem atom0004Coded_decode : atom0004 = SparsePolynomial.decodeCubic 15 atom0004Coded := by decide +kernel
theorem atom0004Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (97380 : Int) atom0004Coded) := by
  have h := atom0004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0005 : SparsePolynomial.Poly := [([0,1,13], -4), ([1,1,13], -12), ([1,2,13], -16), ([1,3,13], -16), ([1,4,13], -16), ([1,5,13], -16), ([1,6,13], -16), ([1,7,13], -16), ([1,8,13], -16), ([1,9,13], -8), ([1,10,13], -4), ([1,11,13], 4), ([1,12,13], 6), ([1,13,13], 10), ([1,13,14], 18)]
theorem atom0005_data : atom0005 = SparsePolynomial.monoTimes [1,13] 1 base02 := by decide +kernel
theorem eval_atom0005 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0005 = (quadA (outer g) ![2,1,2] * g 1 * g 13) := by
  rw [atom0005_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0005_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (882900 : Int) atom0005) := by
  rw [SparsePolynomial.eval_scale, eval_atom0005]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0005Coded : CoefficientMerge.Poly := [(28, -4), (253, -12), (268, -16), (283, -16), (298, -16), (313, -16), (328, -16), (343, -16), (358, -16), (373, -8), (388, -4), (403, 4), (418, 6), (433, 10), (434, 18)]
theorem atom0005Coded_decode : atom0005 = SparsePolynomial.decodeCubic 15 atom0005Coded := by decide +kernel
theorem atom0005Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (882900 : Int) atom0005Coded) := by
  have h := atom0005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0006 : SparsePolynomial.Poly := [([0,1,14], -4), ([1,1,14], -12), ([1,2,14], -16), ([1,3,14], -16), ([1,4,14], -16), ([1,5,14], -16), ([1,6,14], -16), ([1,7,14], -16), ([1,8,14], -16), ([1,9,14], -8), ([1,10,14], -4), ([1,11,14], 4), ([1,12,14], 6), ([1,13,14], 10), ([1,14,14], 18)]
theorem atom0006_data : atom0006 = SparsePolynomial.monoTimes [1,14] 1 base02 := by decide +kernel
theorem eval_atom0006 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0006 = (quadA (outer g) ![2,1,2] * g 1 * g 14) := by
  rw [atom0006_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0006_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1376640 : Int) atom0006) := by
  rw [SparsePolynomial.eval_scale, eval_atom0006]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0006Coded : CoefficientMerge.Poly := [(29, -4), (254, -12), (269, -16), (284, -16), (299, -16), (314, -16), (329, -16), (344, -16), (359, -16), (374, -8), (389, -4), (404, 4), (419, 6), (434, 10), (449, 18)]
theorem atom0006Coded_decode : atom0006 = SparsePolynomial.decodeCubic 15 atom0006Coded := by decide +kernel
theorem atom0006Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1376640 : Int) atom0006Coded) := by
  have h := atom0006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0007 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -14), ([1,1,10], -10), ([1,1,11], -6), ([1,1,12], 2), ([1,1,13], 10), ([1,1,14], 18)]
theorem atom0007_data : atom0007 = SparsePolynomial.monoTimes [1,1] 1 base03 := by decide +kernel
theorem eval_atom0007 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0007 = (quadA (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0007_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0007_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (598590 : Int) atom0007) := by
  rw [SparsePolynomial.eval_scale, eval_atom0007]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0007Coded : CoefficientMerge.Poly := [(16, -8), (241, -12), (242, -16), (243, -16), (244, -16), (245, -16), (246, -16), (247, -16), (248, -16), (249, -14), (250, -10), (251, -6), (252, 2), (253, 10), (254, 18)]
theorem atom0007Coded_decode : atom0007 = SparsePolynomial.decodeCubic 15 atom0007Coded := by decide +kernel
theorem atom0007Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (598590 : Int) atom0007Coded) := by
  have h := atom0007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0008 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -14), ([5,5,10], -10), ([5,5,11], -6), ([5,5,12], 2), ([5,5,13], 10), ([5,5,14], 18)]
theorem atom0008_data : atom0008 = SparsePolynomial.monoTimes [5,5] 1 base03 := by decide +kernel
theorem eval_atom0008 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0008 = (quadA (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0008_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0008_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1274040 : Int) atom0008) := by
  rw [SparsePolynomial.eval_scale, eval_atom0008]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0008Coded : CoefficientMerge.Poly := [(80, -8), (305, -12), (530, -16), (755, -16), (980, -16), (1205, -16), (1206, -16), (1207, -16), (1208, -16), (1209, -14), (1210, -10), (1211, -6), (1212, 2), (1213, 10), (1214, 18)]
theorem atom0008Coded_decode : atom0008 = SparsePolynomial.decodeCubic 15 atom0008Coded := by decide +kernel
theorem atom0008Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1274040 : Int) atom0008Coded) := by
  have h := atom0008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0009 : SparsePolynomial.Poly := [([0,5,6], -8), ([1,5,6], -12), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -14), ([5,6,10], -10), ([5,6,11], -6), ([5,6,12], 2), ([5,6,13], 10), ([5,6,14], 18)]
theorem atom0009_data : atom0009 = SparsePolynomial.monoTimes [5,6] 1 base03 := by decide +kernel
theorem eval_atom0009 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0009 = (quadA (outer g) ![2,2,1] * g 5 * g 6) := by
  rw [atom0009_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0009_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369648 : Int) atom0009) := by
  rw [SparsePolynomial.eval_scale, eval_atom0009]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0009Coded : CoefficientMerge.Poly := [(81, -8), (306, -12), (531, -16), (756, -16), (981, -16), (1206, -16), (1221, -16), (1222, -16), (1223, -16), (1224, -14), (1225, -10), (1226, -6), (1227, 2), (1228, 10), (1229, 18)]
theorem atom0009Coded_decode : atom0009 = SparsePolynomial.decodeCubic 15 atom0009Coded := by decide +kernel
theorem atom0009Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (369648 : Int) atom0009Coded) := by
  have h := atom0009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0010 : SparsePolynomial.Poly := [([0,6,6], -8), ([1,6,6], -12), ([2,6,6], -16), ([3,6,6], -16), ([4,6,6], -16), ([5,6,6], -16), ([6,6,6], -16), ([6,6,7], -16), ([6,6,8], -16), ([6,6,9], -14), ([6,6,10], -10), ([6,6,11], -6), ([6,6,12], 2), ([6,6,13], 10), ([6,6,14], 18)]
theorem atom0010_data : atom0010 = SparsePolynomial.monoTimes [6,6] 1 base03 := by decide +kernel
theorem eval_atom0010 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0010 = (quadA (outer g) ![2,2,1] * g 6 * g 6) := by
  rw [atom0010_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0010_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1539000 : Int) atom0010) := by
  rw [SparsePolynomial.eval_scale, eval_atom0010]
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 6 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0010Coded : CoefficientMerge.Poly := [(96, -8), (321, -12), (546, -16), (771, -16), (996, -16), (1221, -16), (1446, -16), (1447, -16), (1448, -16), (1449, -14), (1450, -10), (1451, -6), (1452, 2), (1453, 10), (1454, 18)]
theorem atom0010Coded_decode : atom0010 = SparsePolynomial.decodeCubic 15 atom0010Coded := by decide +kernel
theorem atom0010Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1539000 : Int) atom0010Coded) := by
  have h := atom0010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0011 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -14), ([7,7,10], -10), ([7,7,11], -6), ([7,7,12], 2), ([7,7,13], 10), ([7,7,14], 18)]
theorem atom0011_data : atom0011 = SparsePolynomial.monoTimes [7,7] 1 base03 := by decide +kernel
theorem eval_atom0011 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0011 = (quadA (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0011_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0011_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (808500 : Int) atom0011) := by
  rw [SparsePolynomial.eval_scale, eval_atom0011]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0011Coded : CoefficientMerge.Poly := [(112, -8), (337, -12), (562, -16), (787, -16), (1012, -16), (1237, -16), (1462, -16), (1687, -16), (1688, -16), (1689, -14), (1690, -10), (1691, -6), (1692, 2), (1693, 10), (1694, 18)]
theorem atom0011Coded_decode : atom0011 = SparsePolynomial.decodeCubic 15 atom0011Coded := by decide +kernel
theorem atom0011Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (808500 : Int) atom0011Coded) := by
  have h := atom0011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0012 : SparsePolynomial.Poly := [([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,0,12], -2), ([0,0,13], -2), ([0,0,14], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -6), ([0,1,10], -4), ([0,1,11], -4), ([0,1,12], -4), ([0,1,13], -4), ([0,1,14], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,2,9], -8), ([0,2,10], -6), ([0,2,11], -6), ([0,2,12], -4), ([0,2,13], -4), ([0,2,14], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -4), ([0,3,7], -4), ([0,3,8], -4), ([0,3,9], -8), ([0,3,10], -6), ([0,3,11], -6), ([0,3,12], -4), ([0,3,13], -4), ([0,3,14], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -4), ([0,4,7], -4), ([0,4,8], -4), ([0,4,9], -8), ([0,4,10], -6), ([0,4,11], -6), ([0,4,12], -4), ([0,4,13], -4), ([0,4,14], -4), ([0,5,5], -2), ([0,5,6], -4), ([0,5,7], -4), ([0,5,8], -4), ([0,5,9], -8), ([0,5,10], -6), ([0,5,11], -6), ([0,5,12], -4), ([0,5,13], -4), ([0,5,14], -4), ([0,6,6], -2), ([0,6,7], -4), ([0,6,8], -4), ([0,6,9], -8), ([0,6,10], -6), ([0,6,11], -6), ([0,6,12], -4), ([0,6,13], -4), ([0,6,14], -4), ([0,7,7], -2), ([0,7,8], -4), ([0,7,9], -8), ([0,7,10], -6), ([0,7,11], -6), ([0,7,12], -4), ([0,7,13], -4), ([0,7,14], -4), ([0,8,8], -2), ([0,8,9], -8), ([0,8,10], -6), ([0,8,11], -6), ([0,8,12], -4), ([0,8,13], -4), ([0,8,14], -4), ([0,9,9], -6), ([0,9,10], -10), ([0,9,11], -10), ([0,9,12], -8), ([0,9,13], -4), ([0,9,14], -4), ([0,10,10], -4), ([0,10,11], -8), ([0,10,12], -8), ([0,10,13], -4), ([0,10,14], -4), ([0,11,11], -4), ([0,11,12], -8), ([0,11,13], -4), ([0,11,14], -4), ([0,12,12], -4), ([0,12,13], -4), ([0,12,14], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -2), ([1,1,7], -2), ([1,1,8], -2), ([1,1,9], -4), ([1,1,10], -2), ([1,1,11], -4), ([1,1,12], -4), ([1,1,13], -4), ([1,1,14], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -8), ([1,2,7], -8), ([1,2,8], -8), ([1,2,9], -12), ([1,2,10], -8), ([1,2,11], -12), ([1,2,12], -10), ([1,2,13], -8), ([1,2,14], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -8), ([1,3,7], -8), ([1,3,8], -8), ([1,3,9], -12), ([1,3,10], -8), ([1,3,11], -12), ([1,3,12], -10), ([1,3,13], -8), ([1,3,14], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -8), ([1,4,7], -8), ([1,4,8], -8), ([1,4,9], -12), ([1,4,10], -8), ([1,4,11], -12), ([1,4,12], -10), ([1,4,13], -8), ([1,4,14], -8), ([1,5,5], -4), ([1,5,6], -8), ([1,5,7], -8), ([1,5,8], -8), ([1,5,9], -12), ([1,5,10], -8), ([1,5,11], -12), ([1,5,12], -10), ([1,5,13], -8), ([1,5,14], -8), ([1,6,6], -4), ([1,6,7], -8), ([1,6,8], -8), ([1,6,9], -12), ([1,6,10], -8), ([1,6,11], -12), ([1,6,12], -10), ([1,6,13], -8), ([1,6,14], -8), ([1,7,7], -4), ([1,7,8], -8), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -12), ([1,7,12], -10), ([1,7,13], -8), ([1,7,14], -8), ([1,8,8], -4), ([1,8,9], -12), ([1,8,10], -8), ([1,8,11], -12), ([1,8,12], -10), ([1,8,13], -8), ([1,8,14], -8), ([1,9,9], -8), ([1,9,10], -12), ([1,9,11], -16), ([1,9,12], -14), ([1,9,13], -8), ([1,9,14], -8), ([1,10,10], -4), ([1,10,11], -12), ([1,10,12], -12), ([1,10,13], -8), ([1,10,14], -8), ([1,11,11], -8), ([1,11,12], -12), ([1,11,13], -8), ([1,11,14], -8), ([1,12,12], -4), ([1,12,13], -4), ([1,12,14], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -6), ([2,2,7], -6), ([2,2,8], -6), ([2,2,9], -8), ([2,2,10], -6), ([2,2,11], -8), ([2,2,12], -6), ([2,2,13], -4), ([2,2,14], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -12), ([2,3,7], -12), ([2,3,8], -12), ([2,3,9], -16), ([2,3,10], -12), ([2,3,11], -16), ([2,3,12], -12), ([2,3,13], -8), ([2,3,14], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -12), ([2,4,7], -12), ([2,4,8], -12), ([2,4,9], -16), ([2,4,10], -12), ([2,4,11], -16), ([2,4,12], -12), ([2,4,13], -8), ([2,4,14], -12), ([2,5,5], -6), ([2,5,6], -12), ([2,5,7], -12), ([2,5,8], -12), ([2,5,9], -16), ([2,5,10], -12), ([2,5,11], -16), ([2,5,12], -12), ([2,5,13], -8), ([2,5,14], -12), ([2,6,6], -6), ([2,6,7], -12), ([2,6,8], -12), ([2,6,9], -16), ([2,6,10], -12), ([2,6,11], -16), ([2,6,12], -12), ([2,6,13], -8), ([2,6,14], -12), ([2,7,7], -6), ([2,7,8], -12), ([2,7,9], -16), ([2,7,10], -12), ([2,7,11], -16), ([2,7,12], -12), ([2,7,13], -8), ([2,7,14], -12), ([2,8,8], -6), ([2,8,9], -16), ([2,8,10], -12), ([2,8,11], -16), ([2,8,12], -12), ([2,8,13], -8), ([2,8,14], -12), ([2,9,9], -10), ([2,9,10], -16), ([2,9,11], -20), ([2,9,12], -16), ([2,9,13], -8), ([2,9,14], -12), ([2,10,10], -6), ([2,10,11], -16), ([2,10,12], -14), ([2,10,13], -8), ([2,10,14], -8), ([2,11,11], -10), ([2,11,12], -14), ([2,11,13], -8), ([2,11,14], -8), ([2,12,12], -4), ([2,12,13], -4), ([2,12,14], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -6), ([3,3,7], -6), ([3,3,8], -6), ([3,3,9], -8), ([3,3,10], -6), ([3,3,11], -8), ([3,3,12], -6), ([3,3,13], -4), ([3,3,14], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -12), ([3,4,7], -12), ([3,4,8], -12), ([3,4,9], -16), ([3,4,10], -12), ([3,4,11], -16), ([3,4,12], -12), ([3,4,13], -8), ([3,4,14], -12), ([3,5,5], -6), ([3,5,6], -12), ([3,5,7], -12), ([3,5,8], -12), ([3,5,9], -16), ([3,5,10], -12), ([3,5,11], -16), ([3,5,12], -12), ([3,5,13], -8), ([3,5,14], -12), ([3,6,6], -6), ([3,6,7], -12), ([3,6,8], -12), ([3,6,9], -16), ([3,6,10], -12), ([3,6,11], -16), ([3,6,12], -12), ([3,6,13], -8), ([3,6,14], -12), ([3,7,7], -6), ([3,7,8], -12), ([3,7,9], -16), ([3,7,10], -12), ([3,7,11], -16), ([3,7,12], -12), ([3,7,13], -8), ([3,7,14], -12), ([3,8,8], -6), ([3,8,9], -16), ([3,8,10], -12), ([3,8,11], -16), ([3,8,12], -12), ([3,8,13], -8), ([3,8,14], -12), ([3,9,9], -10), ([3,9,10], -16), ([3,9,11], -20), ([3,9,12], -16), ([3,9,13], -8), ([3,9,14], -12), ([3,10,10], -6), ([3,10,11], -16), ([3,10,12], -14), ([3,10,13], -8), ([3,10,14], -8), ([3,11,11], -10), ([3,11,12], -14), ([3,11,13], -8), ([3,11,14], -8), ([3,12,12], -4), ([3,12,13], -4), ([3,12,14], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -6), ([4,4,7], -6), ([4,4,8], -6), ([4,4,9], -8), ([4,4,10], -6), ([4,4,11], -8), ([4,4,12], -6), ([4,4,13], -4), ([4,4,14], -6), ([4,5,5], -6), ([4,5,6], -12), ([4,5,7], -12), ([4,5,8], -12), ([4,5,9], -16), ([4,5,10], -12), ([4,5,11], -16), ([4,5,12], -12), ([4,5,13], -8), ([4,5,14], -12), ([4,6,6], -6), ([4,6,7], -12), ([4,6,8], -12), ([4,6,9], -16), ([4,6,10], -12), ([4,6,11], -16), ([4,6,12], -12), ([4,6,13], -8), ([4,6,14], -12), ([4,7,7], -6), ([4,7,8], -12), ([4,7,9], -16), ([4,7,10], -12), ([4,7,11], -16), ([4,7,12], -12), ([4,7,13], -8), ([4,7,14], -12), ([4,8,8], -6), ([4,8,9], -16), ([4,8,10], -12), ([4,8,11], -16), ([4,8,12], -12), ([4,8,13], -8), ([4,8,14], -12), ([4,9,9], -10), ([4,9,10], -16), ([4,9,11], -20), ([4,9,12], -16), ([4,9,13], -8), ([4,9,14], -12), ([4,10,10], -6), ([4,10,11], -16), ([4,10,12], -14), ([4,10,13], -8), ([4,10,14], -8), ([4,11,11], -10), ([4,11,12], -14), ([4,11,13], -8), ([4,11,14], -8), ([4,12,12], -4), ([4,12,13], -4), ([4,12,14], -4), ([5,5,5], -2), ([5,5,6], -6), ([5,5,7], -6), ([5,5,8], -6), ([5,5,9], -8), ([5,5,10], -6), ([5,5,11], -8), ([5,5,12], -6), ([5,5,13], -4), ([5,5,14], -6), ([5,6,6], -6), ([5,6,7], -12), ([5,6,8], -12), ([5,6,9], -16), ([5,6,10], -12), ([5,6,11], -16), ([5,6,12], -12), ([5,6,13], -8), ([5,6,14], -12), ([5,7,7], -6), ([5,7,8], -12), ([5,7,9], -16), ([5,7,10], -12), ([5,7,11], -16), ([5,7,12], -12), ([5,7,13], -8), ([5,7,14], -12), ([5,8,8], -6), ([5,8,9], -16), ([5,8,10], -12), ([5,8,11], -16), ([5,8,12], -12), ([5,8,13], -8), ([5,8,14], -12), ([5,9,9], -10), ([5,9,10], -16), ([5,9,11], -20), ([5,9,12], -16), ([5,9,13], -8), ([5,9,14], -12), ([5,10,10], -6), ([5,10,11], -16), ([5,10,12], -14), ([5,10,13], -8), ([5,10,14], -8), ([5,11,11], -10), ([5,11,12], -14), ([5,11,13], -8), ([5,11,14], -8), ([5,12,12], -4), ([5,12,13], -4), ([5,12,14], -4), ([6,6,6], -2), ([6,6,7], -6), ([6,6,8], -6), ([6,6,9], -8), ([6,6,10], -6), ([6,6,11], -8), ([6,6,12], -6), ([6,6,13], -4), ([6,6,14], -6), ([6,7,7], -6), ([6,7,8], -12), ([6,7,9], -16), ([6,7,10], -12), ([6,7,11], -16), ([6,7,12], -12), ([6,7,13], -8), ([6,7,14], -12), ([6,8,8], -6), ([6,8,9], -16), ([6,8,10], -12), ([6,8,11], -16), ([6,8,12], -12), ([6,8,13], -8), ([6,8,14], -12), ([6,9,9], -10), ([6,9,10], -16), ([6,9,11], -20), ([6,9,12], -16), ([6,9,13], -8), ([6,9,14], -12), ([6,10,10], -6), ([6,10,11], -16), ([6,10,12], -14), ([6,10,13], -8), ([6,10,14], -8), ([6,11,11], -10), ([6,11,12], -14), ([6,11,13], -8), ([6,11,14], -8), ([6,12,12], -4), ([6,12,13], -4), ([6,12,14], -4), ([7,7,7], -2), ([7,7,8], -6), ([7,7,9], -8), ([7,7,10], -6), ([7,7,11], -8), ([7,7,12], -6), ([7,7,13], -4), ([7,7,14], -6), ([7,8,8], -6), ([7,8,9], -16), ([7,8,10], -12), ([7,8,11], -16), ([7,8,12], -12), ([7,8,13], -8), ([7,8,14], -12), ([7,9,9], -10), ([7,9,10], -16), ([7,9,11], -20), ([7,9,12], -16), ([7,9,13], -8), ([7,9,14], -12), ([7,10,10], -6), ([7,10,11], -16), ([7,10,12], -14), ([7,10,13], -8), ([7,10,14], -8), ([7,11,11], -10), ([7,11,12], -14), ([7,11,13], -8), ([7,11,14], -8), ([7,12,12], -4), ([7,12,13], -4), ([7,12,14], -4), ([8,8,8], -2), ([8,8,9], -8), ([8,8,10], -6), ([8,8,11], -8), ([8,8,12], -6), ([8,8,13], -4), ([8,8,14], -6), ([8,9,9], -10), ([8,9,10], -16), ([8,9,11], -20), ([8,9,12], -16), ([8,9,13], -8), ([8,9,14], -12), ([8,10,10], -6), ([8,10,11], -16), ([8,10,12], -14), ([8,10,13], -8), ([8,10,14], -8), ([8,11,11], -10), ([8,11,12], -14), ([8,11,13], -8), ([8,11,14], -8), ([8,12,12], -4), ([8,12,13], -4), ([8,12,14], -4), ([9,9,9], -4), ([9,9,10], -10), ([9,9,11], -12), ([9,9,12], -10), ([9,9,13], -4), ([9,9,14], -6), ([9,10,10], -8), ([9,10,11], -20), ([9,10,12], -18), ([9,10,13], -8), ([9,10,14], -8), ([9,11,11], -12), ([9,11,12], -18), ([9,11,13], -8), ([9,12,12], -6), ([9,12,13], -4), ([9,12,14], 4), ([9,13,14], 8), ([9,14,14], 8), ([10,10,10], -2), ([10,10,11], -8), ([10,10,12], -8), ([10,10,13], -4), ([10,10,14], -4), ([10,11,11], -10), ([10,11,12], -16), ([10,11,13], -8), ([10,12,12], -6), ([10,12,13], -4), ([10,12,14], 4), ([10,13,14], 8), ([10,14,14], 8), ([11,11,11], -4), ([11,11,12], -8), ([11,11,13], -4), ([11,11,14], 4), ([11,12,12], -6), ([11,12,13], -4), ([11,12,14], 12), ([11,13,14], 16), ([11,14,14], 16), ([12,12,12], -2), ([12,12,13], -2), ([12,12,14], 6), ([12,13,14], 16), ([12,14,14], 16), ([13,13,14], 8), ([13,14,14], 16), ([14,14,14], 8)]
theorem atom0012_data : atom0012 = SparsePolynomial.monoTimes [] 1 base04 := by decide +kernel
theorem eval_atom0012 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0012 = (detB (outer g)) := by
  rw [atom0012_data, SparsePolynomial.eval_monoTimes, eval_base04]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0012_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9986220 : Int) atom0012) := by
  rw [SparsePolynomial.eval_scale, eval_atom0012]
  have hb := base04_nonneg g hg hA hB
  rw [eval_base04] at hb
  have ht : 0 ≤ (detB (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0012Coded : CoefficientMerge.Poly := [(9, -2), (10, -2), (11, -2), (12, -2), (13, -2), (14, -2), (17, -2), (18, -2), (19, -2), (20, -2), (21, -2), (22, -2), (23, -2), (24, -6), (25, -4), (26, -4), (27, -4), (28, -4), (29, -4), (32, -2), (33, -4), (34, -4), (35, -4), (36, -4), (37, -4), (38, -4), (39, -8), (40, -6), (41, -6), (42, -4), (43, -4), (44, -4), (48, -2), (49, -4), (50, -4), (51, -4), (52, -4), (53, -4), (54, -8), (55, -6), (56, -6), (57, -4), (58, -4), (59, -4), (64, -2), (65, -4), (66, -4), (67, -4), (68, -4), (69, -8), (70, -6), (71, -6), (72, -4), (73, -4), (74, -4), (80, -2), (81, -4), (82, -4), (83, -4), (84, -8), (85, -6), (86, -6), (87, -4), (88, -4), (89, -4), (96, -2), (97, -4), (98, -4), (99, -8), (100, -6), (101, -6), (102, -4), (103, -4), (104, -4), (112, -2), (113, -4), (114, -8), (115, -6), (116, -6), (117, -4), (118, -4), (119, -4), (128, -2), (129, -8), (130, -6), (131, -6), (132, -4), (133, -4), (134, -4), (144, -6), (145, -10), (146, -10), (147, -8), (148, -4), (149, -4), (160, -4), (161, -8), (162, -8), (163, -4), (164, -4), (176, -4), (177, -8), (178, -4), (179, -4), (192, -4), (193, -4), (194, -4), (242, -2), (243, -2), (244, -2), (245, -2), (246, -2), (247, -2), (248, -2), (249, -4), (250, -2), (251, -4), (252, -4), (253, -4), (254, -4), (257, -4), (258, -8), (259, -8), (260, -8), (261, -8), (262, -8), (263, -8), (264, -12), (265, -8), (266, -12), (267, -10), (268, -8), (269, -8), (273, -4), (274, -8), (275, -8), (276, -8), (277, -8), (278, -8), (279, -12), (280, -8), (281, -12), (282, -10), (283, -8), (284, -8), (289, -4), (290, -8), (291, -8), (292, -8), (293, -8), (294, -12), (295, -8), (296, -12), (297, -10), (298, -8), (299, -8), (305, -4), (306, -8), (307, -8), (308, -8), (309, -12), (310, -8), (311, -12), (312, -10), (313, -8), (314, -8), (321, -4), (322, -8), (323, -8), (324, -12), (325, -8), (326, -12), (327, -10), (328, -8), (329, -8), (337, -4), (338, -8), (339, -12), (340, -8), (341, -12), (342, -10), (343, -8), (344, -8), (353, -4), (354, -12), (355, -8), (356, -12), (357, -10), (358, -8), (359, -8), (369, -8), (370, -12), (371, -16), (372, -14), (373, -8), (374, -8), (385, -4), (386, -12), (387, -12), (388, -8), (389, -8), (401, -8), (402, -12), (403, -8), (404, -8), (417, -4), (418, -4), (419, -4), (482, -2), (483, -6), (484, -6), (485, -6), (486, -6), (487, -6), (488, -6), (489, -8), (490, -6), (491, -8), (492, -6), (493, -4), (494, -6), (498, -6), (499, -12), (500, -12), (501, -12), (502, -12), (503, -12), (504, -16), (505, -12), (506, -16), (507, -12), (508, -8), (509, -12), (514, -6), (515, -12), (516, -12), (517, -12), (518, -12), (519, -16), (520, -12), (521, -16), (522, -12), (523, -8), (524, -12), (530, -6), (531, -12), (532, -12), (533, -12), (534, -16), (535, -12), (536, -16), (537, -12), (538, -8), (539, -12), (546, -6), (547, -12), (548, -12), (549, -16), (550, -12), (551, -16), (552, -12), (553, -8), (554, -12), (562, -6), (563, -12), (564, -16), (565, -12), (566, -16), (567, -12), (568, -8), (569, -12), (578, -6), (579, -16), (580, -12), (581, -16), (582, -12), (583, -8), (584, -12), (594, -10), (595, -16), (596, -20), (597, -16), (598, -8), (599, -12), (610, -6), (611, -16), (612, -14), (613, -8), (614, -8), (626, -10), (627, -14), (628, -8), (629, -8), (642, -4), (643, -4), (644, -4), (723, -2), (724, -6), (725, -6), (726, -6), (727, -6), (728, -6), (729, -8), (730, -6), (731, -8), (732, -6), (733, -4), (734, -6), (739, -6), (740, -12), (741, -12), (742, -12), (743, -12), (744, -16), (745, -12), (746, -16), (747, -12), (748, -8), (749, -12), (755, -6), (756, -12), (757, -12), (758, -12), (759, -16), (760, -12), (761, -16), (762, -12), (763, -8), (764, -12), (771, -6), (772, -12), (773, -12), (774, -16), (775, -12), (776, -16), (777, -12), (778, -8), (779, -12), (787, -6), (788, -12), (789, -16), (790, -12), (791, -16), (792, -12), (793, -8), (794, -12), (803, -6), (804, -16), (805, -12), (806, -16), (807, -12), (808, -8), (809, -12), (819, -10), (820, -16), (821, -20), (822, -16), (823, -8), (824, -12), (835, -6), (836, -16), (837, -14), (838, -8), (839, -8), (851, -10), (852, -14), (853, -8), (854, -8), (867, -4), (868, -4), (869, -4), (964, -2), (965, -6), (966, -6), (967, -6), (968, -6), (969, -8), (970, -6), (971, -8), (972, -6), (973, -4), (974, -6), (980, -6), (981, -12), (982, -12), (983, -12), (984, -16), (985, -12), (986, -16), (987, -12), (988, -8), (989, -12), (996, -6), (997, -12), (998, -12), (999, -16), (1000, -12), (1001, -16), (1002, -12), (1003, -8), (1004, -12), (1012, -6), (1013, -12), (1014, -16), (1015, -12), (1016, -16), (1017, -12), (1018, -8), (1019, -12), (1028, -6), (1029, -16), (1030, -12), (1031, -16), (1032, -12), (1033, -8), (1034, -12), (1044, -10), (1045, -16), (1046, -20), (1047, -16), (1048, -8), (1049, -12), (1060, -6), (1061, -16), (1062, -14), (1063, -8), (1064, -8), (1076, -10), (1077, -14), (1078, -8), (1079, -8), (1092, -4), (1093, -4), (1094, -4), (1205, -2), (1206, -6), (1207, -6), (1208, -6), (1209, -8), (1210, -6), (1211, -8), (1212, -6), (1213, -4), (1214, -6), (1221, -6), (1222, -12), (1223, -12), (1224, -16), (1225, -12), (1226, -16), (1227, -12), (1228, -8), (1229, -12), (1237, -6), (1238, -12), (1239, -16), (1240, -12), (1241, -16), (1242, -12), (1243, -8), (1244, -12), (1253, -6), (1254, -16), (1255, -12), (1256, -16), (1257, -12), (1258, -8), (1259, -12), (1269, -10), (1270, -16), (1271, -20), (1272, -16), (1273, -8), (1274, -12), (1285, -6), (1286, -16), (1287, -14), (1288, -8), (1289, -8), (1301, -10), (1302, -14), (1303, -8), (1304, -8), (1317, -4), (1318, -4), (1319, -4), (1446, -2), (1447, -6), (1448, -6), (1449, -8), (1450, -6), (1451, -8), (1452, -6), (1453, -4), (1454, -6), (1462, -6), (1463, -12), (1464, -16), (1465, -12), (1466, -16), (1467, -12), (1468, -8), (1469, -12), (1478, -6), (1479, -16), (1480, -12), (1481, -16), (1482, -12), (1483, -8), (1484, -12), (1494, -10), (1495, -16), (1496, -20), (1497, -16), (1498, -8), (1499, -12), (1510, -6), (1511, -16), (1512, -14), (1513, -8), (1514, -8), (1526, -10), (1527, -14), (1528, -8), (1529, -8), (1542, -4), (1543, -4), (1544, -4), (1687, -2), (1688, -6), (1689, -8), (1690, -6), (1691, -8), (1692, -6), (1693, -4), (1694, -6), (1703, -6), (1704, -16), (1705, -12), (1706, -16), (1707, -12), (1708, -8), (1709, -12), (1719, -10), (1720, -16), (1721, -20), (1722, -16), (1723, -8), (1724, -12), (1735, -6), (1736, -16), (1737, -14), (1738, -8), (1739, -8), (1751, -10), (1752, -14), (1753, -8), (1754, -8), (1767, -4), (1768, -4), (1769, -4), (1928, -2), (1929, -8), (1930, -6), (1931, -8), (1932, -6), (1933, -4), (1934, -6), (1944, -10), (1945, -16), (1946, -20), (1947, -16), (1948, -8), (1949, -12), (1960, -6), (1961, -16), (1962, -14), (1963, -8), (1964, -8), (1976, -10), (1977, -14), (1978, -8), (1979, -8), (1992, -4), (1993, -4), (1994, -4), (2169, -4), (2170, -10), (2171, -12), (2172, -10), (2173, -4), (2174, -6), (2185, -8), (2186, -20), (2187, -18), (2188, -8), (2189, -8), (2201, -12), (2202, -18), (2203, -8), (2217, -6), (2218, -4), (2219, 4), (2234, 8), (2249, 8), (2410, -2), (2411, -8), (2412, -8), (2413, -4), (2414, -4), (2426, -10), (2427, -16), (2428, -8), (2442, -6), (2443, -4), (2444, 4), (2459, 8), (2474, 8), (2651, -4), (2652, -8), (2653, -4), (2654, 4), (2667, -6), (2668, -4), (2669, 12), (2684, 16), (2699, 16), (2892, -2), (2893, -2), (2894, 6), (2909, 16), (2924, 16), (3134, 8), (3149, 16), (3374, 8)]
theorem atom0012Coded_decode : atom0012 = SparsePolynomial.decodeCubic 15 atom0012Coded := by decide +kernel
theorem atom0012Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (9986220 : Int) atom0012Coded) := by
  have h := atom0012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0013 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,0,12], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -2), ([0,1,10], -2), ([0,1,11], -2), ([0,1,12], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,2,7], -2), ([0,2,8], -2), ([0,2,9], -2), ([0,2,10], -2), ([0,2,11], -2), ([0,2,12], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,3,7], -2), ([0,3,8], -2), ([0,3,9], -2), ([0,3,10], -2), ([0,3,11], -2), ([0,3,12], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,4,7], -2), ([0,4,8], -2), ([0,4,9], -2), ([0,4,10], -2), ([0,4,11], -2), ([0,4,12], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,7], -2), ([0,5,8], -2), ([0,5,9], -2), ([0,5,10], -2), ([0,5,11], -2), ([0,5,12], -2), ([0,6,6], -1), ([0,6,7], -2), ([0,6,8], -2), ([0,6,9], -2), ([0,6,10], -2), ([0,6,11], -2), ([0,6,12], -2), ([0,7,7], -1), ([0,7,8], -2), ([0,7,9], -2), ([0,7,10], -2), ([0,7,11], -2), ([0,7,12], -2), ([0,8,8], -1), ([0,8,9], -2), ([0,8,10], -2), ([0,8,11], -2), ([0,8,12], -2), ([0,9,9], -1), ([0,9,10], -2), ([0,9,11], -2), ([0,9,12], -2), ([0,10,10], -1), ([0,10,11], -2), ([0,10,12], -2), ([0,11,11], -1), ([0,11,12], -2), ([0,11,14], 4), ([0,12,12], -1), ([0,12,14], 4), ([0,13,14], 4), ([0,14,14], 4)]
theorem atom0013_data : atom0013 = SparsePolynomial.monoTimes [0] 1 base05 := by decide +kernel
theorem eval_atom0013 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0013 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0013_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0013_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2298240 : Int) atom0013) := by
  rw [SparsePolynomial.eval_scale, eval_atom0013]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0013Coded : CoefficientMerge.Poly := [(0, -1), (1, -2), (2, -2), (3, -2), (4, -2), (5, -2), (6, -2), (7, -2), (8, -2), (9, -2), (10, -2), (11, -2), (12, -2), (16, -1), (17, -2), (18, -2), (19, -2), (20, -2), (21, -2), (22, -2), (23, -2), (24, -2), (25, -2), (26, -2), (27, -2), (32, -1), (33, -2), (34, -2), (35, -2), (36, -2), (37, -2), (38, -2), (39, -2), (40, -2), (41, -2), (42, -2), (48, -1), (49, -2), (50, -2), (51, -2), (52, -2), (53, -2), (54, -2), (55, -2), (56, -2), (57, -2), (64, -1), (65, -2), (66, -2), (67, -2), (68, -2), (69, -2), (70, -2), (71, -2), (72, -2), (80, -1), (81, -2), (82, -2), (83, -2), (84, -2), (85, -2), (86, -2), (87, -2), (96, -1), (97, -2), (98, -2), (99, -2), (100, -2), (101, -2), (102, -2), (112, -1), (113, -2), (114, -2), (115, -2), (116, -2), (117, -2), (128, -1), (129, -2), (130, -2), (131, -2), (132, -2), (144, -1), (145, -2), (146, -2), (147, -2), (160, -1), (161, -2), (162, -2), (176, -1), (177, -2), (179, 4), (192, -1), (194, 4), (209, 4), (224, 4)]
theorem atom0013Coded_decode : atom0013 = SparsePolynomial.decodeCubic 15 atom0013Coded := by decide +kernel
theorem atom0013Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2298240 : Int) atom0013Coded) := by
  have h := atom0013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0014 : SparsePolynomial.Poly := [([0,0,14], -2), ([0,1,14], -2), ([0,2,14], -2), ([0,3,14], -2), ([0,4,14], -2), ([0,5,14], -2), ([0,6,14], -2), ([0,7,14], -2), ([0,8,14], -2), ([0,9,14], -2), ([0,10,14], -2), ([0,13,14], 2), ([0,14,14], 4)]
theorem atom0014_data : atom0014 = SparsePolynomial.monoTimes [0,14] 1 base06 := by decide +kernel
theorem eval_atom0014 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0014 = (quadB (outer g) ![1,1,0] * g 0 * g 14) := by
  rw [atom0014_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0014_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3144960 : Int) atom0014) := by
  rw [SparsePolynomial.eval_scale, eval_atom0014]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0014Coded : CoefficientMerge.Poly := [(14, -2), (29, -2), (44, -2), (59, -2), (74, -2), (89, -2), (104, -2), (119, -2), (134, -2), (149, -2), (164, -2), (209, 2), (224, 4)]
theorem atom0014Coded_decode : atom0014 = SparsePolynomial.decodeCubic 15 atom0014Coded := by decide +kernel
theorem atom0014Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3144960 : Int) atom0014Coded) := by
  have h := atom0014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0015 : SparsePolynomial.Poly := [([0,2,13], -4), ([1,2,13], -8), ([2,2,13], -16), ([2,3,13], -16), ([2,4,13], -16), ([2,5,13], -16), ([2,6,13], -16), ([2,7,13], -16), ([2,8,13], -16), ([2,9,13], -8), ([2,11,13], 8), ([2,12,13], 12), ([2,13,13], 16), ([2,13,14], 18)]
theorem atom0015_data : atom0015 = SparsePolynomial.monoTimes [2,13] 1 base07 := by decide +kernel
theorem eval_atom0015 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0015 = (quadB (outer g) ![1,2,2] * g 2 * g 13) := by
  rw [atom0015_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0015_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1266840 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0015Coded : CoefficientMerge.Poly := [(43, -4), (268, -8), (493, -16), (508, -16), (523, -16), (538, -16), (553, -16), (568, -16), (583, -16), (598, -8), (628, 8), (643, 12), (658, 16), (659, 18)]
theorem atom0015Coded_decode : atom0015 = SparsePolynomial.decodeCubic 15 atom0015Coded := by decide +kernel
theorem atom0015Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1266840 : Int) atom0015Coded) := by
  have h := atom0015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0016 : SparsePolynomial.Poly := [([0,3,7], -4), ([1,3,7], -8), ([2,3,7], -16), ([3,3,7], -16), ([3,4,7], -16), ([3,5,7], -16), ([3,6,7], -16), ([3,7,7], -16), ([3,7,8], -16), ([3,7,9], -8), ([3,7,11], 8), ([3,7,12], 12), ([3,7,13], 16), ([3,7,14], 18)]
theorem atom0016_data : atom0016 = SparsePolynomial.monoTimes [3,7] 1 base07 := by decide +kernel
theorem eval_atom0016 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0016 = (quadB (outer g) ![1,2,2] * g 3 * g 7) := by
  rw [atom0016_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0016_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28080 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016Coded : CoefficientMerge.Poly := [(52, -4), (277, -8), (502, -16), (727, -16), (742, -16), (757, -16), (772, -16), (787, -16), (788, -16), (789, -8), (791, 8), (792, 12), (793, 16), (794, 18)]
theorem atom0016Coded_decode : atom0016 = SparsePolynomial.decodeCubic 15 atom0016Coded := by decide +kernel
theorem atom0016Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (28080 : Int) atom0016Coded) := by
  have h := atom0016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0017 : SparsePolynomial.Poly := [([0,3,8], -4), ([1,3,8], -8), ([2,3,8], -16), ([3,3,8], -16), ([3,4,8], -16), ([3,5,8], -16), ([3,6,8], -16), ([3,7,8], -16), ([3,8,8], -16), ([3,8,9], -8), ([3,8,11], 8), ([3,8,12], 12), ([3,8,13], 16), ([3,8,14], 18)]
theorem atom0017_data : atom0017 = SparsePolynomial.monoTimes [3,8] 1 base07 := by decide +kernel
theorem eval_atom0017 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0017 = (quadB (outer g) ![1,2,2] * g 3 * g 8) := by
  rw [atom0017_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0017_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56160 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017Coded : CoefficientMerge.Poly := [(53, -4), (278, -8), (503, -16), (728, -16), (743, -16), (758, -16), (773, -16), (788, -16), (803, -16), (804, -8), (806, 8), (807, 12), (808, 16), (809, 18)]
theorem atom0017Coded_decode : atom0017 = SparsePolynomial.decodeCubic 15 atom0017Coded := by decide +kernel
theorem atom0017Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (56160 : Int) atom0017Coded) := by
  have h := atom0017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0018 : SparsePolynomial.Poly := [([0,3,10], -4), ([1,3,10], -8), ([2,3,10], -16), ([3,3,10], -16), ([3,4,10], -16), ([3,5,10], -16), ([3,6,10], -16), ([3,7,10], -16), ([3,8,10], -16), ([3,9,10], -8), ([3,10,11], 8), ([3,10,12], 12), ([3,10,13], 16), ([3,10,14], 18)]
theorem atom0018_data : atom0018 = SparsePolynomial.monoTimes [3,10] 1 base07 := by decide +kernel
theorem eval_atom0018 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = (quadB (outer g) ![1,2,2] * g 3 * g 10) := by
  rw [atom0018_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145125 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018Coded : CoefficientMerge.Poly := [(55, -4), (280, -8), (505, -16), (730, -16), (745, -16), (760, -16), (775, -16), (790, -16), (805, -16), (820, -8), (836, 8), (837, 12), (838, 16), (839, 18)]
theorem atom0018Coded_decode : atom0018 = SparsePolynomial.decodeCubic 15 atom0018Coded := by decide +kernel
theorem atom0018Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (145125 : Int) atom0018Coded) := by
  have h := atom0018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0019 : SparsePolynomial.Poly := [([0,3,12], -4), ([1,3,12], -8), ([2,3,12], -16), ([3,3,12], -16), ([3,4,12], -16), ([3,5,12], -16), ([3,6,12], -16), ([3,7,12], -16), ([3,8,12], -16), ([3,9,12], -8), ([3,11,12], 8), ([3,12,12], 12), ([3,12,13], 16), ([3,12,14], 18)]
theorem atom0019_data : atom0019 = SparsePolynomial.monoTimes [3,12] 1 base07 := by decide +kernel
theorem eval_atom0019 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0019 = (quadB (outer g) ![1,2,2] * g 3 * g 12) := by
  rw [atom0019_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0019_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266895 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019Coded : CoefficientMerge.Poly := [(57, -4), (282, -8), (507, -16), (732, -16), (747, -16), (762, -16), (777, -16), (792, -16), (807, -16), (822, -8), (852, 8), (867, 12), (868, 16), (869, 18)]
theorem atom0019Coded_decode : atom0019 = SparsePolynomial.decodeCubic 15 atom0019Coded := by decide +kernel
theorem atom0019Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (266895 : Int) atom0019Coded) := by
  have h := atom0019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0020 : SparsePolynomial.Poly := [([0,3,13], -4), ([1,3,13], -8), ([2,3,13], -16), ([3,3,13], -16), ([3,4,13], -16), ([3,5,13], -16), ([3,6,13], -16), ([3,7,13], -16), ([3,8,13], -16), ([3,9,13], -8), ([3,11,13], 8), ([3,12,13], 12), ([3,13,13], 16), ([3,13,14], 18)]
theorem atom0020_data : atom0020 = SparsePolynomial.monoTimes [3,13] 1 base07 := by decide +kernel
theorem eval_atom0020 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0020 = (quadB (outer g) ![1,2,2] * g 3 * g 13) := by
  rw [atom0020_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0020_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2039715 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020Coded : CoefficientMerge.Poly := [(58, -4), (283, -8), (508, -16), (733, -16), (748, -16), (763, -16), (778, -16), (793, -16), (808, -16), (823, -8), (853, 8), (868, 12), (883, 16), (884, 18)]
theorem atom0020Coded_decode : atom0020 = SparsePolynomial.decodeCubic 15 atom0020Coded := by decide +kernel
theorem atom0020Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2039715 : Int) atom0020Coded) := by
  have h := atom0020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0021 : SparsePolynomial.Poly := [([0,3,14], -4), ([1,3,14], -8), ([2,3,14], -16), ([3,3,14], -16), ([3,4,14], -16), ([3,5,14], -16), ([3,6,14], -16), ([3,7,14], -16), ([3,8,14], -16), ([3,9,14], -8), ([3,11,14], 8), ([3,12,14], 12), ([3,13,14], 16), ([3,14,14], 18)]
theorem atom0021_data : atom0021 = SparsePolynomial.monoTimes [3,14] 1 base07 := by decide +kernel
theorem eval_atom0021 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0021 = (quadB (outer g) ![1,2,2] * g 3 * g 14) := by
  rw [atom0021_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0021_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410535 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021Coded : CoefficientMerge.Poly := [(59, -4), (284, -8), (509, -16), (734, -16), (749, -16), (764, -16), (779, -16), (794, -16), (809, -16), (824, -8), (854, 8), (869, 12), (884, 16), (899, 18)]
theorem atom0021Coded_decode : atom0021 = SparsePolynomial.decodeCubic 15 atom0021Coded := by decide +kernel
theorem atom0021Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (410535 : Int) atom0021Coded) := by
  have h := atom0021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0022 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -8), ([4,5,11], 8), ([4,5,12], 12), ([4,5,13], 16), ([4,5,14], 18)]
theorem atom0022_data : atom0022 = SparsePolynomial.monoTimes [4,5] 1 base07 := by decide +kernel
theorem eval_atom0022 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0022 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0022_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0022_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (961560 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022Coded : CoefficientMerge.Poly := [(65, -4), (290, -8), (515, -16), (740, -16), (965, -16), (980, -16), (981, -16), (982, -16), (983, -16), (984, -8), (986, 8), (987, 12), (988, 16), (989, 18)]
theorem atom0022Coded_decode : atom0022 = SparsePolynomial.decodeCubic 15 atom0022Coded := by decide +kernel
theorem atom0022Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (961560 : Int) atom0022Coded) := by
  have h := atom0022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0023 : SparsePolynomial.Poly := [([0,4,6], -4), ([1,4,6], -8), ([2,4,6], -16), ([3,4,6], -16), ([4,4,6], -16), ([4,5,6], -16), ([4,6,6], -16), ([4,6,7], -16), ([4,6,8], -16), ([4,6,9], -8), ([4,6,11], 8), ([4,6,12], 12), ([4,6,13], 16), ([4,6,14], 18)]
theorem atom0023_data : atom0023 = SparsePolynomial.monoTimes [4,6] 1 base07 := by decide +kernel
theorem eval_atom0023 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0023 = (quadB (outer g) ![1,2,2] * g 4 * g 6) := by
  rw [atom0023_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0023_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (810360 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023Coded : CoefficientMerge.Poly := [(66, -4), (291, -8), (516, -16), (741, -16), (966, -16), (981, -16), (996, -16), (997, -16), (998, -16), (999, -8), (1001, 8), (1002, 12), (1003, 16), (1004, 18)]
theorem atom0023Coded_decode : atom0023 = SparsePolynomial.decodeCubic 15 atom0023Coded := by decide +kernel
theorem atom0023Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (810360 : Int) atom0023Coded) := by
  have h := atom0023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0024 : SparsePolynomial.Poly := [([0,4,7], -4), ([1,4,7], -8), ([2,4,7], -16), ([3,4,7], -16), ([4,4,7], -16), ([4,5,7], -16), ([4,6,7], -16), ([4,7,7], -16), ([4,7,8], -16), ([4,7,9], -8), ([4,7,11], 8), ([4,7,12], 12), ([4,7,13], 16), ([4,7,14], 18)]
theorem atom0024_data : atom0024 = SparsePolynomial.monoTimes [4,7] 1 base07 := by decide +kernel
theorem eval_atom0024 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = (quadB (outer g) ![1,2,2] * g 4 * g 7) := by
  rw [atom0024_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (659160 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024Coded : CoefficientMerge.Poly := [(67, -4), (292, -8), (517, -16), (742, -16), (967, -16), (982, -16), (997, -16), (1012, -16), (1013, -16), (1014, -8), (1016, 8), (1017, 12), (1018, 16), (1019, 18)]
theorem atom0024Coded_decode : atom0024 = SparsePolynomial.decodeCubic 15 atom0024Coded := by decide +kernel
theorem atom0024Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (659160 : Int) atom0024Coded) := by
  have h := atom0024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0025 : SparsePolynomial.Poly := [([0,4,8], -4), ([1,4,8], -8), ([2,4,8], -16), ([3,4,8], -16), ([4,4,8], -16), ([4,5,8], -16), ([4,6,8], -16), ([4,7,8], -16), ([4,8,8], -16), ([4,8,9], -8), ([4,8,11], 8), ([4,8,12], 12), ([4,8,13], 16), ([4,8,14], 18)]
theorem atom0025_data : atom0025 = SparsePolynomial.monoTimes [4,8] 1 base07 := by decide +kernel
theorem eval_atom0025 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0025 = (quadB (outer g) ![1,2,2] * g 4 * g 8) := by
  rw [atom0025_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0025_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (507960 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025Coded : CoefficientMerge.Poly := [(68, -4), (293, -8), (518, -16), (743, -16), (968, -16), (983, -16), (998, -16), (1013, -16), (1028, -16), (1029, -8), (1031, 8), (1032, 12), (1033, 16), (1034, 18)]
theorem atom0025Coded_decode : atom0025 = SparsePolynomial.decodeCubic 15 atom0025Coded := by decide +kernel
theorem atom0025Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (507960 : Int) atom0025Coded) := by
  have h := atom0025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0026 : SparsePolynomial.Poly := [([0,4,10], -4), ([1,4,10], -8), ([2,4,10], -16), ([3,4,10], -16), ([4,4,10], -16), ([4,5,10], -16), ([4,6,10], -16), ([4,7,10], -16), ([4,8,10], -16), ([4,9,10], -8), ([4,10,11], 8), ([4,10,12], 12), ([4,10,13], 16), ([4,10,14], 18)]
theorem atom0026_data : atom0026 = SparsePolynomial.monoTimes [4,10] 1 base07 := by decide +kernel
theorem eval_atom0026 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0026 = (quadB (outer g) ![1,2,2] * g 4 * g 10) := by
  rw [atom0026_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0026_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (517275 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026Coded : CoefficientMerge.Poly := [(70, -4), (295, -8), (520, -16), (745, -16), (970, -16), (985, -16), (1000, -16), (1015, -16), (1030, -16), (1045, -8), (1061, 8), (1062, 12), (1063, 16), (1064, 18)]
theorem atom0026Coded_decode : atom0026 = SparsePolynomial.decodeCubic 15 atom0026Coded := by decide +kernel
theorem atom0026Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (517275 : Int) atom0026Coded) := by
  have h := atom0026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0027 : SparsePolynomial.Poly := [([0,4,12], -4), ([1,4,12], -8), ([2,4,12], -16), ([3,4,12], -16), ([4,4,12], -16), ([4,5,12], -16), ([4,6,12], -16), ([4,7,12], -16), ([4,8,12], -16), ([4,9,12], -8), ([4,11,12], 8), ([4,12,12], 12), ([4,12,13], 16), ([4,12,14], 18)]
theorem atom0027_data : atom0027 = SparsePolynomial.monoTimes [4,12] 1 base07 := by decide +kernel
theorem eval_atom0027 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0027 = (quadB (outer g) ![1,2,2] * g 4 * g 12) := by
  rw [atom0027_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0027_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (838305 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027Coded : CoefficientMerge.Poly := [(72, -4), (297, -8), (522, -16), (747, -16), (972, -16), (987, -16), (1002, -16), (1017, -16), (1032, -16), (1047, -8), (1077, 8), (1092, 12), (1093, 16), (1094, 18)]
theorem atom0027Coded_decode : atom0027 = SparsePolynomial.decodeCubic 15 atom0027Coded := by decide +kernel
theorem atom0027Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (838305 : Int) atom0027Coded) := by
  have h := atom0027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0028 : SparsePolynomial.Poly := [([0,4,13], -4), ([1,4,13], -8), ([2,4,13], -16), ([3,4,13], -16), ([4,4,13], -16), ([4,5,13], -16), ([4,6,13], -16), ([4,7,13], -16), ([4,8,13], -16), ([4,9,13], -8), ([4,11,13], 8), ([4,12,13], 12), ([4,13,13], 16), ([4,13,14], 18)]
theorem atom0028_data : atom0028 = SparsePolynomial.monoTimes [4,13] 1 base07 := by decide +kernel
theorem eval_atom0028 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0028 = (quadB (outer g) ![1,2,2] * g 4 * g 13) := by
  rw [atom0028_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0028_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2803725 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028Coded : CoefficientMerge.Poly := [(73, -4), (298, -8), (523, -16), (748, -16), (973, -16), (988, -16), (1003, -16), (1018, -16), (1033, -16), (1048, -8), (1078, 8), (1093, 12), (1108, 16), (1109, 18)]
theorem atom0028Coded_decode : atom0028 = SparsePolynomial.decodeCubic 15 atom0028Coded := by decide +kernel
theorem atom0028Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2803725 : Int) atom0028Coded) := by
  have h := atom0028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0029 : SparsePolynomial.Poly := [([0,4,14], -4), ([1,4,14], -8), ([2,4,14], -16), ([3,4,14], -16), ([4,4,14], -16), ([4,5,14], -16), ([4,6,14], -16), ([4,7,14], -16), ([4,8,14], -16), ([4,9,14], -8), ([4,11,14], 8), ([4,12,14], 12), ([4,13,14], 16), ([4,14,14], 18)]
theorem atom0029_data : atom0029 = SparsePolynomial.monoTimes [4,14] 1 base07 := by decide +kernel
theorem eval_atom0029 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = (quadB (outer g) ![1,2,2] * g 4 * g 14) := by
  rw [atom0029_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1367145 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029Coded : CoefficientMerge.Poly := [(74, -4), (299, -8), (524, -16), (749, -16), (974, -16), (989, -16), (1004, -16), (1019, -16), (1034, -16), (1049, -8), (1079, 8), (1094, 12), (1109, 16), (1124, 18)]
theorem atom0029Coded_decode : atom0029 = SparsePolynomial.decodeCubic 15 atom0029Coded := by decide +kernel
theorem atom0029Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1367145 : Int) atom0029Coded) := by
  have h := atom0029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0030 : SparsePolynomial.Poly := [([0,5,6], -4), ([1,5,6], -8), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -8), ([5,6,11], 8), ([5,6,12], 12), ([5,6,13], 16), ([5,6,14], 18)]
theorem atom0030_data : atom0030 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0030 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0030 = (quadB (outer g) ![1,2,2] * g 5 * g 6) := by
  rw [atom0030_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0030_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1557720 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030Coded : CoefficientMerge.Poly := [(81, -4), (306, -8), (531, -16), (756, -16), (981, -16), (1206, -16), (1221, -16), (1222, -16), (1223, -16), (1224, -8), (1226, 8), (1227, 12), (1228, 16), (1229, 18)]
theorem atom0030Coded_decode : atom0030 = SparsePolynomial.decodeCubic 15 atom0030Coded := by decide +kernel
theorem atom0030Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1557720 : Int) atom0030Coded) := by
  have h := atom0030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0031 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -16), ([5,7,7], -16), ([5,7,8], -16), ([5,7,9], -8), ([5,7,11], 8), ([5,7,12], 12), ([5,7,13], 16), ([5,7,14], 18)]
theorem atom0031_data : atom0031 = SparsePolynomial.monoTimes [5,7] 1 base07 := by decide +kernel
theorem eval_atom0031 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0031 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0031_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0031_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1619280 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031Coded : CoefficientMerge.Poly := [(82, -4), (307, -8), (532, -16), (757, -16), (982, -16), (1207, -16), (1222, -16), (1237, -16), (1238, -16), (1239, -8), (1241, 8), (1242, 12), (1243, 16), (1244, 18)]
theorem atom0031Coded_decode : atom0031 = SparsePolynomial.decodeCubic 15 atom0031Coded := by decide +kernel
theorem atom0031Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1619280 : Int) atom0031Coded) := by
  have h := atom0031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0032 : SparsePolynomial.Poly := [([0,5,8], -4), ([1,5,8], -8), ([2,5,8], -16), ([3,5,8], -16), ([4,5,8], -16), ([5,5,8], -16), ([5,6,8], -16), ([5,7,8], -16), ([5,8,8], -16), ([5,8,9], -8), ([5,8,11], 8), ([5,8,12], 12), ([5,8,13], 16), ([5,8,14], 18)]
theorem atom0032_data : atom0032 = SparsePolynomial.monoTimes [5,8] 1 base07 := by decide +kernel
theorem eval_atom0032 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0032 = (quadB (outer g) ![1,2,2] * g 5 * g 8) := by
  rw [atom0032_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0032_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1214280 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032Coded : CoefficientMerge.Poly := [(83, -4), (308, -8), (533, -16), (758, -16), (983, -16), (1208, -16), (1223, -16), (1238, -16), (1253, -16), (1254, -8), (1256, 8), (1257, 12), (1258, 16), (1259, 18)]
theorem atom0032Coded_decode : atom0032 = SparsePolynomial.decodeCubic 15 atom0032Coded := by decide +kernel
theorem atom0032Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1214280 : Int) atom0032Coded) := by
  have h := atom0032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0033 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -16), ([5,7,10], -16), ([5,8,10], -16), ([5,9,10], -8), ([5,10,11], 8), ([5,10,12], 12), ([5,10,13], 16), ([5,10,14], 18)]
theorem atom0033_data : atom0033 = SparsePolynomial.monoTimes [5,10] 1 base07 := by decide +kernel
theorem eval_atom0033 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0033_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (882045 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033Coded : CoefficientMerge.Poly := [(85, -4), (310, -8), (535, -16), (760, -16), (985, -16), (1210, -16), (1225, -16), (1240, -16), (1255, -16), (1270, -8), (1286, 8), (1287, 12), (1288, 16), (1289, 18)]
theorem atom0033Coded_decode : atom0033 = SparsePolynomial.decodeCubic 15 atom0033Coded := by decide +kernel
theorem atom0033Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (882045 : Int) atom0033Coded) := by
  have h := atom0033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0034 : SparsePolynomial.Poly := [([0,5,12], -4), ([1,5,12], -8), ([2,5,12], -16), ([3,5,12], -16), ([4,5,12], -16), ([5,5,12], -16), ([5,6,12], -16), ([5,7,12], -16), ([5,8,12], -16), ([5,9,12], -8), ([5,11,12], 8), ([5,12,12], 12), ([5,12,13], 16), ([5,12,14], 18)]
theorem atom0034_data : atom0034 = SparsePolynomial.monoTimes [5,12] 1 base07 := by decide +kernel
theorem eval_atom0034 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0034 = (quadB (outer g) ![1,2,2] * g 5 * g 12) := by
  rw [atom0034_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0034_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1027575 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034Coded : CoefficientMerge.Poly := [(87, -4), (312, -8), (537, -16), (762, -16), (987, -16), (1212, -16), (1227, -16), (1242, -16), (1257, -16), (1272, -8), (1302, 8), (1317, 12), (1318, 16), (1319, 18)]
theorem atom0034Coded_decode : atom0034 = SparsePolynomial.decodeCubic 15 atom0034Coded := by decide +kernel
theorem atom0034Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1027575 : Int) atom0034Coded) := by
  have h := atom0034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0035 : SparsePolynomial.Poly := [([0,5,13], -4), ([1,5,13], -8), ([2,5,13], -16), ([3,5,13], -16), ([4,5,13], -16), ([5,5,13], -16), ([5,6,13], -16), ([5,7,13], -16), ([5,8,13], -16), ([5,9,13], -8), ([5,11,13], 8), ([5,12,13], 12), ([5,13,13], 16), ([5,13,14], 18)]
theorem atom0035_data : atom0035 = SparsePolynomial.monoTimes [5,13] 1 base07 := by decide +kernel
theorem eval_atom0035 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0035 = (quadB (outer g) ![1,2,2] * g 5 * g 13) := by
  rw [atom0035_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0035_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2960595 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035Coded : CoefficientMerge.Poly := [(88, -4), (313, -8), (538, -16), (763, -16), (988, -16), (1213, -16), (1228, -16), (1243, -16), (1258, -16), (1273, -8), (1303, 8), (1318, 12), (1333, 16), (1334, 18)]
theorem atom0035Coded_decode : atom0035 = SparsePolynomial.decodeCubic 15 atom0035Coded := by decide +kernel
theorem atom0035Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2960595 : Int) atom0035Coded) := by
  have h := atom0035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0036 : SparsePolynomial.Poly := [([0,5,14], -4), ([1,5,14], -8), ([2,5,14], -16), ([3,5,14], -16), ([4,5,14], -16), ([5,5,14], -16), ([5,6,14], -16), ([5,7,14], -16), ([5,8,14], -16), ([5,9,14], -8), ([5,11,14], 8), ([5,12,14], 12), ([5,13,14], 16), ([5,14,14], 18)]
theorem atom0036_data : atom0036 = SparsePolynomial.monoTimes [5,14] 1 base07 := by decide +kernel
theorem eval_atom0036 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = (quadB (outer g) ![1,2,2] * g 5 * g 14) := by
  rw [atom0036_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1491615 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036Coded : CoefficientMerge.Poly := [(89, -4), (314, -8), (539, -16), (764, -16), (989, -16), (1214, -16), (1229, -16), (1244, -16), (1259, -16), (1274, -8), (1304, 8), (1319, 12), (1334, 16), (1349, 18)]
theorem atom0036Coded_decode : atom0036 = SparsePolynomial.decodeCubic 15 atom0036Coded := by decide +kernel
theorem atom0036Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1491615 : Int) atom0036Coded) := by
  have h := atom0036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0037 : SparsePolynomial.Poly := [([0,6,7], -4), ([1,6,7], -8), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -8), ([6,7,11], 8), ([6,7,12], 12), ([6,7,13], 16), ([6,7,14], 18)]
theorem atom0037_data : atom0037 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0037 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0037 = (quadB (outer g) ![1,2,2] * g 6 * g 7) := by
  rw [atom0037_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0037_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1614192 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037Coded : CoefficientMerge.Poly := [(97, -4), (322, -8), (547, -16), (772, -16), (997, -16), (1222, -16), (1447, -16), (1462, -16), (1463, -16), (1464, -8), (1466, 8), (1467, 12), (1468, 16), (1469, 18)]
theorem atom0037Coded_decode : atom0037 = SparsePolynomial.decodeCubic 15 atom0037Coded := by decide +kernel
theorem atom0037Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1614192 : Int) atom0037Coded) := by
  have h := atom0037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0038 : SparsePolynomial.Poly := [([0,6,8], -4), ([1,6,8], -8), ([2,6,8], -16), ([3,6,8], -16), ([4,6,8], -16), ([5,6,8], -16), ([6,6,8], -16), ([6,7,8], -16), ([6,8,8], -16), ([6,8,9], -8), ([6,8,11], 8), ([6,8,12], 12), ([6,8,13], 16), ([6,8,14], 18)]
theorem atom0038_data : atom0038 = SparsePolynomial.monoTimes [6,8] 1 base07 := by decide +kernel
theorem eval_atom0038 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = (quadB (outer g) ![1,2,2] * g 6 * g 8) := by
  rw [atom0038_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1905120 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038Coded : CoefficientMerge.Poly := [(98, -4), (323, -8), (548, -16), (773, -16), (998, -16), (1223, -16), (1448, -16), (1463, -16), (1478, -16), (1479, -8), (1481, 8), (1482, 12), (1483, 16), (1484, 18)]
theorem atom0038Coded_decode : atom0038 = SparsePolynomial.decodeCubic 15 atom0038Coded := by decide +kernel
theorem atom0038Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1905120 : Int) atom0038Coded) := by
  have h := atom0038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0039 : SparsePolynomial.Poly := [([0,6,10], -4), ([1,6,10], -8), ([2,6,10], -16), ([3,6,10], -16), ([4,6,10], -16), ([5,6,10], -16), ([6,6,10], -16), ([6,7,10], -16), ([6,8,10], -16), ([6,9,10], -8), ([6,10,11], 8), ([6,10,12], 12), ([6,10,13], 16), ([6,10,14], 18)]
theorem atom0039_data : atom0039 = SparsePolynomial.monoTimes [6,10] 1 base07 := by decide +kernel
theorem eval_atom0039 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0039 = (quadB (outer g) ![1,2,2] * g 6 * g 10) := by
  rw [atom0039_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0039_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1070685 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039Coded : CoefficientMerge.Poly := [(100, -4), (325, -8), (550, -16), (775, -16), (1000, -16), (1225, -16), (1450, -16), (1465, -16), (1480, -16), (1495, -8), (1511, 8), (1512, 12), (1513, 16), (1514, 18)]
theorem atom0039Coded_decode : atom0039 = SparsePolynomial.decodeCubic 15 atom0039Coded := by decide +kernel
theorem atom0039Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1070685 : Int) atom0039Coded) := by
  have h := atom0039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0040 : SparsePolynomial.Poly := [([0,6,12], -4), ([1,6,12], -8), ([2,6,12], -16), ([3,6,12], -16), ([4,6,12], -16), ([5,6,12], -16), ([6,6,12], -16), ([6,7,12], -16), ([6,8,12], -16), ([6,9,12], -8), ([6,11,12], 8), ([6,12,12], 12), ([6,12,13], 16), ([6,12,14], 18)]
theorem atom0040_data : atom0040 = SparsePolynomial.monoTimes [6,12] 1 base07 := by decide +kernel
theorem eval_atom0040 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0040 = (quadB (outer g) ![1,2,2] * g 6 * g 12) := by
  rw [atom0040_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0040_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (868455 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040Coded : CoefficientMerge.Poly := [(102, -4), (327, -8), (552, -16), (777, -16), (1002, -16), (1227, -16), (1452, -16), (1467, -16), (1482, -16), (1497, -8), (1527, 8), (1542, 12), (1543, 16), (1544, 18)]
theorem atom0040Coded_decode : atom0040 = SparsePolynomial.decodeCubic 15 atom0040Coded := by decide +kernel
theorem atom0040Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (868455 : Int) atom0040Coded) := by
  have h := atom0040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0041 : SparsePolynomial.Poly := [([0,6,13], -4), ([1,6,13], -8), ([2,6,13], -16), ([3,6,13], -16), ([4,6,13], -16), ([5,6,13], -16), ([6,6,13], -16), ([6,7,13], -16), ([6,8,13], -16), ([6,9,13], -8), ([6,11,13], 8), ([6,12,13], 12), ([6,13,13], 16), ([6,13,14], 18)]
theorem atom0041_data : atom0041 = SparsePolynomial.monoTimes [6,13] 1 base07 := by decide +kernel
theorem eval_atom0041 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0041 = (quadB (outer g) ![1,2,2] * g 6 * g 13) := by
  rw [atom0041_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0041_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2679075 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041Coded : CoefficientMerge.Poly := [(103, -4), (328, -8), (553, -16), (778, -16), (1003, -16), (1228, -16), (1453, -16), (1468, -16), (1483, -16), (1498, -8), (1528, 8), (1543, 12), (1558, 16), (1559, 18)]
theorem atom0041Coded_decode : atom0041 = SparsePolynomial.decodeCubic 15 atom0041Coded := by decide +kernel
theorem atom0041Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2679075 : Int) atom0041Coded) := by
  have h := atom0041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0042 : SparsePolynomial.Poly := [([0,6,14], -4), ([1,6,14], -8), ([2,6,14], -16), ([3,6,14], -16), ([4,6,14], -16), ([5,6,14], -16), ([6,6,14], -16), ([6,7,14], -16), ([6,8,14], -16), ([6,9,14], -8), ([6,11,14], 8), ([6,12,14], 12), ([6,13,14], 16), ([6,14,14], 18)]
theorem atom0042_data : atom0042 = SparsePolynomial.monoTimes [6,14] 1 base07 := by decide +kernel
theorem eval_atom0042 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0042 = (quadB (outer g) ![1,2,2] * g 6 * g 14) := by
  rw [atom0042_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0042_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1087695 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042Coded : CoefficientMerge.Poly := [(104, -4), (329, -8), (554, -16), (779, -16), (1004, -16), (1229, -16), (1454, -16), (1469, -16), (1484, -16), (1499, -8), (1529, 8), (1544, 12), (1559, 16), (1574, 18)]
theorem atom0042Coded_decode : atom0042 = SparsePolynomial.decodeCubic 15 atom0042Coded := by decide +kernel
theorem atom0042Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1087695 : Int) atom0042Coded) := by
  have h := atom0042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0043 : SparsePolynomial.Poly := [([0,7,8], -4), ([1,7,8], -8), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -8), ([7,8,11], 8), ([7,8,12], 12), ([7,8,13], 16), ([7,8,14], 18)]
theorem atom0043_data : atom0043 = SparsePolynomial.monoTimes [7,8] 1 base07 := by decide +kernel
theorem eval_atom0043 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0043 = (quadB (outer g) ![1,2,2] * g 7 * g 8) := by
  rw [atom0043_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0043_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1443640 : Int) atom0043) := by
  rw [SparsePolynomial.eval_scale, eval_atom0043]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0043Coded : CoefficientMerge.Poly := [(113, -4), (338, -8), (563, -16), (788, -16), (1013, -16), (1238, -16), (1463, -16), (1688, -16), (1703, -16), (1704, -8), (1706, 8), (1707, 12), (1708, 16), (1709, 18)]
theorem atom0043Coded_decode : atom0043 = SparsePolynomial.decodeCubic 15 atom0043Coded := by decide +kernel
theorem atom0043Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1443640 : Int) atom0043Coded) := by
  have h := atom0043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0044 : SparsePolynomial.Poly := [([0,7,9], -4), ([1,7,9], -8), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -8), ([7,9,11], 8), ([7,9,12], 12), ([7,9,13], 16), ([7,9,14], 18)]
theorem atom0044_data : atom0044 = SparsePolynomial.monoTimes [7,9] 1 base07 := by decide +kernel
theorem eval_atom0044 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0044 = (quadB (outer g) ![1,2,2] * g 7 * g 9) := by
  rw [atom0044_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0044_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122520 : Int) atom0044) := by
  rw [SparsePolynomial.eval_scale, eval_atom0044]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0044Coded : CoefficientMerge.Poly := [(114, -4), (339, -8), (564, -16), (789, -16), (1014, -16), (1239, -16), (1464, -16), (1689, -16), (1704, -16), (1719, -8), (1721, 8), (1722, 12), (1723, 16), (1724, 18)]
theorem atom0044Coded_decode : atom0044 = SparsePolynomial.decodeCubic 15 atom0044Coded := by decide +kernel
theorem atom0044Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (122520 : Int) atom0044Coded) := by
  have h := atom0044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0045 : SparsePolynomial.Poly := [([0,7,10], -4), ([1,7,10], -8), ([2,7,10], -16), ([3,7,10], -16), ([4,7,10], -16), ([5,7,10], -16), ([6,7,10], -16), ([7,7,10], -16), ([7,8,10], -16), ([7,9,10], -8), ([7,10,11], 8), ([7,10,12], 12), ([7,10,13], 16), ([7,10,14], 18)]
theorem atom0045_data : atom0045 = SparsePolynomial.monoTimes [7,10] 1 base07 := by decide +kernel
theorem eval_atom0045 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0045 = (quadB (outer g) ![1,2,2] * g 7 * g 10) := by
  rw [atom0045_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0045_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1169520 : Int) atom0045) := by
  rw [SparsePolynomial.eval_scale, eval_atom0045]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0045Coded : CoefficientMerge.Poly := [(115, -4), (340, -8), (565, -16), (790, -16), (1015, -16), (1240, -16), (1465, -16), (1690, -16), (1705, -16), (1720, -8), (1736, 8), (1737, 12), (1738, 16), (1739, 18)]
theorem atom0045Coded_decode : atom0045 = SparsePolynomial.decodeCubic 15 atom0045Coded := by decide +kernel
theorem atom0045Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1169520 : Int) atom0045Coded) := by
  have h := atom0045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0046 : SparsePolynomial.Poly := [([0,7,12], -4), ([1,7,12], -8), ([2,7,12], -16), ([3,7,12], -16), ([4,7,12], -16), ([5,7,12], -16), ([6,7,12], -16), ([7,7,12], -16), ([7,8,12], -16), ([7,9,12], -8), ([7,11,12], 8), ([7,12,12], 12), ([7,12,13], 16), ([7,12,14], 18)]
theorem atom0046_data : atom0046 = SparsePolynomial.monoTimes [7,12] 1 base07 := by decide +kernel
theorem eval_atom0046 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0046 = (quadB (outer g) ![1,2,2] * g 7 * g 12) := by
  rw [atom0046_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0046_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (343680 : Int) atom0046) := by
  rw [SparsePolynomial.eval_scale, eval_atom0046]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0046Coded : CoefficientMerge.Poly := [(117, -4), (342, -8), (567, -16), (792, -16), (1017, -16), (1242, -16), (1467, -16), (1692, -16), (1707, -16), (1722, -8), (1752, 8), (1767, 12), (1768, 16), (1769, 18)]
theorem atom0046Coded_decode : atom0046 = SparsePolynomial.decodeCubic 15 atom0046Coded := by decide +kernel
theorem atom0046Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (343680 : Int) atom0046Coded) := by
  have h := atom0046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0047 : SparsePolynomial.Poly := [([0,7,13], -4), ([1,7,13], -8), ([2,7,13], -16), ([3,7,13], -16), ([4,7,13], -16), ([5,7,13], -16), ([6,7,13], -16), ([7,7,13], -16), ([7,8,13], -16), ([7,9,13], -8), ([7,11,13], 8), ([7,12,13], 12), ([7,13,13], 16), ([7,13,14], 18)]
theorem atom0047_data : atom0047 = SparsePolynomial.monoTimes [7,13] 1 base07 := by decide +kernel
theorem eval_atom0047 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0047 = (quadB (outer g) ![1,2,2] * g 7 * g 13) := by
  rw [atom0047_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0047_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1872840 : Int) atom0047) := by
  rw [SparsePolynomial.eval_scale, eval_atom0047]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0047Coded : CoefficientMerge.Poly := [(118, -4), (343, -8), (568, -16), (793, -16), (1018, -16), (1243, -16), (1468, -16), (1693, -16), (1708, -16), (1723, -8), (1753, 8), (1768, 12), (1783, 16), (1784, 18)]
theorem atom0047Coded_decode : atom0047 = SparsePolynomial.decodeCubic 15 atom0047Coded := by decide +kernel
theorem atom0047Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1872840 : Int) atom0047Coded) := by
  have h := atom0047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0048 : SparsePolynomial.Poly := [([0,8,9], -4), ([1,8,9], -8), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -8), ([8,9,11], 8), ([8,9,12], 12), ([8,9,13], 16), ([8,9,14], 18)]
theorem atom0048_data : atom0048 = SparsePolynomial.monoTimes [8,9] 1 base07 := by decide +kernel
theorem eval_atom0048 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0048 = (quadB (outer g) ![1,2,2] * g 8 * g 9) := by
  rw [atom0048_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0048_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (692550 : Int) atom0048) := by
  rw [SparsePolynomial.eval_scale, eval_atom0048]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0048Coded : CoefficientMerge.Poly := [(129, -4), (354, -8), (579, -16), (804, -16), (1029, -16), (1254, -16), (1479, -16), (1704, -16), (1929, -16), (1944, -8), (1946, 8), (1947, 12), (1948, 16), (1949, 18)]
theorem atom0048Coded_decode : atom0048 = SparsePolynomial.decodeCubic 15 atom0048Coded := by decide +kernel
theorem atom0048Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (692550 : Int) atom0048Coded) := by
  have h := atom0048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0049 : SparsePolynomial.Poly := [([0,8,10], -4), ([1,8,10], -8), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -8), ([8,10,11], 8), ([8,10,12], 12), ([8,10,13], 16), ([8,10,14], 18)]
theorem atom0049_data : atom0049 = SparsePolynomial.monoTimes [8,10] 1 base07 := by decide +kernel
theorem eval_atom0049 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0049 = (quadB (outer g) ![1,2,2] * g 8 * g 10) := by
  rw [atom0049_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0049_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1251450 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049Coded : CoefficientMerge.Poly := [(130, -4), (355, -8), (580, -16), (805, -16), (1030, -16), (1255, -16), (1480, -16), (1705, -16), (1930, -16), (1945, -8), (1961, 8), (1962, 12), (1963, 16), (1964, 18)]
theorem atom0049Coded_decode : atom0049 = SparsePolynomial.decodeCubic 15 atom0049Coded := by decide +kernel
theorem atom0049Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1251450 : Int) atom0049Coded) := by
  have h := atom0049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0050 : SparsePolynomial.Poly := [([0,8,13], -4), ([1,8,13], -8), ([2,8,13], -16), ([3,8,13], -16), ([4,8,13], -16), ([5,8,13], -16), ([6,8,13], -16), ([7,8,13], -16), ([8,8,13], -16), ([8,9,13], -8), ([8,11,13], 8), ([8,12,13], 12), ([8,13,13], 16), ([8,13,14], 18)]
theorem atom0050_data : atom0050 = SparsePolynomial.monoTimes [8,13] 1 base07 := by decide +kernel
theorem eval_atom0050 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0050 = (quadB (outer g) ![1,2,2] * g 8 * g 13) := by
  rw [atom0050_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0050_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (468990 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050Coded : CoefficientMerge.Poly := [(133, -4), (358, -8), (583, -16), (808, -16), (1033, -16), (1258, -16), (1483, -16), (1708, -16), (1933, -16), (1948, -8), (1978, 8), (1993, 12), (2008, 16), (2009, 18)]
theorem atom0050Coded_decode : atom0050 = SparsePolynomial.decodeCubic 15 atom0050Coded := by decide +kernel
theorem atom0050Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (468990 : Int) atom0050Coded) := by
  have h := atom0050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0051 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -14), ([0,1,10], -10), ([0,1,11], -2), ([0,1,12], 2), ([0,1,13], 10), ([0,1,14], 18)]
theorem atom0051_data : atom0051 = SparsePolynomial.monoTimes [0,1] 1 base08 := by decide +kernel
theorem eval_atom0051 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0051 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0051_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0051_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524880 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051Coded : CoefficientMerge.Poly := [(1, -8), (16, -12), (17, -16), (18, -16), (19, -16), (20, -16), (21, -16), (22, -16), (23, -16), (24, -14), (25, -10), (26, -2), (27, 2), (28, 10), (29, 18)]
theorem atom0051Coded_decode : atom0051 = SparsePolynomial.decodeCubic 15 atom0051Coded := by decide +kernel
theorem atom0051Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (524880 : Int) atom0051Coded) := by
  have h := atom0051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0052 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -14), ([0,2,10], -10), ([0,2,11], -2), ([0,2,12], 2), ([0,2,13], 10), ([0,2,14], 18)]
theorem atom0052_data : atom0052 = SparsePolynomial.monoTimes [0,2] 1 base08 := by decide +kernel
theorem eval_atom0052 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0052 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0052_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0052_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (762480 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052Coded : CoefficientMerge.Poly := [(2, -8), (17, -12), (32, -16), (33, -16), (34, -16), (35, -16), (36, -16), (37, -16), (38, -16), (39, -14), (40, -10), (41, -2), (42, 2), (43, 10), (44, 18)]
theorem atom0052Coded_decode : atom0052 = SparsePolynomial.decodeCubic 15 atom0052Coded := by decide +kernel
theorem atom0052Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (762480 : Int) atom0052Coded) := by
  have h := atom0052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0053 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -14), ([0,3,10], -10), ([0,3,11], -2), ([0,3,12], 2), ([0,3,13], 10), ([0,3,14], 18)]
theorem atom0053_data : atom0053 = SparsePolynomial.monoTimes [0,3] 1 base08 := by decide +kernel
theorem eval_atom0053 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0053 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0053_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0053_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1000080 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053Coded : CoefficientMerge.Poly := [(3, -8), (18, -12), (33, -16), (48, -16), (49, -16), (50, -16), (51, -16), (52, -16), (53, -16), (54, -14), (55, -10), (56, -2), (57, 2), (58, 10), (59, 18)]
theorem atom0053Coded_decode : atom0053 = SparsePolynomial.decodeCubic 15 atom0053Coded := by decide +kernel
theorem atom0053Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1000080 : Int) atom0053Coded) := by
  have h := atom0053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0054 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -14), ([0,4,10], -10), ([0,4,11], -2), ([0,4,12], 2), ([0,4,13], 10), ([0,4,14], 18)]
theorem atom0054_data : atom0054 = SparsePolynomial.monoTimes [0,4] 1 base08 := by decide +kernel
theorem eval_atom0054 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0054 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0054_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0054_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1237680 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054Coded : CoefficientMerge.Poly := [(4, -8), (19, -12), (34, -16), (49, -16), (64, -16), (65, -16), (66, -16), (67, -16), (68, -16), (69, -14), (70, -10), (71, -2), (72, 2), (73, 10), (74, 18)]
theorem atom0054Coded_decode : atom0054 = SparsePolynomial.decodeCubic 15 atom0054Coded := by decide +kernel
theorem atom0054Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1237680 : Int) atom0054Coded) := by
  have h := atom0054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0055 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -14), ([0,5,10], -10), ([0,5,11], -2), ([0,5,12], 2), ([0,5,13], 10), ([0,5,14], 18)]
theorem atom0055_data : atom0055 = SparsePolynomial.monoTimes [0,5] 1 base08 := by decide +kernel
theorem eval_atom0055 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0055 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0055_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0055_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1475280 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055Coded : CoefficientMerge.Poly := [(5, -8), (20, -12), (35, -16), (50, -16), (65, -16), (80, -16), (81, -16), (82, -16), (83, -16), (84, -14), (85, -10), (86, -2), (87, 2), (88, 10), (89, 18)]
theorem atom0055Coded_decode : atom0055 = SparsePolynomial.decodeCubic 15 atom0055Coded := by decide +kernel
theorem atom0055Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1475280 : Int) atom0055Coded) := by
  have h := atom0055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0056 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -14), ([0,6,10], -10), ([0,6,11], -2), ([0,6,12], 2), ([0,6,13], 10), ([0,6,14], 18)]
theorem atom0056_data : atom0056 = SparsePolynomial.monoTimes [0,6] 1 base08 := by decide +kernel
theorem eval_atom0056 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0056 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0056_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0056_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1712880 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056Coded : CoefficientMerge.Poly := [(6, -8), (21, -12), (36, -16), (51, -16), (66, -16), (81, -16), (96, -16), (97, -16), (98, -16), (99, -14), (100, -10), (101, -2), (102, 2), (103, 10), (104, 18)]
theorem atom0056Coded_decode : atom0056 = SparsePolynomial.decodeCubic 15 atom0056Coded := by decide +kernel
theorem atom0056Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1712880 : Int) atom0056Coded) := by
  have h := atom0056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0057 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -14), ([0,7,10], -10), ([0,7,11], -2), ([0,7,12], 2), ([0,7,13], 10), ([0,7,14], 18)]
theorem atom0057_data : atom0057 = SparsePolynomial.monoTimes [0,7] 1 base08 := by decide +kernel
theorem eval_atom0057 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0057 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0057_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0057_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1950480 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057Coded : CoefficientMerge.Poly := [(7, -8), (22, -12), (37, -16), (52, -16), (67, -16), (82, -16), (97, -16), (112, -16), (113, -16), (114, -14), (115, -10), (116, -2), (117, 2), (118, 10), (119, 18)]
theorem atom0057Coded_decode : atom0057 = SparsePolynomial.decodeCubic 15 atom0057Coded := by decide +kernel
theorem atom0057Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1950480 : Int) atom0057Coded) := by
  have h := atom0057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0058 : SparsePolynomial.Poly := [([0,0,8], -8), ([0,1,8], -12), ([0,2,8], -16), ([0,3,8], -16), ([0,4,8], -16), ([0,5,8], -16), ([0,6,8], -16), ([0,7,8], -16), ([0,8,8], -16), ([0,8,9], -14), ([0,8,10], -10), ([0,8,11], -2), ([0,8,12], 2), ([0,8,13], 10), ([0,8,14], 18)]
theorem atom0058_data : atom0058 = SparsePolynomial.monoTimes [0,8] 1 base08 := by decide +kernel
theorem eval_atom0058 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0058 = (quadB (outer g) ![2,2,1] * g 0 * g 8) := by
  rw [atom0058_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0058_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2188080 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058Coded : CoefficientMerge.Poly := [(8, -8), (23, -12), (38, -16), (53, -16), (68, -16), (83, -16), (98, -16), (113, -16), (128, -16), (129, -14), (130, -10), (131, -2), (132, 2), (133, 10), (134, 18)]
theorem atom0058Coded_decode : atom0058 = SparsePolynomial.decodeCubic 15 atom0058Coded := by decide +kernel
theorem atom0058Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2188080 : Int) atom0058Coded) := by
  have h := atom0058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0059 : SparsePolynomial.Poly := [([0,0,13], -8), ([0,1,13], -12), ([0,2,13], -16), ([0,3,13], -16), ([0,4,13], -16), ([0,5,13], -16), ([0,6,13], -16), ([0,7,13], -16), ([0,8,13], -16), ([0,9,13], -14), ([0,10,13], -10), ([0,11,13], -2), ([0,12,13], 2), ([0,13,13], 10), ([0,13,14], 18)]
theorem atom0059_data : atom0059 = SparsePolynomial.monoTimes [0,13] 1 base08 := by decide +kernel
theorem eval_atom0059 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0059 = (quadB (outer g) ![2,2,1] * g 0 * g 13) := by
  rw [atom0059_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0059_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (548640 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059Coded : CoefficientMerge.Poly := [(13, -8), (28, -12), (43, -16), (58, -16), (73, -16), (88, -16), (103, -16), (118, -16), (133, -16), (148, -14), (163, -10), (178, -2), (193, 2), (208, 10), (209, 18)]
theorem atom0059Coded_decode : atom0059 = SparsePolynomial.decodeCubic 15 atom0059Coded := by decide +kernel
theorem atom0059Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (548640 : Int) atom0059Coded) := by
  have h := atom0059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0060 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -14), ([1,1,10], -10), ([1,1,11], -2), ([1,1,12], 2), ([1,1,13], 10), ([1,1,14], 18)]
theorem atom0060_data : atom0060 = SparsePolynomial.monoTimes [1,1] 1 base08 := by decide +kernel
theorem eval_atom0060 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0060 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0060_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0060_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253530 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060Coded : CoefficientMerge.Poly := [(16, -8), (241, -12), (242, -16), (243, -16), (244, -16), (245, -16), (246, -16), (247, -16), (248, -16), (249, -14), (250, -10), (251, -2), (252, 2), (253, 10), (254, 18)]
theorem atom0060Coded_decode : atom0060 = SparsePolynomial.decodeCubic 15 atom0060Coded := by decide +kernel
theorem atom0060Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (253530 : Int) atom0060Coded) := by
  have h := atom0060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0061 : SparsePolynomial.Poly := [([0,1,14], -8), ([1,1,14], -12), ([1,2,14], -16), ([1,3,14], -16), ([1,4,14], -16), ([1,5,14], -16), ([1,6,14], -16), ([1,7,14], -16), ([1,8,14], -16), ([1,9,14], -14), ([1,10,14], -10), ([1,11,14], -2), ([1,12,14], 2), ([1,13,14], 10), ([1,14,14], 18)]
theorem atom0061_data : atom0061 = SparsePolynomial.monoTimes [1,14] 1 base08 := by decide +kernel
theorem eval_atom0061 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0061 = (quadB (outer g) ![2,2,1] * g 1 * g 14) := by
  rw [atom0061_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0061_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291780 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061Coded : CoefficientMerge.Poly := [(29, -8), (254, -12), (269, -16), (284, -16), (299, -16), (314, -16), (329, -16), (344, -16), (359, -16), (374, -14), (389, -10), (404, -2), (419, 2), (434, 10), (449, 18)]
theorem atom0061Coded_decode : atom0061 = SparsePolynomial.decodeCubic 15 atom0061Coded := by decide +kernel
theorem atom0061Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (291780 : Int) atom0061Coded) := by
  have h := atom0061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0062 : SparsePolynomial.Poly := [([0,2,14], -8), ([1,2,14], -12), ([2,2,14], -16), ([2,3,14], -16), ([2,4,14], -16), ([2,5,14], -16), ([2,6,14], -16), ([2,7,14], -16), ([2,8,14], -16), ([2,9,14], -14), ([2,10,14], -10), ([2,11,14], -2), ([2,12,14], 2), ([2,13,14], 10), ([2,14,14], 18)]
theorem atom0062_data : atom0062 = SparsePolynomial.monoTimes [2,14] 1 base08 := by decide +kernel
theorem eval_atom0062 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0062 = (quadB (outer g) ![2,2,1] * g 2 * g 14) := by
  rw [atom0062_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0062_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (527580 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062Coded : CoefficientMerge.Poly := [(44, -8), (269, -12), (494, -16), (509, -16), (524, -16), (539, -16), (554, -16), (569, -16), (584, -16), (599, -14), (614, -10), (629, -2), (644, 2), (659, 10), (674, 18)]
theorem atom0062Coded_decode : atom0062 = SparsePolynomial.decodeCubic 15 atom0062Coded := by decide +kernel
theorem atom0062Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (527580 : Int) atom0062Coded) := by
  have h := atom0062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0063 : SparsePolynomial.Poly := [([0,3,3], -8), ([1,3,3], -12), ([2,3,3], -16), ([3,3,3], -16), ([3,3,4], -16), ([3,3,5], -16), ([3,3,6], -16), ([3,3,7], -16), ([3,3,8], -16), ([3,3,9], -14), ([3,3,10], -10), ([3,3,11], -2), ([3,3,12], 2), ([3,3,13], 10), ([3,3,14], 18)]
theorem atom0063_data : atom0063 = SparsePolynomial.monoTimes [3,3] 1 base08 := by decide +kernel
theorem eval_atom0063 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0063 = (quadB (outer g) ![2,2,1] * g 3 * g 3) := by
  rw [atom0063_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0063_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87480 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 3 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063Coded : CoefficientMerge.Poly := [(48, -8), (273, -12), (498, -16), (723, -16), (724, -16), (725, -16), (726, -16), (727, -16), (728, -16), (729, -14), (730, -10), (731, -2), (732, 2), (733, 10), (734, 18)]
theorem atom0063Coded_decode : atom0063 = SparsePolynomial.decodeCubic 15 atom0063Coded := by decide +kernel
theorem atom0063Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87480 : Int) atom0063Coded) := by
  have h := atom0063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0064 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -14), ([4,4,10], -10), ([4,4,11], -2), ([4,4,12], 2), ([4,4,13], 10), ([4,4,14], 18)]
theorem atom0064_data : atom0064 = SparsePolynomial.monoTimes [4,4] 1 base08 := by decide +kernel
theorem eval_atom0064 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0064 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0064_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0064_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (831240 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064Coded : CoefficientMerge.Poly := [(64, -8), (289, -12), (514, -16), (739, -16), (964, -16), (965, -16), (966, -16), (967, -16), (968, -16), (969, -14), (970, -10), (971, -2), (972, 2), (973, 10), (974, 18)]
theorem atom0064Coded_decode : atom0064 = SparsePolynomial.decodeCubic 15 atom0064Coded := by decide +kernel
theorem atom0064Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (831240 : Int) atom0064Coded) := by
  have h := atom0064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0065 : SparsePolynomial.Poly := [([0,6,6], -8), ([1,6,6], -12), ([2,6,6], -16), ([3,6,6], -16), ([4,6,6], -16), ([5,6,6], -16), ([6,6,6], -16), ([6,6,7], -16), ([6,6,8], -16), ([6,6,9], -14), ([6,6,10], -10), ([6,6,11], -2), ([6,6,12], 2), ([6,6,13], 10), ([6,6,14], 18)]
theorem atom0065_data : atom0065 = SparsePolynomial.monoTimes [6,6] 1 base08 := by decide +kernel
theorem eval_atom0065 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0065 = (quadB (outer g) ![2,2,1] * g 6 * g 6) := by
  rw [atom0065_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0065_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146880 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065Coded : CoefficientMerge.Poly := [(96, -8), (321, -12), (546, -16), (771, -16), (996, -16), (1221, -16), (1446, -16), (1447, -16), (1448, -16), (1449, -14), (1450, -10), (1451, -2), (1452, 2), (1453, 10), (1454, 18)]
theorem atom0065Coded_decode : atom0065 = SparsePolynomial.decodeCubic 15 atom0065Coded := by decide +kernel
theorem atom0065Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (146880 : Int) atom0065Coded) := by
  have h := atom0065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0066 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -14), ([6,7,10], -10), ([6,7,11], -2), ([6,7,12], 2), ([6,7,13], 10), ([6,7,14], 18)]
theorem atom0066_data : atom0066 = SparsePolynomial.monoTimes [6,7] 1 base08 := by decide +kernel
theorem eval_atom0066 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0066 = (quadB (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0066_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0066_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1024248 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066Coded : CoefficientMerge.Poly := [(97, -8), (322, -12), (547, -16), (772, -16), (997, -16), (1222, -16), (1447, -16), (1462, -16), (1463, -16), (1464, -14), (1465, -10), (1466, -2), (1467, 2), (1468, 10), (1469, 18)]
theorem atom0066Coded_decode : atom0066 = SparsePolynomial.decodeCubic 15 atom0066Coded := by decide +kernel
theorem atom0066Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1024248 : Int) atom0066Coded) := by
  have h := atom0066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0067 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -14), ([7,7,10], -10), ([7,7,11], -2), ([7,7,12], 2), ([7,7,13], 10), ([7,7,14], 18)]
theorem atom0067_data : atom0067 = SparsePolynomial.monoTimes [7,7] 1 base08 := by decide +kernel
theorem eval_atom0067 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0067 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0067_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0067_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1120140 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067Coded : CoefficientMerge.Poly := [(112, -8), (337, -12), (562, -16), (787, -16), (1012, -16), (1237, -16), (1462, -16), (1687, -16), (1688, -16), (1689, -14), (1690, -10), (1691, -2), (1692, 2), (1693, 10), (1694, 18)]
theorem atom0067Coded_decode : atom0067 = SparsePolynomial.decodeCubic 15 atom0067Coded := by decide +kernel
theorem atom0067Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1120140 : Int) atom0067Coded) := by
  have h := atom0067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0068 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -14), ([7,8,10], -10), ([7,8,11], -2), ([7,8,12], 2), ([7,8,13], 10), ([7,8,14], 18)]
theorem atom0068_data : atom0068 = SparsePolynomial.monoTimes [7,8] 1 base08 := by decide +kernel
theorem eval_atom0068 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0068 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0068_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0068_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1274960 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068Coded : CoefficientMerge.Poly := [(113, -8), (338, -12), (563, -16), (788, -16), (1013, -16), (1238, -16), (1463, -16), (1688, -16), (1703, -16), (1704, -14), (1705, -10), (1706, -2), (1707, 2), (1708, 10), (1709, 18)]
theorem atom0068Coded_decode : atom0068 = SparsePolynomial.decodeCubic 15 atom0068Coded := by decide +kernel
theorem atom0068Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1274960 : Int) atom0068Coded) := by
  have h := atom0068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0069 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -14), ([8,8,10], -10), ([8,8,11], -2), ([8,8,12], 2), ([8,8,13], 10), ([8,8,14], 18)]
theorem atom0069_data : atom0069 = SparsePolynomial.monoTimes [8,8] 1 base08 := by decide +kernel
theorem eval_atom0069 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0069 = (quadB (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0069_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0069_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1885680 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069Coded : CoefficientMerge.Poly := [(128, -8), (353, -12), (578, -16), (803, -16), (1028, -16), (1253, -16), (1478, -16), (1703, -16), (1928, -16), (1929, -14), (1930, -10), (1931, -2), (1932, 2), (1933, 10), (1934, 18)]
theorem atom0069Coded_decode : atom0069 = SparsePolynomial.decodeCubic 15 atom0069Coded := by decide +kernel
theorem atom0069Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1885680 : Int) atom0069Coded) := by
  have h := atom0069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0070 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -14), ([10,10,10], -10), ([10,10,11], -2), ([10,10,12], 2), ([10,10,13], 10), ([10,10,14], 18)]
theorem atom0070_data : atom0070 = SparsePolynomial.monoTimes [10,10] 1 base08 := by decide +kernel
theorem eval_atom0070 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0070 = (quadB (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0070_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0070_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1041984 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070Coded : CoefficientMerge.Poly := [(160, -8), (385, -12), (610, -16), (835, -16), (1060, -16), (1285, -16), (1510, -16), (1735, -16), (1960, -16), (2185, -14), (2410, -10), (2411, -2), (2412, 2), (2413, 10), (2414, 18)]
theorem atom0070Coded_decode : atom0070 = SparsePolynomial.decodeCubic 15 atom0070Coded := by decide +kernel
theorem atom0070Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1041984 : Int) atom0070Coded) := by
  have h := atom0070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0071 : SparsePolynomial.Poly := [([0,0,9], 1)]
theorem eval_atom0071 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0071 = ((g 0) * (g 0) * (g 9)) := by
  norm_num [atom0071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0071_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7810560 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 0) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071Coded : CoefficientMerge.Poly := [(9, 1)]
theorem atom0071Coded_decode : atom0071 = SparsePolynomial.decodeCubic 15 atom0071Coded := by decide +kernel
theorem atom0071Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (7810560 : Int) atom0071Coded) := by
  have h := atom0071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0072 : SparsePolynomial.Poly := [([0,0,10], 1)]
theorem eval_atom0072 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0072 = ((g 0) * (g 0) * (g 10)) := by
  norm_num [atom0072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0072_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5909760 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 0) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072Coded : CoefficientMerge.Poly := [(10, 1)]
theorem atom0072Coded_decode : atom0072 = SparsePolynomial.decodeCubic 15 atom0072Coded := by decide +kernel
theorem atom0072Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5909760 : Int) atom0072Coded) := by
  have h := atom0072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block000 : CoefficientMerge.Poly := [(0, -2298240), (1, -8795520), (2, -10696320), (3, -12597120), (4, -14497920), (5, -16398720), (6, -18299520), (7, -20200320), (8, -22101120), (9, -24001920), (10, -25902720), (11, -31812480), (12, -31812480), (13, -31605120), (14, -33505920), (16, -15413760), (17, -49360320), (18, -52211520), (19, -55062720), (20, -57913920), (21, -60765120), (22, -63616320), (23, -67337280), (24, -93592800), (25, -68590800), (26, -60078240), (27, -58368240), (28, -59298480), (29, -59114880), (32, -41713920), (33, -87229440), (34, -91031040), (35, -94832640), (36, -98634240), (37, -102435840), (38, -106237440), (39, -124135200), (40, -93869280), (41, -80525880), (42, -57503520), (43, -60652800), (44, -51217920), (48, -46215360), (49, -94832640), (50, -98634240), (51, -102435840), (52, -106349760), (53, -110263680), (54, -127461600), (55, -96825780), (56, -81001080), (57, -58095900), (58, -61368300), (59, -44362620), (64, -55967040), (65, -106282080), (66, -109478880), (67, -112675680), (68, -115872480), (69, -130788000), (70, -100690380), (71, -81476280), (72, -59906340), (73, -62048340), (74, -43912260), (80, -63311040), (81, -119614752), (82, -120317760), (83, -122499360), (84, -134114400), (85, -104525460), (86, -81951480), (87, -60188220), (88, -60299820), (89, -40133340), (96, -70407360), (97, -132292992), (98, -129064320), (99, -137440800), (100, -107656020), (101, -82426680), (102, -59076540), (103, -56797740), (104, -34240860), (112, -76151040), (113, -141219680), (114, -141257280), (115, -110427360), (116, -82901880), (117, -56502240), (118, -51196800), (119, -25613280), (128, -79608960), (129, -146863800), (130, -113131080), (131, -83377080), (132, -54652320), (133, -43205400), (134, -21336480), (144, -83946240), (145, -140676480), (146, -133432920), (147, -113460480), (148, -62112960), (149, -60721920), (160, -65066112), (161, -113460480), (162, -113460480), (163, -59918400), (164, -60721920), (176, -56730240), (177, -113460480), (178, -55529280), (179, -45239040), (192, -56730240), (193, -53334720), (194, -45239040), (208, 5486400), (209, 25358400), (224, 21772800), (241, -10225440), (242, -40849920), (243, -40849920), (244, -40849920), (245, -40849920), (246, -40849920), (247, -40849920), (248, -43459200), (249, -66361680), (250, -48677760), (251, -51287040), (252, -53896320), (253, -56505600), (254, -59114880), (257, -54432000), (258, -108864000), (259, -108864000), (260, -108864000), (261, -108864000), (262, -108864000), (263, -112343040), (264, -163296000), (265, -126118080), (266, -141565320), (267, -137638080), (268, -133125120), (269, -141889680), (273, -55481760), (274, -108864000), (275, -108864000), (276, -108864000), (277, -109088640), (278, -112792320), (279, -163296000), (280, -127279080), (281, -141565320), (282, -139773240), (283, -139308120), (284, -138843000), (289, -64406880), (290, -116556480), (291, -115346880), (292, -114137280), (293, -116406720), (294, -163296000), (295, -130256280), (296, -141565320), (297, -144344520), (298, -145420200), (299, -146495880), (305, -69720480), (306, -126536832), (307, -121818240), (308, -122057280), (309, -163296000), (310, -133174440), (311, -141565320), (312, -145858680), (313, -146675160), (314, -147491640), (321, -74662560), (322, -134068512), (323, -127584000), (324, -163296000), (325, -134683560), (326, -141565320), (327, -144585720), (328, -144423000), (329, -144260280), (337, -77575680), (338, -139191680), (339, -164276160), (340, -135474240), (341, -141565320), (342, -140387520), (343, -137973120), (344, -135558720), (353, -80539200), (354, -170575920), (355, -136999440), (356, -140695560), (357, -136333440), (358, -124567920), (359, -131644800), (369, -108864000), (370, -171923040), (371, -195997320), (372, -191291040), (373, -115927200), (374, -123962040), (385, -71249328), (386, -144495360), (387, -157215240), (388, -101611800), (389, -97877520), (401, -94376880), (402, -148419360), (403, -90845280), (404, -89453880), (417, -53847720), (418, -48160800), (419, -43835760), (433, 8829000), (434, 32576400), (449, 30031560), (482, -27216000), (483, -81648000), (484, -81648000), (485, -81648000), (486, -81648000), (487, -81648000), (488, -81648000), (489, -108864000), (490, -81648000), (491, -94376880), (492, -81648000), (493, -74701440), (494, -90089280), (498, -83047680), (499, -163296000), (500, -163296000), (501, -163296000), (502, -163745280), (503, -164194560), (504, -217728000), (505, -165618000), (506, -188753760), (507, -167566320), (508, -161768880), (509, -178305840), (514, -94947840), (515, -178680960), (516, -176261760), (517, -173842560), (518, -171423360), (519, -217728000), (520, -171572400), (521, -188753760), (522, -176708880), (523, -173993040), (524, -193611600), (530, -102032640), (531, -195684480), (532, -189204480), (533, -182724480), (534, -217728000), (535, -177408720), (536, -188753760), (537, -179737200), (538, -176502960), (539, -195603120), (546, -108622080), (547, -205511040), (548, -193777920), (549, -217728000), (550, -180426960), (551, -188753760), (552, -177191280), (553, -171998640), (554, -189140400), (562, -112506240), (563, -206793600), (564, -219688320), (565, -182008320), (566, -188753760), (567, -168794880), (568, -159098880), (569, -171737280), (578, -111818880), (579, -228808800), (580, -183319200), (581, -188753760), (582, -163296000), (583, -136637280), (584, -171737280), (594, -136080000), (595, -217728000), (596, -243185760), (597, -217728000), (598, -118998720), (599, -170682120), (610, -98319744), (611, -195997320), (612, -190512000), (613, -108864000), (614, -114139800), (626, -114349320), (627, -168781320), (628, -84242160), (629, -95432040), (642, -54432000), (643, -39229920), (644, -53376840), (658, 20269440), (659, 28078920), (674, 9496440), (723, -28615680), (724, -83047680), (725, -83047680), (726, -83047680), (727, -83496960), (728, -83946240), (729, -110088720), (730, -84844800), (731, -94551840), (732, -85743360), (733, -86192640), (734, -86641920), (739, -94947840), (740, -178680960), (741, -176261760), (742, -174291840), (743, -172321920), (744, -217728000), (745, -173894400), (746, -188753760), (747, -180979200), (748, -186359040), (749, -191738880), (755, -102032640), (756, -195684480), (757, -189653760), (758, -183623040), (759, -217728000), (760, -179730720), (761, -188753760), (762, -184007520), (763, -188868960), (764, -193730400), (771, -108622080), (772, -205960320), (773, -194676480), (774, -217728000), (775, -182748960), (776, -188753760), (777, -181461600), (778, -184364640), (779, -187267680), (787, -112955520), (788, -208141440), (789, -219912960), (790, -184330320), (791, -188529120), (792, -172728240), (793, -171015600), (794, -169359120), (803, -112717440), (804, -229258080), (805, -185641200), (806, -188304480), (807, -166892400), (808, -148104720), (809, -168853680), (819, -136080000), (820, -218889000), (821, -243185760), (822, -219863160), (823, -125181720), (824, -166580280), (835, -98319744), (836, -194836320), (837, -188770500), (838, -106542000), (839, -106251750), (851, -114349320), (852, -166646160), (853, -78059160), (854, -91092600), (867, -51229260), (868, -25685100), (869, -44701470), (883, 32635440), (884, 43283430), (899, 7389630), (964, -40515840), (965, -110332800), (966, -107913600), (967, -105494400), (968, -103075200), (969, -120501360), (970, -98236800), (971, -96039360), (972, -93398400), (973, -90979200), (974, -88560000), (980, -117417600), (981, -224035200), (982, -215136000), (983, -206236800), (984, -225420480), (985, -185685120), (986, -181061280), (987, -181611360), (988, -185708160), (989, -191728080), (996, -121587840), (997, -229023360), (998, -214871040), (999, -224210880), (1000, -188703360), (1001, -182270880), (1002, -180879840), (1003, -183623040), (1004, -187986960), (1012, -123052800), (1013, -225467520), (1014, -224961600), (1015, -190284720), (1016, -183480480), (1017, -174297840), (1018, -173142480), (1019, -173305440), (1028, -119946240), (1029, -232872480), (1030, -191595600), (1031, -184690080), (1032, -170613360), (1033, -153100080), (1034, -176027040), (1044, -136080000), (1045, -221866200), (1046, -243185760), (1047, -224434440), (1048, -131293800), (1049, -174233160), (1060, -98319744), (1061, -191859120), (1062, -184304700), (1063, -100587600), (1064, -99553050), (1076, -114349320), (1077, -162074880), (1078, -71947080), (1079, -83439720), (1092, -44372340), (1093, -7374420), (1094, -22936770), (1108, 44859600), (1109, 72341370), (1124, 24608610), (1205, -47600640), (1206, -134421120), (1207, -127941120), (1208, -121461120), (1209, -126700560), (1210, -108501120), (1211, -102021120), (1212, -95541120), (1213, -89061120), (1214, -82581120), (1221, -141010560), (1222, -263808000), (1223, -245594880), (1224, -236140128), (1225, -198236160), (1226, -178122240), (1227, -173037600), (1228, -168928128), (1229, -168127920), (1237, -138414720), (1238, -252130560), (1239, -232642560), (1240, -196121040), (1241, -175799520), (1242, -165804720), (1243, -160290480), (1244, -158014800), (1253, -131247360), (1254, -238523040), (1255, -197431920), (1256, -179039520), (1257, -165165840), (1258, -144308880), (1259, -165304800), (1269, -136080000), (1270, -224784360), (1271, -243185760), (1272, -225948600), (1273, -132548760), (1274, -175228920), (1285, -98319744), (1286, -188940960), (1287, -179927460), (1288, -94751280), (1289, -92987190), (1301, -114349320), (1302, -160560720), (1303, -70692120), (1304, -82443960), (1317, -42101100), (1318, -2463660), (1319, -18036270), (1333, 47369520), (1334, 77156550), (1349, 26849070), (1446, -54190080), (1447, -150837120), (1448, -139104000), (1449, -132466320), (1450, -115637760), (1451, -103904640), (1452, -92171520), (1453, -80438400), (1454, -68705280), (1462, -154721280), (1463, -279490560), (1464, -246941328), (1465, -209381760), (1466, -177888720), (1467, -161271360), (1468, -145625088), (1469, -133207200), (1478, -142300800), (1479, -244049760), (1480, -200450160), (1481, -173512800), (1482, -154329840), (1483, -128751120), (1484, -146406960), (1494, -136080000), (1495, -226293480), (1496, -243185760), (1497, -224675640), (1498, -130296600), (1499, -171997560), (1510, -98319744), (1511, -187431840), (1512, -177663780), (1513, -91733040), (1514, -89591670), (1526, -114349320), (1527, -161833680), (1528, -72944280), (1529, -85675320), (1542, -44010540), (1543, -8387820), (1544, -25747470), (1558, 42865200), (1559, 65626470), (1574, 19578510), (1687, -58074240), (1688, -156003840), (1689, -137825280), (1690, -119646720), (1691, -101468160), (1692, -83289600), (1693, -65111040), (1694, -46932480), (1703, -155316480), (1704, -260167680), (1705, -214781120), (1706, -179754560), (1707, -148921280), (1708, -110485440), (1709, -114361200), (1719, -137060160), (1720, -227084160), (1721, -242205600), (1722, -219007200), (1723, -121886400), (1724, -161090640), (1735, -98319744), (1736, -186641160), (1737, -176477760), (1738, -90151680), (1739, -87812640), (1751, -114349320), (1752, -166031880), (1753, -79394160), (1754, -94376880), (1767, -50307840), (1768, -26459040), (1769, -48245760), (1783, 29965440), (1784, 33711120), (1928, -57386880), (1929, -146344320), (1930, -120528000), (1931, -98148240), (1932, -77876640), (1933, -43079040), (1934, -47705760), (1944, -141620400), (1945, -227739600), (1946, -237645360), (1947, -209417400), (1948, -101535120), (1949, -150830100), (1960, -98319744), (1961, -185985720), (1962, -175494600), (1963, -88840800), (1964, -86337900), (1976, -114349320), (1977, -168781320), (1978, -90624960), (1979, -94376880), (1992, -54432000), (1993, -48804120), (1994, -54432000), (2008, 7503840), (2009, 8441820), (2169, -54432000), (2170, -136080000), (2171, -148808880), (2172, -136080000), (2173, -54432000), (2174, -81648000), (2185, -123451776), (2186, -250429320), (2187, -244944000), (2188, -108864000), (2189, -108864000), (2201, -141565320), (2202, -223213320), (2203, -94376880), (2204, -14487120), (2217, -81648000), (2218, -54432000), (2219, 54432000), (2234, 108864000), (2249, 108864000), (2410, -37635840), (2411, -103704408), (2412, -106780032), (2413, -44012160), (2414, -35676288), (2426, -121592880), (2427, -203240880), (2428, -94376880), (2429, -14487120), (2442, -81648000), (2443, -54432000), (2444, 54432000), (2459, 108864000), (2474, 108864000), (2651, -47188440), (2652, -101620440), (2653, -47188440), (2654, 32701320), (2667, -81648000), (2668, -54432000), (2669, 134321760), (2684, 188753760), (2699, 188753760), (2892, -27216000), (2893, -27216000), (2894, 81648000), (2909, 217728000), (2924, 217728000), (3134, 108864000), (3149, 217728000), (3374, 108864000)]
theorem block000_data : block000 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3621780 : Int) atom0000Coded) (CoefficientMerge.scale (96912 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217440 : Int) atom0002Coded) (CoefficientMerge.scale (1078380 : Int) atom0003Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (97380 : Int) atom0004Coded) (CoefficientMerge.scale (882900 : Int) atom0005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1376640 : Int) atom0006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (598590 : Int) atom0007Coded) (CoefficientMerge.scale (1274040 : Int) atom0008Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (369648 : Int) atom0009Coded) (CoefficientMerge.scale (1539000 : Int) atom0010Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (808500 : Int) atom0011Coded) (CoefficientMerge.scale (9986220 : Int) atom0012Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2298240 : Int) atom0013Coded) (CoefficientMerge.scale (3144960 : Int) atom0014Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1266840 : Int) atom0015Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28080 : Int) atom0016Coded) (CoefficientMerge.scale (56160 : Int) atom0017Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145125 : Int) atom0018Coded) (CoefficientMerge.scale (266895 : Int) atom0019Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2039715 : Int) atom0020Coded) (CoefficientMerge.scale (410535 : Int) atom0021Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (961560 : Int) atom0022Coded) (CoefficientMerge.scale (810360 : Int) atom0023Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (659160 : Int) atom0024Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (507960 : Int) atom0025Coded) (CoefficientMerge.scale (517275 : Int) atom0026Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (838305 : Int) atom0027Coded) (CoefficientMerge.scale (2803725 : Int) atom0028Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1367145 : Int) atom0029Coded) (CoefficientMerge.scale (1557720 : Int) atom0030Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1619280 : Int) atom0031Coded) (CoefficientMerge.scale (1214280 : Int) atom0032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (882045 : Int) atom0033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027575 : Int) atom0034Coded) (CoefficientMerge.scale (2960595 : Int) atom0035Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1491615 : Int) atom0036Coded) (CoefficientMerge.scale (1614192 : Int) atom0037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1905120 : Int) atom0038Coded) (CoefficientMerge.scale (1070685 : Int) atom0039Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (868455 : Int) atom0040Coded) (CoefficientMerge.scale (2679075 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1087695 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1443640 : Int) atom0043Coded) (CoefficientMerge.scale (122520 : Int) atom0044Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1169520 : Int) atom0045Coded) (CoefficientMerge.scale (343680 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1872840 : Int) atom0047Coded) (CoefficientMerge.scale (692550 : Int) atom0048Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1251450 : Int) atom0049Coded) (CoefficientMerge.scale (468990 : Int) atom0050Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524880 : Int) atom0051Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (762480 : Int) atom0052Coded) (CoefficientMerge.scale (1000080 : Int) atom0053Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1237680 : Int) atom0054Coded) (CoefficientMerge.scale (1475280 : Int) atom0055Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1712880 : Int) atom0056Coded) (CoefficientMerge.scale (1950480 : Int) atom0057Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2188080 : Int) atom0058Coded) (CoefficientMerge.scale (548640 : Int) atom0059Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253530 : Int) atom0060Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291780 : Int) atom0061Coded) (CoefficientMerge.scale (527580 : Int) atom0062Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87480 : Int) atom0063Coded) (CoefficientMerge.scale (831240 : Int) atom0064Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146880 : Int) atom0065Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1024248 : Int) atom0066Coded) (CoefficientMerge.scale (1120140 : Int) atom0067Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1274960 : Int) atom0068Coded) (CoefficientMerge.scale (1885680 : Int) atom0069Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041984 : Int) atom0070Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7810560 : Int) atom0071Coded) (CoefficientMerge.scale (5909760 : Int) atom0072Coded)))))))) := by decide +kernel
theorem block000_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block000 := by
  rw [block000_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000Coded_nonneg g hg hA hB) (atom0001Coded_nonneg g hg hA hB)) (add_nonneg (atom0002Coded_nonneg g hg hA hB) (atom0003Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0004Coded_nonneg g hg hA hB) (atom0005Coded_nonneg g hg hA hB)) (add_nonneg (atom0006Coded_nonneg g hg hA hB) (add_nonneg (atom0007Coded_nonneg g hg hA hB) (atom0008Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0009Coded_nonneg g hg hA hB) (atom0010Coded_nonneg g hg hA hB)) (add_nonneg (atom0011Coded_nonneg g hg hA hB) (atom0012Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0013Coded_nonneg g hg hA hB) (atom0014Coded_nonneg g hg hA hB)) (add_nonneg (atom0015Coded_nonneg g hg hA hB) (add_nonneg (atom0016Coded_nonneg g hg hA hB) (atom0017Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0018Coded_nonneg g hg hA hB) (atom0019Coded_nonneg g hg hA hB)) (add_nonneg (atom0020Coded_nonneg g hg hA hB) (atom0021Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0022Coded_nonneg g hg hA hB) (atom0023Coded_nonneg g hg hA hB)) (add_nonneg (atom0024Coded_nonneg g hg hA hB) (add_nonneg (atom0025Coded_nonneg g hg hA hB) (atom0026Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0027Coded_nonneg g hg hA hB) (atom0028Coded_nonneg g hg hA hB)) (add_nonneg (atom0029Coded_nonneg g hg hA hB) (atom0030Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0031Coded_nonneg g hg hA hB) (atom0032Coded_nonneg g hg hA hB)) (add_nonneg (atom0033Coded_nonneg g hg hA hB) (add_nonneg (atom0034Coded_nonneg g hg hA hB) (atom0035Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0036Coded_nonneg g hg hA hB) (atom0037Coded_nonneg g hg hA hB)) (add_nonneg (atom0038Coded_nonneg g hg hA hB) (atom0039Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0040Coded_nonneg g hg hA hB) (atom0041Coded_nonneg g hg hA hB)) (add_nonneg (atom0042Coded_nonneg g hg hA hB) (add_nonneg (atom0043Coded_nonneg g hg hA hB) (atom0044Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0045Coded_nonneg g hg hA hB) (atom0046Coded_nonneg g hg hA hB)) (add_nonneg (atom0047Coded_nonneg g hg hA hB) (atom0048Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0049Coded_nonneg g hg hA hB) (atom0050Coded_nonneg g hg hA hB)) (add_nonneg (atom0051Coded_nonneg g hg hA hB) (add_nonneg (atom0052Coded_nonneg g hg hA hB) (atom0053Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0054Coded_nonneg g hg hA hB) (atom0055Coded_nonneg g hg hA hB)) (add_nonneg (atom0056Coded_nonneg g hg hA hB) (atom0057Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0058Coded_nonneg g hg hA hB) (atom0059Coded_nonneg g hg hA hB)) (add_nonneg (atom0060Coded_nonneg g hg hA hB) (add_nonneg (atom0061Coded_nonneg g hg hA hB) (atom0062Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0063Coded_nonneg g hg hA hB) (atom0064Coded_nonneg g hg hA hB)) (add_nonneg (atom0065Coded_nonneg g hg hA hB) (add_nonneg (atom0066Coded_nonneg g hg hA hB) (atom0067Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0068Coded_nonneg g hg hA hB) (atom0069Coded_nonneg g hg hA hB)) (add_nonneg (atom0070Coded_nonneg g hg hA hB) (add_nonneg (atom0071Coded_nonneg g hg hA hB) (atom0072Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
