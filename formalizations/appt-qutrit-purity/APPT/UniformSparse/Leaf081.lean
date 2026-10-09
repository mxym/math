import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0985 : CoefficientMerge.Poly :=
  [(1392896, 1)]
noncomputable def atom0985 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0985_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0985 g t z = CoefficientMerge.eval (monomial g t z) coeff0985 := by
  norm_num [atom0985, coeff0985, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0985_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0985 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0985]
  positivity
theorem weighted0985_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9103701234649733225434262352100396650844303866109756554219129116686215053607487156903027001432289076298273861633648516821140727971299159040 : Int) coeff0985) := by
  rw [CoefficientMerge.eval_scale, ← atom0985_identity]
  exact mul_nonneg (by norm_num) (atom0985_nonneg g t z hg hA hB ht hz hw)

def coeff0986 : CoefficientMerge.Poly :=
  [(655616, 1)]
noncomputable def atom0986 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (t) ^ 2)
theorem atom0986_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0986 g t z = CoefficientMerge.eval (monomial g t z) coeff0986 := by
  norm_num [atom0986, coeff0986, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0986_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0986 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0986]
  positivity
theorem weighted0986_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2429879450461656145154177679459008557556461087126481916320275749759817925635715262342689618193200220415033568600774534021721570223585689600 : Int) coeff0986) := by
  rw [CoefficientMerge.eval_scale, ← atom0986_identity]
  exact mul_nonneg (by norm_num) (atom0986_nonneg g t z hg hA hB ht hz hw)

def coeff0987 : CoefficientMerge.Poly :=
  [(1442048, 1)]
noncomputable def atom0987 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0987_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0987 g t z = CoefficientMerge.eval (monomial g t z) coeff0987 := by
  norm_num [atom0987, coeff0987, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0987_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0987 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0987]
  positivity
theorem weighted0987_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4445432016644230595927229453142723490070013470441782688135377396880364793875879764923217944049419825246743634489782533637391512520681541120 : Int) coeff0987) := by
  rw [CoefficientMerge.eval_scale, ← atom0987_identity]
  exact mul_nonneg (by norm_num) (atom0987_nonneg g t z hg hA hB ht hz hw)

def coeff0988 : CoefficientMerge.Poly :=
  [(2101760, 1)]
noncomputable def atom0988 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0988_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0988 g t z = CoefficientMerge.eval (monomial g t z) coeff0988 := by
  norm_num [atom0988, coeff0988, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0988_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0988 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0988]
  positivity
theorem weighted0988_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1332993392962517357922621007945140965994666511473852351544029322734587557266193415144997294357294336998678697700979970325896795882590586240 : Int) coeff0988) := by
  rw [CoefficientMerge.eval_scale, ← atom0988_identity]
  exact mul_nonneg (by norm_num) (atom0988_nonneg g t z hg hA hB ht hz hw)

def coeff0989 : CoefficientMerge.Poly :=
  [(2114048, 1)]
noncomputable def atom0989 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0989_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0989 g t z = CoefficientMerge.eval (monomial g t z) coeff0989 := by
  norm_num [atom0989, coeff0989, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0989_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0989 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0989]
  positivity
theorem weighted0989_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1499300328784824838699850568299820858630178440192835950257786741804628541785303166148754587574449494498926594845218786761599163061927873920 : Int) coeff0989) := by
  rw [CoefficientMerge.eval_scale, ← atom0989_identity]
  exact mul_nonneg (by norm_num) (atom0989_nonneg g t z hg hA hB ht hz hw)

def coeff0990 : CoefficientMerge.Poly :=
  [(2163200, 1)]
noncomputable def atom0990 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0990_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0990 g t z = CoefficientMerge.eval (monomial g t z) coeff0990 := by
  norm_num [atom0990, coeff0990, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0990_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0990 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0990]
  positivity
theorem weighted0990_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2748900933894840434680404380273940654140990250649443336409897382967253068817014135552846282151421735895075391107093859973901952112910602880 : Int) coeff0990) := by
  rw [CoefficientMerge.eval_scale, ← atom0990_identity]
  exact mul_nonneg (by norm_num) (atom0990_nonneg g t z hg hA hB ht hz hw)

def coeff0991 : CoefficientMerge.Poly :=
  [(2099456, 1)]
noncomputable def atom0991 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 2 * (z) ^ 2)
theorem atom0991_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0991 g t z = CoefficientMerge.eval (monomial g t z) coeff0991 := by
  norm_num [atom0991, coeff0991, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0991_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0991 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0991]
  positivity
theorem weighted0991_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (152835615908026497881621560880867247202755380140433373610254673086728859596891499888124403664205240533746623637878179687493946455306959360 : Int) coeff0991) := by
  rw [CoefficientMerge.eval_scale, ← atom0991_identity]
  exact mul_nonneg (by norm_num) (atom0991_nonneg g t z hg hA hB ht hz hw)

def coeff0992 : CoefficientMerge.Poly :=
  [(2102528, 1)]
noncomputable def atom0992 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0992_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0992 g t z = CoefficientMerge.eval (monomial g t z) coeff0992 := by
  norm_num [atom0992, coeff0992, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0992_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0992 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0992]
  positivity
theorem weighted0992_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1726247794830473523757395120059353557032920445998607640412579302033842785703362233621951857502476874268877057141937805983378831924739399680 : Int) coeff0992) := by
  rw [CoefficientMerge.eval_scale, ← atom0992_identity]
  exact mul_nonneg (by norm_num) (atom0992_nonneg g t z hg hA hB ht hz hw)

def coeff0993 : CoefficientMerge.Poly :=
  [(2114816, 1)]
noncomputable def atom0993 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0993_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0993 g t z = CoefficientMerge.eval (monomial g t z) coeff0993 := by
  norm_num [atom0993, coeff0993, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0993_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0993 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0993]
  positivity
theorem weighted0993_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2271898145761252161510709394732759264382074098266786980536664750054723914244025043261902877167855025142152052681998924415727384550393466880 : Int) coeff0993) := by
  rw [CoefficientMerge.eval_scale, ← atom0993_identity]
  exact mul_nonneg (by norm_num) (atom0993_nonneg g t z hg hA hB ht hz hw)

def coeff0994 : CoefficientMerge.Poly :=
  [(2163968, 1)]
noncomputable def atom0994 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0994_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0994 g t z = CoefficientMerge.eval (monomial g t z) coeff0994 := by
  norm_num [atom0994, coeff0994, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0994_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0994 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0994]
  positivity
theorem weighted0994_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2625666341110222863734783643788173354107322936720753300702299452646778811530479716896273816004605759529832210478970874549473440042032850380 : Int) coeff0994) := by
  rw [CoefficientMerge.eval_scale, ← atom0994_identity]
  exact mul_nonneg (by norm_num) (atom0994_nonneg g t z hg hA hB ht hz hw)

def coeff0995 : CoefficientMerge.Poly :=
  [(2105600, 1)]
noncomputable def atom0995 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom0995_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0995 g t z = CoefficientMerge.eval (monomial g t z) coeff0995 := by
  norm_num [atom0995, coeff0995, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0995_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0995 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0995]
  positivity
theorem weighted0995_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1059809901624950721660238092880428534910559160231468086974128102577037119467174392596359749112589071790205412701296334451080818066057029120 : Int) coeff0995) := by
  rw [CoefficientMerge.eval_scale, ← atom0995_identity]
  exact mul_nonneg (by norm_num) (atom0995_nonneg g t z hg hA hB ht hz hw)

def coeff0996 : CoefficientMerge.Poly :=
  [(2117888, 1)]
noncomputable def atom0996 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0996_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0996 g t z = CoefficientMerge.eval (monomial g t z) coeff0996 := by
  norm_num [atom0996, coeff0996, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0996_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0996 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0996]
  positivity
theorem weighted0996_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2788375903828471119202297272418222291736429761910447673888720830233646287748742740587294623311424772888377221740524438460536734806073281440 : Int) coeff0996) := by
  rw [CoefficientMerge.eval_scale, ← atom0996_identity]
  exact mul_nonneg (by norm_num) (atom0996_nonneg g t z hg hA hB ht hz hw)

def coeff0997 : CoefficientMerge.Poly :=
  [(2167040, 1)]
noncomputable def atom0997 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0997_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0997 g t z = CoefficientMerge.eval (monomial g t z) coeff0997 := by
  norm_num [atom0997, coeff0997, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0997_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0997 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0997]
  positivity
theorem weighted0997_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3160565235143872465637871556386549866428736842128621075702625923717211928086772944942226313377318904762441776291357137729732476208979197440 : Int) coeff0997) := by
  rw [CoefficientMerge.eval_scale, ← atom0997_identity]
  exact mul_nonneg (by norm_num) (atom0997_nonneg g t z hg hA hB ht hz hw)

def coeff0998 : CoefficientMerge.Poly :=
  [(2130176, 1)]
noncomputable def atom0998 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (z) ^ 2)
theorem atom0998_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0998 g t z = CoefficientMerge.eval (monomial g t z) coeff0998 := by
  norm_num [atom0998, coeff0998, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0998_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0998 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0998]
  positivity
theorem weighted0998_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1822596096397065550040727810738319265949312008476728275174726731862368434458571120521315116562042375211891568963715620025810180684725701120 : Int) coeff0998) := by
  rw [CoefficientMerge.eval_scale, ← atom0998_identity]
  exact mul_nonneg (by norm_num) (atom0998_nonneg g t z hg hA hB ht hz hw)

def coeff0999 : CoefficientMerge.Poly :=
  [(2179328, 1)]
noncomputable def atom0999 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0999_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0999 g t z = CoefficientMerge.eval (monomial g t z) coeff0999 := by
  norm_num [atom0999, coeff0999, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0999_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0999 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0999]
  positivity
theorem weighted0999_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4643332926721809772101174896761599859010028098976064593807835214987546580266662203082121668744190754920042743569096300545552135898008202240 : Int) coeff0999) := by
  rw [CoefficientMerge.eval_scale, ← atom0999_identity]
  exact mul_nonneg (by norm_num) (atom0999_nonneg g t z hg hA hB ht hz hw)

def coeff1000 : CoefficientMerge.Poly :=
  [(2228480, 1)]
noncomputable def atom1000 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (z) ^ 2)
theorem atom1000_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1000 g t z = CoefficientMerge.eval (monomial g t z) coeff1000 := by
  norm_num [atom1000, coeff1000, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1000_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1000 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1000]
  positivity
theorem weighted1000_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2138410272056696746341455262182660444376707520304531726992522056877851809754948890663890426622106090528886152919221814517704882394554846720 : Int) coeff1000) := by
  rw [CoefficientMerge.eval_scale, ← atom1000_identity]
  exact mul_nonneg (by norm_num) (atom1000_nonneg g t z hg hA hB ht hz hw)

def coeff1001 : CoefficientMerge.Poly :=
  [(82944, 1)]
noncomputable def atom1001 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1)
theorem atom1001_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1001 g t z = CoefficientMerge.eval (monomial g t z) coeff1001 := by
  norm_num [atom1001, coeff1001, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1001_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1001 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1001]
  positivity
theorem weighted1001_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1698669766550322454074290858029274709850124617822520836656456707473739238588259002550914904810715019148512454807995933585378168670161715200 : Int) coeff1001) := by
  rw [CoefficientMerge.eval_scale, ← atom1001_identity]
  exact mul_nonneg (by norm_num) (atom1001_nonneg g t z hg hA hB ht hz hw)

def coeff1002 : CoefficientMerge.Poly :=
  [(345088, 1)]
noncomputable def atom1002 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom1002_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1002 g t z = CoefficientMerge.eval (monomial g t z) coeff1002 := by
  norm_num [atom1002, coeff1002, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1002_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1002 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1002]
  positivity
theorem weighted1002_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (967878165216936600726420694828883715799231265092950030758989766898955952936607390620075176052548795943486506034471361953390820596828160000 : Int) coeff1002) := by
  rw [CoefficientMerge.eval_scale, ← atom1002_identity]
  exact mul_nonneg (by norm_num) (atom1002_nonneg g t z hg hA hB ht hz hw)

def coeff1003 : CoefficientMerge.Poly :=
  [(1131520, 1)]
noncomputable def atom1003 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom1003_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1003 g t z = CoefficientMerge.eval (monomial g t z) coeff1003 := by
  norm_num [atom1003, coeff1003, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1003_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1003 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1003]
  positivity
theorem weighted1003_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6522468440121302593635755758510819083746190345766796256563770952725253642978339467999027188096950814731847064894010965247561999581420131840 : Int) coeff1003) := by
  rw [CoefficientMerge.eval_scale, ← atom1003_identity]
  exact mul_nonneg (by norm_num) (atom1003_nonneg g t z hg hA hB ht hz hw)

def coeff1004 : CoefficientMerge.Poly :=
  [(527360, 1)]
noncomputable def atom1004 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (t) ^ 2)
theorem atom1004_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1004 g t z = CoefficientMerge.eval (monomial g t z) coeff1004 := by
  norm_num [atom1004, coeff1004, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1004_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1004 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1004]
  positivity
theorem weighted1004_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (206814522901306098250289911328069206338206030585868476217610018369253034044425583144246988978760725899298117463496301303341356628285184000 : Int) coeff1004) := by
  rw [CoefficientMerge.eval_scale, ← atom1004_identity]
  exact mul_nonneg (by norm_num) (atom1004_nonneg g t z hg hA hB ht hz hw)

def sparseBlock081 : CoefficientMerge.Poly :=
  [(82944, 1698669766550322454074290858029274709850124617822520836656456707473739238588259002550914904810715019148512454807995933585378168670161715200), (345088, 967878165216936600726420694828883715799231265092950030758989766898955952936607390620075176052548795943486506034471361953390820596828160000), (527360, 206814522901306098250289911328069206338206030585868476217610018369253034044425583144246988978760725899298117463496301303341356628285184000), (655616, 2429879450461656145154177679459008557556461087126481916320275749759817925635715262342689618193200220415033568600774534021721570223585689600), (1131520, 6522468440121302593635755758510819083746190345766796256563770952725253642978339467999027188096950814731847064894010965247561999581420131840), (1392896, 9103701234649733225434262352100396650844303866109756554219129116686215053607487156903027001432289076298273861633648516821140727971299159040), (1442048, 4445432016644230595927229453142723490070013470441782688135377396880364793875879764923217944049419825246743634489782533637391512520681541120), (2099456, 152835615908026497881621560880867247202755380140433373610254673086728859596891499888124403664205240533746623637878179687493946455306959360), (2101760, 1332993392962517357922621007945140965994666511473852351544029322734587557266193415144997294357294336998678697700979970325896795882590586240), (2102528, 1726247794830473523757395120059353557032920445998607640412579302033842785703362233621951857502476874268877057141937805983378831924739399680), (2105600, 1059809901624950721660238092880428534910559160231468086974128102577037119467174392596359749112589071790205412701296334451080818066057029120), (2114048, 1499300328784824838699850568299820858630178440192835950257786741804628541785303166148754587574449494498926594845218786761599163061927873920), (2114816, 2271898145761252161510709394732759264382074098266786980536664750054723914244025043261902877167855025142152052681998924415727384550393466880), (2117888, 2788375903828471119202297272418222291736429761910447673888720830233646287748742740587294623311424772888377221740524438460536734806073281440), (2130176, 1822596096397065550040727810738319265949312008476728275174726731862368434458571120521315116562042375211891568963715620025810180684725701120), (2163200, 2748900933894840434680404380273940654140990250649443336409897382967253068817014135552846282151421735895075391107093859973901952112910602880), (2163968, 2625666341110222863734783643788173354107322936720753300702299452646778811530479716896273816004605759529832210478970874549473440042032850380), (2167040, 3160565235143872465637871556386549866428736842128621075702625923717211928086772944942226313377318904762441776291357137729732476208979197440), (2179328, 4643332926721809772101174896761599859010028098976064593807835214987546580266662203082121668744190754920042743569096300545552135898008202240), (2228480, 2138410272056696746341455262182660444376707520304531726992522056877851809754948890663890426622106090528886152919221814517704882394554846720)]
theorem sparseBlock081_data : sparseBlock081 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (9103701234649733225434262352100396650844303866109756554219129116686215053607487156903027001432289076298273861633648516821140727971299159040 : Int) coeff0985) (CoefficientMerge.scale (2429879450461656145154177679459008557556461087126481916320275749759817925635715262342689618193200220415033568600774534021721570223585689600 : Int) coeff0986)) (CoefficientMerge.merge (CoefficientMerge.scale (4445432016644230595927229453142723490070013470441782688135377396880364793875879764923217944049419825246743634489782533637391512520681541120 : Int) coeff0987) (CoefficientMerge.merge (CoefficientMerge.scale (1332993392962517357922621007945140965994666511473852351544029322734587557266193415144997294357294336998678697700979970325896795882590586240 : Int) coeff0988) (CoefficientMerge.scale (1499300328784824838699850568299820858630178440192835950257786741804628541785303166148754587574449494498926594845218786761599163061927873920 : Int) coeff0989)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2748900933894840434680404380273940654140990250649443336409897382967253068817014135552846282151421735895075391107093859973901952112910602880 : Int) coeff0990) (CoefficientMerge.scale (152835615908026497881621560880867247202755380140433373610254673086728859596891499888124403664205240533746623637878179687493946455306959360 : Int) coeff0991)) (CoefficientMerge.merge (CoefficientMerge.scale (1726247794830473523757395120059353557032920445998607640412579302033842785703362233621951857502476874268877057141937805983378831924739399680 : Int) coeff0992) (CoefficientMerge.merge (CoefficientMerge.scale (2271898145761252161510709394732759264382074098266786980536664750054723914244025043261902877167855025142152052681998924415727384550393466880 : Int) coeff0993) (CoefficientMerge.scale (2625666341110222863734783643788173354107322936720753300702299452646778811530479716896273816004605759529832210478970874549473440042032850380 : Int) coeff0994))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1059809901624950721660238092880428534910559160231468086974128102577037119467174392596359749112589071790205412701296334451080818066057029120 : Int) coeff0995) (CoefficientMerge.scale (2788375903828471119202297272418222291736429761910447673888720830233646287748742740587294623311424772888377221740524438460536734806073281440 : Int) coeff0996)) (CoefficientMerge.merge (CoefficientMerge.scale (3160565235143872465637871556386549866428736842128621075702625923717211928086772944942226313377318904762441776291357137729732476208979197440 : Int) coeff0997) (CoefficientMerge.merge (CoefficientMerge.scale (1822596096397065550040727810738319265949312008476728275174726731862368434458571120521315116562042375211891568963715620025810180684725701120 : Int) coeff0998) (CoefficientMerge.scale (4643332926721809772101174896761599859010028098976064593807835214987546580266662203082121668744190754920042743569096300545552135898008202240 : Int) coeff0999)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2138410272056696746341455262182660444376707520304531726992522056877851809754948890663890426622106090528886152919221814517704882394554846720 : Int) coeff1000) (CoefficientMerge.scale (1698669766550322454074290858029274709850124617822520836656456707473739238588259002550914904810715019148512454807995933585378168670161715200 : Int) coeff1001)) (CoefficientMerge.merge (CoefficientMerge.scale (967878165216936600726420694828883715799231265092950030758989766898955952936607390620075176052548795943486506034471361953390820596828160000 : Int) coeff1002) (CoefficientMerge.merge (CoefficientMerge.scale (6522468440121302593635755758510819083746190345766796256563770952725253642978339467999027188096950814731847064894010965247561999581420131840 : Int) coeff1003) (CoefficientMerge.scale (206814522901306098250289911328069206338206030585868476217610018369253034044425583144246988978760725899298117463496301303341356628285184000 : Int) coeff1004)))))) := by decide +kernel
theorem sparseBlock081_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock081 := by
  rw [sparseBlock081_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0985_nonneg g t z hg hA hB ht hz hw) (weighted0986_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0987_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0988_nonneg g t z hg hA hB ht hz hw) (weighted0989_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0990_nonneg g t z hg hA hB ht hz hw) (weighted0991_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0992_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0993_nonneg g t z hg hA hB ht hz hw) (weighted0994_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0995_nonneg g t z hg hA hB ht hz hw) (weighted0996_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0997_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0998_nonneg g t z hg hA hB ht hz hw) (weighted0999_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1000_nonneg g t z hg hA hB ht hz hw) (weighted1001_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1002_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1003_nonneg g t z hg hA hB ht hz hw) (weighted1004_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
