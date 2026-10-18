import RationalGateInterface.Library
import RationalGateProvider.CircleDensity
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.DenseEmbedding

open CircuitRecursion Matrix
open scoped ComplexConjugate
namespace RationalGateUniversality

set_option maxHeartbeats 1000000

def zTorus (z : Circle) : SU2 :=
  quaternionSU2 (z : ℂ) 0 (by simp)

def xTorus (z : Circle) : SU2 :=
  quaternionSU2 ((z : ℂ).re : ℂ) (Complex.I * ((z : ℂ).im : ℂ)) (by
    have h := Circle.normSq_coe z
    simpa [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] using h)

theorem ext_first_row (U V : SU2) (h0 : U.val 0 0 = V.val 0 0)
    (h1 : U.val 0 1 = V.val 0 1) : U = V := by
  apply Subtype.ext
  rw [su2_normalForm U, su2_normalForm V, h0, h1]

theorem zTorus_mul (z w : Circle) : zTorus (z*w) = zTorus z * zTorus w := by
  apply ext_first_row <;>
    simp [zTorus, quaternionSU2, quaternionMatrix]

theorem xTorus_mul (z w : Circle) : xTorus (z*w) = xTorus z * xTorus w := by
  apply ext_first_row <;> apply Complex.ext <;>
    simp [xTorus, quaternionSU2, quaternionMatrix,
      Complex.mul_re, Complex.mul_im]
  all_goals ring

def zHom : Circle →* SU2 where
  toFun := zTorus
  map_one' := by
    apply ext_first_row <;> norm_num [zTorus, quaternionSU2, quaternionMatrix]
  map_mul' := zTorus_mul

def xHom : Circle →* SU2 where
  toFun := xTorus
  map_one' := by
    apply ext_first_row <;> norm_num [xTorus, quaternionSU2, quaternionMatrix]
  map_mul' := xTorus_mul

theorem continuous_zTorus : Continuous zTorus := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_def, zTorus, quaternionSU2, quaternionMatrix]
  all_goals fun_prop

theorem continuous_xTorus : Continuous xTorus := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_def, xTorus, quaternionSU2, quaternionMatrix]
  all_goals fun_prop

theorem su2_topologicalGroup : IsTopologicalGroup SU2 :=
  { continuous_mul := by
      apply continuous_induced_rng.mpr
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    continuous_inv := by
      apply continuous_induced_rng.mpr
      exact continuous_subtype_val.star }

end RationalGateUniversality
