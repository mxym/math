import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Factorization

/-! Curated dependency of upstream Arithmetic.lean.
The simplexConstant definition below is identical to openai/math,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/Geometry/ProjectionVolume/Model.lean.
The unused geometric definitions and the broad `import Mathlib` were omitted.
The full original is retained in vendor/openai/Model.lean. -/
namespace OAI.Paper092
noncomputable def simplexConstant (d : ℕ) : ℝ :=
  (d + 1) * (d : ℝ) ^ d / d.factorial
end OAI.Paper092
