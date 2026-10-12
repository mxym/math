import Entry002.ArithmeticCore
import Entry002.GenericDyadicDensity
import Entry002.PrimeIdealEulerLogAnalytic

/-! Explicit intermediate interfaces for the weaker route. Their supply
propositions and generalized sieve remain open; none fills the old A5 field. -/

namespace Entry002

open Filter
open scoped Classical Topology

noncomputable section

/-- The actual membership indicator of a rational-prime supply set. -/
def supplyPrimeCoefficient (P : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ P then 1 else 0

/-- The genuine real Dirichlet sum of the supplied rational primes. -/
def supplyPrimeDirichletSeries (P : Set ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, supplyPrimeCoefficient P n / (n : ℝ) ^ s

theorem supplyPrimeCoefficient_LSeries_abscissa_le_one (P : Set ℕ) :
    LSeries.abscissaOfAbsConv (fun n => (supplyPrimeCoefficient P n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_one_of_isBigO_one
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  by_cases hn : n ∈ P <;> simp [supplyPrimeCoefficient, hn]

theorem supplyPrimeDirichletSeries_summable (P : Set ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => supplyPrimeCoefficient P n / (n : ℝ) ^ s) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((supplyPrimeCoefficient_LSeries_abscissa_le_one P).trans_lt (by exact_mod_cast hs))

theorem supplyPrimeDirichletSeries_nonneg (P : Set ℕ) (s : ℝ) :
    0 ≤ supplyPrimeDirichletSeries P s := by
  apply tsum_nonneg
  intro n
  apply div_nonneg
  · unfold supplyPrimeCoefficient
    split_ifs <;> norm_num
  · positivity

/-- Positive upper Dirichlet density, expressed by its cofinal positive
normalized lower values. The epsilon and all subsequent choices remain
explicit; this is not an eventual lower bound at every epsilon. -/
def PositiveUpperDirichletSupply (P : Set ℕ) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ η : ℝ, 0 < η → ∃ ε : ℝ,
    0 < ε ∧ ε < min η (1 / 2) ∧
      d * Real.log (1 / ε) ≤ supplyPrimeDirichletSeries P (1 + ε)

/-- Actual fixed-density good bins up to an endpoint, excluding zero/one. -/
def goodDyadicBins (P : Set ℕ) (δ : ℝ) (J : ℕ) : Finset ℕ :=
  (Finset.Icc 2 J).filter (fun j =>
    δ * (2 : ℝ) ^ j / Real.log ((2 : ℝ) ^ (j + 1)) ≤ (dyadicPrimeBatch P j).card)

/-- Fixed local density together with a cofinal positive logarithmic weight.
The Dirichlet-to-good-bin implication is an open bridge, not a field supplied
by a theorem in this module. -/
def PositiveUpperLogGoodBinSupply (P : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ β : ℝ, 0 < β ∧ ∀ J₀ : ℕ, ∃ J : ℕ,
    max J₀ 2 ≤ J ∧
      β * Real.log (J : ℝ) ≤ ∑ j ∈ goodDyadicBins P δ J, 1 / ((j : ℝ) + 1)

/-- A1--A4 plus the actual weaker prime Dirichlet supply. It is a new
intermediate proposition and does not replace the literal MainTarget. -/
structure WeakArithmeticInterface {L : Type*} [AddCommGroup L]
    (data : SignedResidueData L) (b : Module.Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : Prop where
  core : ArithmeticCore data b e
  upper_dirichlet_supply : PositiveUpperDirichletSupply data.primes

end

end Entry002
