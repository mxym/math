import Entry002.PrimeIdealEulerLogIdentity

/-! The logarithmic real-pole asymptotic for the actual Euler-logarithm
series. This is weaker than a prime-ideal PNT and requires no such premise. -/

namespace Entry002

open NumberField Filter
open scoped NumberField Classical Topology ComplexOrder

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Euler-logarithm series has the logarithmic singularity of
the positive actual Dedekind-zeta real pole. -/
theorem primeIdealEulerLogLSeries_add_log_sub_one_tendsto_nhdsGT :
    Tendsto
      (fun s : ℝ ↦ (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re +
        Real.log (s - 1))
      (𝓝[>] 1) (𝓝 (Real.log (dedekindZeta_residue K))) := by
  have h : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
    simpa [Function.comp_def, Complex.mul_re] using
      Complex.continuous_re.tendsto (dedekindZeta_residue K : ℂ) |>.comp
        (actualDedekindZeta_tendsto_sub_one_mul_nhdsGT K)
  apply (h.log (actualDedekindZeta_residue_pos K).ne').congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hz := (Complex.pos_iff.mp (actualDedekindZeta_pos_real K hs)).1
  rw [Real.log_mul (sub_pos_of_lt hs).ne' hz.ne',
    actualDedekindZeta_real_log_eq_eulerLog K hs]
  ring

end

end Entry002
