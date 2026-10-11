import HydrologyTree.BlockJacobian

/-! Actual polynomial coefficient gluing and its actual Frechet derivative. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev PolyPair (m n : ℕ) := Coeff m × Coeff n
abbrev GlueInput (m n : ℕ) := PolyPair m n × PolyPair m n

def pairBasis (m n : ℕ) : Module.Basis (Fin (m+n)) ℝ (PolyPair m n) :=
  ((degreeLT.basis ℝ m).prod (degreeLT.basis ℝ n)).reindex finSumFinEquiv

lemma coeff_natDegree_le {n : ℕ} (p : Coeff n) : (p : ℝ[X]).natDegree ≤ n := by
  simpa using bounded_natDegree (liftCLM n p)

def sylvCLM {m n : ℕ} (f g : ℝ[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    PolyPair m n →L[ℝ] Coeff (m+n) :=
  LinearMap.toContinuousLinearMap (sylvesterMap f g hf hg)

@[simp] theorem sylvCLM_cut {m n : ℕ} (f g : ℝ[X])
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (x : PolyPair m n) :
    sylvCLM f g hf hg x = cut (m+n) (f * (x.2 : ℝ[X]) + g * (x.1 : ℝ[X])) := by
  exact (cut_coe (sylvesterMap f g hf hg x)).symm

def monoSylv {m n : ℕ} (x : PolyPair m n) : PolyPair m n →L[ℝ] Coeff (m+n) :=
  sylvCLM (monicPoly x.1) (monicPoly x.2)
    (bounded_natDegree _) (bounded_natDegree _)

def lowSylv {m n : ℕ} (x : PolyPair m n) : PolyPair m n →L[ℝ] Coeff (m+n) :=
  sylvCLM x.1 x.2 (coeff_natDegree_le _) (coeff_natDegree_le _)

/-- The non-leading coefficients of `U*V`, and all coefficients of `R*V+U*S`.
Here U and V are actual monic polynomials with the supplied low coefficients;
R and S have arbitrary coefficients of degrees below m and n. -/
def glue {m n : ℕ} (x : GlueInput m n) : Coeff (m+n) × Coeff (m+n) :=
  (mulCLM (m+1) (n+1) (m+n) (monicPoly x.1.1) (monicPoly x.1.2),
   mulCLM m (n+1) (m+n) x.2.1 (monicPoly x.1.2) +
     mulCLM (m+1) n (m+n) (monicPoly x.1.1) x.2.2)

/-- The complete derivative, including the off-diagonal numerator terms. -/
def glueDerivative {m n : ℕ} (x : GlueInput m n) :
    GlueInput m n →L[ℝ] (Coeff (m+n) × Coeff (m+n)) :=
  repeatedBlock (monoSylv x.1) (lowSylv x.2)

set_option maxHeartbeats 600000 in
theorem hasFDerivAt_glue {m n : ℕ} (x : GlueInput m n) :
    HasFDerivAt glue (glueDerivative x) x := by
  let A : GlueInput m n →L[ℝ] Coeff m :=
    (ContinuousLinearMap.fst ℝ (Coeff m) (Coeff n)).comp
      (ContinuousLinearMap.fst ℝ (PolyPair m n) (PolyPair m n))
  let B : GlueInput m n →L[ℝ] Coeff n :=
    (ContinuousLinearMap.snd ℝ (Coeff m) (Coeff n)).comp
      (ContinuousLinearMap.fst ℝ (PolyPair m n) (PolyPair m n))
  let R : GlueInput m n →L[ℝ] Coeff m :=
    (ContinuousLinearMap.fst ℝ (Coeff m) (Coeff n)).comp
      (ContinuousLinearMap.snd ℝ (PolyPair m n) (PolyPair m n))
  let S : GlueInput m n →L[ℝ] Coeff n :=
    (ContinuousLinearMap.snd ℝ (Coeff m) (Coeff n)).comp
      (ContinuousLinearMap.snd ℝ (PolyPair m n) (PolyPair m n))
  have ha := (hasFDerivAt_monicPoly (A x)).comp x A.hasFDerivAt
  have hb := (hasFDerivAt_monicPoly (B x)).comp x B.hasFDerivAt
  have hp := ((mulCLM (m+1) (n+1) (m+n)).hasFDerivAt.comp x ha).clm_apply hb
  have hr := ((mulCLM m (n+1) (m+n)).hasFDerivAt.comp x R.hasFDerivAt).clm_apply hb
  have hs := ((mulCLM (m+1) n (m+n)).hasFDerivAt.comp x ha).clm_apply S.hasFDerivAt
  apply (hp.prodMk (hr.add hs)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  all_goals
    simp only [glueDerivative, repeatedBlock_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      Function.comp_apply, A, B, R, S,
      monoSylv, lowSylv, sylvCLM_cut,
      mulCLM_apply, coe_lift]
  · change cut (m+n) ((monicPoly x.1.1 : ℝ[X]) * (h.1.2 : ℝ[X])) +
        cut (m+n) ((h.1.1 : ℝ[X]) * (monicPoly x.1.2 : ℝ[X])) =
      cut (m+n) ((monicPoly x.1.1 : ℝ[X]) * (h.1.2 : ℝ[X]) +
        (monicPoly x.1.2 : ℝ[X]) * (h.1.1 : ℝ[X]))
    rw [map_add, mul_comm (h.1.1 : ℝ[X])]
  · change (cut (m+n) ((x.2.1 : ℝ[X]) * (h.1.2 : ℝ[X])) +
        cut (m+n) ((h.2.1 : ℝ[X]) * (monicPoly x.1.2 : ℝ[X]))) +
      (cut (m+n) ((monicPoly x.1.1 : ℝ[X]) * (h.2.2 : ℝ[X])) +
        cut (m+n) ((h.1.1 : ℝ[X]) * (x.2.2 : ℝ[X]))) =
      cut (m+n) ((x.2.1 : ℝ[X]) * (h.1.2 : ℝ[X]) +
        (x.2.2 : ℝ[X]) * (h.1.1 : ℝ[X])) +
      cut (m+n) ((monicPoly x.1.1 : ℝ[X]) * (h.2.2 : ℝ[X]) +
        (monicPoly x.1.2 : ℝ[X]) * (h.2.1 : ℝ[X]))
    simp only [map_add]
    rw [mul_comm (h.2.1 : ℝ[X]), mul_comm (h.1.1 : ℝ[X])]
    abel

/-- The Jacobian of the actual real coefficient map, in specified coefficient bases. -/
def gluingJacobian {m n : ℕ} (x : GlueInput m n) : ℝ :=
  (LinearMap.toMatrix ((pairBasis m n).prod (pairBasis m n))
    ((degreeLT.basis ℝ (m+n)).prod (degreeLT.basis ℝ (m+n)))
    (fderiv ℝ glue x).toLinearMap).det

/-- The two-polynomial gluing formula for every degree, every numerator and
all coefficients. Common roots and zero resultant are included. -/
theorem gluingJacobian_eq_resultant_sq {m n : ℕ} (x : GlueInput m n) :
    gluingJacobian x =
      Polynomial.resultant (monicPoly x.1.1) (monicPoly x.1.2) m n ^ 2 := by
  rw [gluingJacobian, (hasFDerivAt_glue x).fderiv]
  change (LinearMap.toMatrix _ _ (repeatedBlock _ _).toLinearMap).det = _
  rw [det_repeatedBlock]
  change (LinearMap.toMatrix (pairBasis m n) (degreeLT.basis ℝ (m+n))
    (sylvesterMap (monicPoly x.1.1) (monicPoly x.1.2)
      (bounded_natDegree _) (bounded_natDegree _))).det ^ 2 = _
  rw [pairBasis, Polynomial.toMatrix_sylvesterMap']
  rfl

end HydrologyTree
