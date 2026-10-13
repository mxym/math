import HydrologyTree.GraphMatrixTransport
import HydrologyTree.PolynomialMapJacobian
import HydrologyTree.LocatedLeakJacobian

/-! Independent symbolic characteristic/cofactor coefficient polynomials for
actual graph matrices with a separate leak vertex. No Jacobian formula is built
into their definition; formal partial differentiation is applied afterwards. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev GraphCoordinate (G : SimpleGraph V) := Unit ⊕ G.Dart
abbrev GraphRatePolynomial (G : SimpleGraph V) := MvPolynomial (GraphCoordinate G) ℝ
abbrev GraphRatesOver (R : Type*) (G : SimpleGraph V) := R × (G.Dart → R)

def graphRatesOverMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (y : GraphRatesOver R G) : GraphRatesOver S G := (φ y.1,fun d => φ (y.2 d))

def graphMatrixOver {R : Type*} [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ell : V) (y : GraphRatesOver R G) : Matrix V V R :=
  (∑ d : G.Dart,y.2 d • (Matrix.single d.snd d.fst 1-Matrix.single d.fst d.fst 1))-
    y.1 • Matrix.single ell ell 1

lemma graphMatrixOver_real (ell : V) (y : GraphRates G) :
    graphMatrixOver G ell y=graphCompartmentMatrix G ell y := rfl

lemma graphMatrixOver_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ell : V) (y : GraphRatesOver R G) :
    (graphMatrixOver G ell y).map φ=graphMatrixOver G ell (graphRatesOverMap φ y) := by
  have hsm (c : R) (A : Matrix V V R) : φ.mapMatrix (c • A)=φ c • φ.mapMatrix A := by
    ext i j
    simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
  have hsingle (i j : V) (c : R) : φ.mapMatrix (Matrix.single i j c)=Matrix.single i j (φ c) := by
    ext k l
    simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.single_apply]
    by_cases h : i=k ∧ j=l <;> simp [h]
  change φ.mapMatrix (graphMatrixOver G ell y)=_
  simp only [graphMatrixOver,map_sub,map_sum,hsm,hsingle,map_one]
  rfl

/-- Genuine observed principal cofactor in the symbolic coefficient ring. -/
def graphCofactorOver {R : Type*} [CommRing R] (o ell : V) (y : GraphRatesOver R G) : R[X] :=
  (Matrix.charmatrix (graphMatrixOver G ell y)).adjugate o o

lemma graphCofactorOver_real (o ell : V) (y : GraphRates G) :
    graphCofactorOver o ell y=diagonalCofactor (graphCompartmentMatrix G ell y) o := rfl

lemma graphCofactorOver_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (o ell : V) (y : GraphRatesOver R G) :
    (graphCofactorOver o ell y).map φ=graphCofactorOver o ell (graphRatesOverMap φ y) := by
  have h := congrArg (fun A : Matrix V V S[X] => A o o)
    ((Polynomial.mapRingHom φ).map_adjugate (Matrix.charmatrix (graphMatrixOver G ell y)))
  change Polynomial.map φ ((Matrix.charmatrix (graphMatrixOver G ell y)).adjugate o o)=
    ((Matrix.charmatrix (graphMatrixOver G ell y)).map (Polynomial.map φ)).adjugate o o at h
  rw [← Matrix.charmatrix_map,graphMatrixOver_map] at h
  exact h

def graphRateArrayEquiv (G : SimpleGraph V) : GraphRates G ≃ₗ[ℝ] (GraphCoordinate G → ℝ) where
  toFun y := Sum.elim (fun _ => y.1) y.2
  invFun z := (z (.inl ()),fun d => z (.inr d))
  left_inv y := rfl
  right_inv z := by funext i; rcases i with i | d; cases i; rfl; rfl
  map_add' x y := by funext i; rcases i with i | d <;> rfl
  map_smul' c x := by funext i; rcases i with i | d <;> rfl

@[simp] lemma graphRateArray_leak (y : GraphRates G) : graphRateArrayEquiv G y (.inl ())=y.1 := rfl
@[simp] lemma graphRateArray_dart (y : GraphRates G) (d : G.Dart) : graphRateArrayEquiv G y (.inr d)=y.2 d := rfl

def universalGraphRates (G : SimpleGraph V) : GraphRatesOver (GraphRatePolynomial G) G :=
  (MvPolynomial.X (.inl ()),fun d => MvPolynomial.X (.inr d))

lemma universalGraphRates_eval (y : GraphRates G) :
    graphRatesOverMap (MvPolynomial.eval (graphRateArrayEquiv G y)) (universalGraphRates G)=y := by
  apply Prod.ext
  · simp [universalGraphRates,graphRatesOverMap]
  · funext d
    simp [universalGraphRates,graphRatesOverMap]

/-- Actual monic coefficient polynomials, returned in the explicitly declared
fixed graph-rate-shaped output ordering. -/
def symbolicLocatedCoefficients {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (ell : V) :
    GraphCoordinate G → GraphRatePolynomial G
  | .inl _ => (graphMatrixOver G ell (universalGraphRates G)).charpoly.coeff 0
  | .inr d => Sum.elim
      (fun e : Fin n => (graphMatrixOver G ell (universalGraphRates G)).charpoly.coeff e.succ)
      (fun e : Fin n => (graphCofactorOver o ell (universalGraphRates G)).coeff e)
      ((treeDartEquiv p).symm d)

/-- Every symbolic output specializes to the actual independent graph coefficient,
for ALL real rate vectors, including signed and zero-boundary values. -/
lemma symbolicLocatedCoefficients_evaluate {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) :
    polynomialCoordinateMap (symbolicLocatedCoefficients p ell) (graphRateArrayEquiv G y)=
      graphRateArrayEquiv G (normalizedLocatedGraphCoefficients p ell y) := by
  let φ := MvPolynomial.eval (graphRateArrayEquiv G y)
  have hP : ((graphMatrixOver G ell (universalGraphRates G)).charpoly).map φ=
      (graphCompartmentMatrix G ell y).charpoly := by
    rw [← Matrix.charpoly_map,graphMatrixOver_map,universalGraphRates_eval,graphMatrixOver_real]
  have hF : (graphCofactorOver o ell (universalGraphRates G)).map φ=
      diagonalCofactor (graphCompartmentMatrix G ell y) o := by
    rw [graphCofactorOver_map,universalGraphRates_eval,graphCofactorOver_real]
  have hcP (i : ℕ) := congrArg (fun Q : ℝ[X] => Q.coeff i) hP
  have hcF (i : ℕ) := congrArg (fun Q : ℝ[X] => Q.coeff i) hF
  simp only [Polynomial.coeff_map] at hcP hcF
  funext i
  rcases i with i | d
  · cases i
    change φ ((graphMatrixOver G ell (universalGraphRates G)).charpoly.coeff 0) =
      ((cut (n+1) (graphCompartmentMatrix G ell y).charpoly : Coeff (n+1)) : ℝ[X]).coeff 0
    exact (hcP 0).trans (cut_coeff (n+1) (graphCompartmentMatrix G ell y).charpoly (0 : Fin (n+1))).symm
  · obtain ⟨e,rfl⟩ := (treeDartEquiv p).surjective d
    rcases e with e | e
    · simpa only [polynomialCoordinateMap,symbolicLocatedCoefficients,Equiv.symm_apply_apply,Sum.elim_inl,
        graphRateArray_dart,graphRateEquiv_inward,normalizedLocatedGraphCoefficients,
        coefficientArrayEquiv_first,locatedGraphCoefficientMap,cut_coeff] using hcP e.succ
    · simpa only [polynomialCoordinateMap,symbolicLocatedCoefficients,Equiv.symm_apply_apply,Sum.elim_inr,
        graphRateArray_dart,graphRateEquiv_outward,normalizedLocatedGraphCoefficients,
        coefficientArrayEquiv_second,locatedGraphCoefficientMap,cut_coeff] using hcF e

/-- Independently defined determinant of actual formal partial derivatives. -/
def formalLocatedJacobian {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (ell : V) : GraphRatePolynomial G :=
  formalJacobianPolynomial (symbolicLocatedCoefficients p ell)

end HydrologyTree
