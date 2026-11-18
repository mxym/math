# Independent mathematical audit: Euclidean cube corner measures

**PASS, with a prior-art qualification.** Frozen mathematical text SHA-256
`7bb046f038404013b29e78de4f99c83c074035defa36eef5d86b6cef93361b45`;
first checker `a5da8b4a25b4e764eedb62c6c70beaf5f1d6f72f207f2d6c5be8cd3835799020`.
The bundled proof retains that mathematical argument, with editorial changes to its status, references and endpoints; both checkers are bundled without code changes. This is an AI internal adversarial review, not an external peer review or determination of priority.

## 1. Variational criterion and dimensions

For the compact cube, extended finite signed Borel measures are finite signed measures on
Euclidean space. The Fourier density of the kernel is positive everywhere and integrable:
its tail cancels the radial multiplicity to order r⁻². The energy is consequently
strictly positive on every nonzero signed measure by Fourier uniqueness. Compactness of
probabilities and weak continuity of energy give existence; strict positive definiteness
gives strict convexity on them. A measure with constant potential c on its support is
optimal precisely if its potential nowhere falls below c. Indeed, subtraction gives the
positive quadratic increment plus twice the integral of the potential difference;
conversely, perturb by epsilon times a point mass minus epsilon times the old probability.
Order two is the reciprocal of energy, and Leinster–Roff Cor. 7.3 identifies its maximizers
with simultaneous maximizers. There is no claim about additional maximizers of order zero
alone. The corner orbit and Hamming sum have the stated factor 2^d, with side scale s, not
edge spacing on an n-by-n grid.

At a point on the relative interior of an m-face, m≥2, no vertex coincides with the
point. Trace the radial Hessian on the m tangent coordinate vectors: it is
(s exp(−sr)/r)[L²/r²+sL²/r−m]. As L≤r and L≤√m the bracket is at most
1+s√m−m, strictly negative at every s in the claimed range. This rules out a
global minimum there, and compactness and the decomposition by relative interiors
leave just edges and vertices. It is not necessary that the ambient Laplacian
or the restriction to every individual coordinate have the same sign.

Reflection sends any edge to the first coordinate edge; sorting the vertices paired by
that coordinate and the Hamming weight k on the other coordinates gives the stated
multiplicities. Differentiation gives h'_k=e^(−sr)(k−s u² r)/r³, r²=k+u².
For u≤1 and k≥1, k−s u² r≥k−s√(k+1)>0, because
k/√(k+1)≥1/√2>s. On the left half-edge each k≥1 pair therefore helps. Exactly
one k=1 pair offsets the unfavorable k=0 pair by the square result; all surplus pairs
are positive (for d>2). For the square the right edge derivative of 4U at a corner
has sign e^(−s)+(1/√2)e^(−s√2)−1: even at the cusp no two-sided derivative was used.
It is strictly decreasing through its unique zero.

## 2. Independent rigorous sign certificate

For t<1/2 and 0≤s≤s*, F_s(t) decreases strictly with s: both u e^(−su) and
u e^(−s√(1+u²)) increase with u, as s*<1, making ∂_s[H(1−t)−H(t)]<0.
It suffices to work at exact s*. I checked the original 2048-cell Taylor interval
proof, including outward rounding, exp argument ≤1, signs and closed-cell coverage,
and reran it under python -O. The three integer bounds reproduce.

The separate script `independent.py` uses exact fractions, different transcendental
enclosures, derivatives and partitions. Put r=√(1+u²), a=e^(−su), c=e^(−sr). Then

    H'  = −s a + c/r³ − s c u²/r²,
    H'' = s² a + c(s²u³/r³ − 3u/r⁵ − 3s u/r⁴).

On the same entire closed parameter box [46019/100000,46020/100000], it certifies
F''=H''(1−t)−H''(t) ≤ −71884/10⁶ for 0≤t≤1/4, and
F'=−H'(1−t)−H'(t) ≤ −8165/10⁶ for 1/4≤t≤1/2. Each covers 128 closed cells.
Exponential enclosures start from 1−x/m ≤ exp(−x/m) ≤ 1/(1+x/m), and square with
directed rational rounding, m=2¹⁰ (2²⁰ for the independent parameter root bracket).
Square roots are bracketed by integer-square-root inequalities. At the critical
s the two endpoint values F(0), F(1/2) vanish. Strict decrease on the right interval
implies F(1/4)>0; concavity then places F strictly above zero throughout (0,1/4].
This proof does not use any exponential Taylor series, middle-interval lower bound on F
or numerical interpolation. Its endpoint test gives lower/upper bounds +792/10⁸ and
−332/10⁸ on the endpoint signs.

## 3. Sharpness and what is not claimed

Strict positivity of the critical edge derivative at all interior points of
the left half-edge, together with symmetry, excludes nonvertex contacts even at s*.
Strict positivity here refers to U' on (0,1/2), not at 0 or at 1/2.
Every noncorner square point of sufficiently small positive edge coordinate violates
the equilibrium inequality if s>s*, by the negative right derivative. The restricted
positive definite problem on the four vertices always has the uniform measure as
its unique minimizer. Failure of this one probability then excludes every
vertex-supported minimizer, and the first noncorner point 1/(n−1) on all sufficiently
fine square grids eventually witnesses failure, for each fixed s>s*. The quantifier
is uniformity over all d≥2 or over all grid resolutions, not a single identical
transition in **each** d or **each** finite grid. Affinely scaled Euclidean cubes
are meant; exclude s=0. No solution above transition, no characterization of
all cube phases, no statement about the ball conjecture or the microscopic uniform measure.

## 4. Provenance

* [Leinster–Roff, Q. J. Math. (2021), Cor. 7.3, §10(2)](https://doi.org/10.1093/qmath/haab003)
  ask for the measure on a Euclidean cube or ball; the finite concentric spheres
  conjecture applies only to **balls**. The energy/diversity correspondence is prior.
* [Salim, Sheffield PhD (2021), Chapter 4](https://etheses.whiterose.ac.uk/id/eprint/29673/1/PhD_thesis.pdf).
  Sections 4.1–4.2 numerically study grids including 3×3 through 10×10. In §4.3
  Thm 4.3.3 compares the corner **orbit** with single competitor orbits at small scale;
  Thm 4.3.4 treats corner plus one further orbit in odd grids; Cor. 4.3.5 covers even
  grids. She gives qualitative theorems, not only computations. A useful consequence
  of those statements and the standard first-variation argument is already small-scale
  optimality for each fixed grid in their scope. Indeed for corner orbit probability μ and
  other orbit probability ν, the energy of (1−z)μ+zν is a strictly convex quadratic.
  Its unrestricted minimizer is the normalized weighting of the union: constant
  potential, and total weighting strictly positive by invertibility/positive definiteness.
  Salim's negative weight, constant within an orbit, places its z outside [0,1].
  The greater magnitude of the corner orbit means E(0)<E(1), hence the vertex z* of
  the quadratic is <1/2 and must be negative. Thus the derivative at 0 is positive.
  Orbit symmetry converts each such derivative to the one-point variation at every
  point of that orbit. This establishes the full fixed-grid **qualitative** claim,
  not a uniform lower bound in side length. Her scale t is **grid spacing**,
  s=(n−1)t, and approximate breakpoints on a 3×3 grid are not the continuum critical
  equation. The advantage here is the exact continuum threshold and the sharp range
  uniform over resolutions/all d, not the discovery that very small grids favor corners.
* [Dajani, arXiv:2610.38031 (2026), §2 Eqs. (4),(5)](https://arxiv.org/pdf/2610.38031).
  Already gives the Fourier positive-energy identity and necessary/sufficient equilibrium
  potential test for arbitrary compact domains. Ball threshold propositions use that
  same test, then use ball-specific reductions. The closing discussion (p. 28) distinguishes
  the factorized taxicab box and leaves Euclidean cube support undetermined.
  Searches of the mathematical literature, including Leinster's [magnitude bibliography](https://webhomes.maths.ed.ac.uk/~tl/magbib/),
  did not locate this sharp Euclidean-cube threshold. This is not a priority guarantee.
* At the time of this mathematical audit, the GitHub API resolved main to #103,
  `dbd59e86427ab13aa1a0bc9688835fb9fe5ba7a4`. I inspected the author's reproducible
  scan settings and hit reports against that SHA: 14,770 unique main blobs, 277
  tag-only blobs, 160 archives/162 PDFs across that search, and a separate release-asset
  search. Hits for the target pattern were unrelated. I did not independently re-extract
  every attachment, and keyword searches cannot establish absence of all equivalents.
