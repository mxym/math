# Sharp mass-constrained Gaussian propeller fans

**Status:** complete self-contained analytical proofs with standalone
exact-rational computational replay. Research note, not a claim of
historical priority.

We strengthen the *planar conical fan subclass* of OpenAI's Gaussian
propeller problem by imposing a minimum Gaussian mass on each cell.
The results apply to cylindrical extensions in ambient dimension n>=2.
The upstream theorem concerns all measurable Gaussian partitions;
our constrained results concern consecutive planar sectors only.

## Main results

For k>=3, lower angle epsilon in [0,2pi/k], and f(t)=sin^2(t/2),
put a_r=[2pi-(k-r)epsilon]/r,
V_r=r*f(a_r)+(k-r)*f(epsilon).
The exact constrained optimum of the sum of squared first
Gaussian moments is max(V_1,V_2,V_3)/(2pi).

The complete paper.md also proves the following.

- An **arbitrary heterogeneous minimum-mass theorem**: if every
  sector has its own lower angle ell_i, the exact maximum is still
  the greatest among candidate vectors with at most three
  non-minimal angles. At most k + C(k,2) + C(k,3) explicit candidates
  suffice, versus the originally continuous optimization.

- **Radial universality:** the entire fan theory holds for
  every rotationally invariant probability law with finite
  nonzero first radial moment and no atom at the origin.
- **Higher-dimensional gap:** for every k>=4, equal-mass
  regular-simplex Gaussian partitions in dimension k-1
  strictly beat *all planar fan partitions* with equal
  masses 1/k. The score ratio grows as (4/pi) log k.
  For k=4 this is an explicit 3D tetrahedron:
  P_tet = 3/(4pi) [1+(2/pi) arcsin(1/3)]^2 > 1/pi.
- **Interior dimension-jump threshold:** the fixed
  tetrahedron beats all four-sector fans whenever their
  minimum mass exceeds an explicit q_tet in (1/100,1/80),
  with an exact trigonometric formula for q_tet.
- **Gaussian noise-stability consequence:** the tetrahedral
  four-cell partition strictly exceeds four equal-mass planar
  quadrants for every Gaussian correlation 0 < rho <= rho_*,
  where rho_* is the unique root of an explicit arcsine
  equation and 29/100 < rho_* < 3/10. The endpoint is
  strict because higher Hermite levels are nonzero.
  This comparison does **not** prove full regular-simplex
  optimality among all fixed-mass partitions.
- A **two-transition phase diagram** for every k>=5:
  the optimal number of non-minimal-mass sectors is successively
  3, 2, 1. The first transition has a unique explicit root,
  the second occurs at epsilon=pi/(k-2), where a continuum
  of extremizers exists.
- An exact first-transition asymptotic
  k*epsilon_*(k) =
  2pi-6 arccos((sqrt(33)-1)/8) + O(1/k).
- High-mass sharp extremizers and a quantitative stability bound
  penalizing excess angles spread over several sectors.
- The full four-sector closed form:
  M_4(epsilon)=[1+sin^3((pi/2-epsilon)/3)]/pi;
  the transition at epsilon=pi/2 has cubic behavior.
- The globally optimal three-sector angular deficit:
  9/(8pi)-P(theta) >=
  [3/(16pi^3)] sum_i(theta_i-2pi/3)^2,
  including complete equality classification.

**paper.md** contains all definitions, derivations, complete
proofs, cases and limitations.

## Reproduction (Python 3 standard library only)

    python3 check_exact.py
    python3 check_exact.py --quick

The checker uses fractions.Fraction, exact Machin-series bounds
for pi, and outward-rounded integer Taylor intervals for cosine.
It does not use binary floating point in any certified comparison.
Tests cover candidate values, certified phase-transition brackets
for k=5,6,10,100, homogeneous and heterogeneous angle grids,
and sharp all-k dimension-jump rational inequalities,
the tetrahedral transition bracket, exact small-noise
arcsine brackets, and equality cases.
Full test output is in results/exact-check.txt. See AUDIT.md.

**Finite-grid tests are not mathematical proofs.** The
universal statements are established analytically in paper.md.

## Upstream comparator and attribution

OpenAI Mathematics result family 096, *The Gaussian propeller bound
in every dimension* (24 September 2026), source pinned to
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf

Pinned public source commit:
adc7f1241b42e322a6451854ab7e4b4c146bf78a

The Gaussian problem is inherited; all constrained fan proofs
presented here are developed independently.

Fixed-mass Gaussian centroid partition problems, including the
regular-simplex conjecture, have been studied previously:
Steven Heilman, *Euclidean Partitions Optimizing Noise Stability*
(arXiv:1211.7138) and *Stable Gaussian Minimal Bubbles*
(arXiv:1901.03934). The Gaussian multi-bubble perimeter result
of Milman and Neeman (Annals of Mathematics, 2022) optimizes
a different functional. Our simplex construction is a strict
lower-bound comparison, not a claimed global optimum.

## Limitations and unfinished bibliographic work

No sharp universal optimum for arbitrary nonconical fixed-mass Gaussian
partitions is asserted. Systematic historical literature checking
and external peer review remain outstanding. We do not claim
the world-first proof of any result.
