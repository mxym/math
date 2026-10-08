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
for k=5,6,10,100, angle grids and equality cases.
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

## Limitations and unfinished bibliographic work

No constrained inequality for arbitrary nonconical Gaussian
partitions is asserted. Systematic historical literature checking
and external peer review remain outstanding. We do not claim
the world-first proof of any result.
