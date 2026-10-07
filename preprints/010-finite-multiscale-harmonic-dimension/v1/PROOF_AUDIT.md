# 010 v1 proof audit

This file audits the new finite-multiscale deduction independently of its
expository presentation in paper.md.

## A. Quantifiers

The proved statement is finite:

for every finite m, there exists one metric g handling m selected scales.

It is not:

there exists one metric g handling infinitely many unbounded scales.

The construction fixes the largest finite cutoff p_m before invoking the
radial, transfer, and matching arguments.

## B. Parameter feasibility

Fix beta > 1 and A >= 1 with A beta^2 < 9/4. Choose a in (2/3,1)
arbitrarily close to one so that the desired near-Euclidean tensor bound
holds and

A beta^2 < 9a^2/4.

Then choose theta with

A beta^2 < theta^2 < 9a^2/4.

Shrinking the angular neighborhood makes the ordered-spectrum comparison
constant C_* arbitrarily close to one, so

2 theta sqrt(C_*) / (3a) < 1

can also be imposed strictly.

For each band choose k_r sufficiently large. The needed conditions are:

1. the upstream adjacent-double threshold;
2. M_{r-1} < L_r, where L_r=floor(sqrt(k_r)) and
   M_r=floor(theta k_r);
3. the strict band-average inequality;
4. the fixed-low-rank inequality;
5. M_r >= floor(beta(k_r+1));
6. (M_r+1)^2 > A floor(beta(k_r+1))^2.

All are lower-bound conditions on k_r; condition 6 is eventually true
because M_r/k_r tends to theta and theta^2 > A beta^2. In particular, condition 2 can be
forced by taking k_r > M_{r-1}^2. Thus the scales can be separated as
widely as desired.

verification/check_bands.py replays the quantitative choice
A=11/10, beta=4/3, theta=7/5 on five separated bands using only Python
integers and Fraction. It certifies the exact structural slack
theta^2-A beta^2=1/225.

## C. Common-cutoff crossings

A double supplied for band I_r is initially isolated only through that
band's one-scale cutoff. This is insufficient for a combined program.

The upstream retained-double lemma resolves the issue: for any exact
isolated double and any larger finite cutoff q, it permits an arbitrarily
small perturbation that keeps the designated double exact while splitting
every other multiplicity through q, including the outer gap.

Apply it with the common q=p_m+1 to every designated adjacent pair in every
band. Since only finitely many doubles are used, all chosen points remain
inside the prescribed angular neighborhood.

Finite-cutoff avoidance, also with p_m+1, connects every short crossing
segment to one base point while introducing no other crossing in the
protected range.

Hence the combined loop has exactly the intended simple double crossings
through the entire finite cluster.

## D. Return permutation and common period

Each short crossing swaps two adjacent ordered positions inside one band.
Every connector is simple through the protected cutoff, so it changes no
ordered rank. Therefore every partial rank permutation preserves each
band I_r.

Concatenating the standard adjacent swaps inside I_r gives one cycle C_r
on that band. Because the bands are disjoint, the total return permutation
is the product of disjoint cycles

C = C_1 ... C_m.

All positions outside the bands are fixed.

Let N_r=|I_r| and Q=lcm(N_1,...,N_m). Then all continued eigenvalues have
common period Q S; allowing real eigenline signs, the frame has period at
most 2 Q S. This supplies a single finite periodic datum for all pairwise
matching recurrences.

## E. Exact multiband average

Fix a label i in band I_r and a noncrossing phase t in one basic period.
Let sigma_t be the partial rank permutation accumulated by that phase.
Because all swaps stay inside their bands,

sigma_t(I_r)=I_r.

At the same phase in period number q, the rank of i is

sigma_t C^q(i).

For q=0,...,N_r-1, C^q(i) traverses I_r exactly once. Hence so does
sigma_t C^q(i). Integrating phasewise gives the exact identity

mean(i)
= (1/(N_r S)) integral_0^S sum_{j in I_r}
    d(a^{-2} lambda_j(H(t))) dt.

No estimate involving another band's duration is needed. Repeating the
identity Q/N_r times gives the same mean over the common period.

The near-round ordered-spectrum estimate bounds this mean by the same
one-band weighted average as in the upstream proof, which is strictly less
than k_r for large enough k_r.

## F. Prefix mean bound

For a fixed scale r, every label among positions 1,...,p_r is in one of
three classes.

1. I_r: mean < k_r by Section E.
2. An earlier band I_q, q<r: mean < k_q < k_r.
3. No band: its rank never changes. Since the current band is exactly
   B_{L_r}+1,...,p_r, such a rank not in an earlier band is at most
   B_{L_r}. Its instantaneous cone frequency is bounded by
   a^{-1} sqrt(C_*) (L_r+1) < k_r.

Future bands begin above p_r because of band separation. Therefore no
fourth case exists, and

max_{i<=p_r} mu_i < k_r.

## G. Applicability of radial/transfer/matching machinery

The combined object is one finite smooth periodic angular program. It has:

- fixed area form;
- the same prescribed curvature neighborhood;
- a strict outer gap after p_m;
- a smooth continued frame through p_m;
- finitely many linearly split doubles;
- a nonzero off-diagonal control direction at each double;
- finite smooth norms and crossing separations.

For a pair of labels in one band, crossings recur with bounded gaps over
the common period. For a pair in different bands, or involving a fixed
label, equality never occurs; compactness of the common period gives a
uniform gap.

These are exactly the structural inputs used in the pinned
radial/transfer/matching sections. Inspection of those sections finds no
use of the assertion that the return permutation has one nontrivial cycle
after the angular mean estimate. Constants are permitted to depend on the
fixed p_m and the fixed finite program.

Thus the published analytic proof applies without any new limiting or
uniform-in-m assertion.

## H. Growth and independence

The simultaneous matching produces p_m exact invariant lines and hence
p_m independent entire harmonic functions. The upstream growth section
identifies the exact logarithmic spherical exponent of the i-th function
with mu_i.

For each fixed r, Section F gives a strict finite margin below k_r for the
first p_r exponents. Choose gamma_r strictly between their maximum and k_r.
The same all-radius contraction plus local elliptic estimate then puts all
first p_r functions in H_{k_r}. Their independence was established
simultaneously at the common inner sphere, so

h_{k_r} >= p_r = (M_r+1)^2.

No uniform growth constant in r is required because m is finite.

## I. Integer block endpoint

For

D_r = floor(beta(k_r+1)) - 1,

the parameter choice gives D_r+1 <= M_r. For k_r <= d <= D_r,
monotonicity of polynomial-growth spaces gives

h_d >= h_{k_r} >= (M_r+1)^2
    > A floor(beta(k_r+1))^2
    >= A(d+1)^2.

This is strict even when beta(k_r+1) is an integer and proves the same
A-factor excess on every selected block.

## J. Geometry

The radial realization and tensor comparison are applied to the combined
finite program exactly as to the one-band program. Hence completeness,
Ricci nonnegativity, eventual positive Ricci curvature, Euclidean core,
global near-Euclidean tensor comparison, and prescribed asymptotic volume
ratio carry over.

The combined path contains a base phase simple through the protected
cluster and a designated double phase, so its ordered spectrum is
nonconstant. The pinned tangent-cone argument then supplies an interval of
link spectra and hence uncountably many pairwise nonisometric cone limits.
At a phase with nonzero angular derivative, the pinned radial sectional
curvature calculation also supplies negative radial planes along an
escaping sequence.

## K. Audit conclusion

The genuinely new part of 010 is finite-dimensional and exact:
common-cutoff spectral assembly, disjoint-cycle permutation algebra,
multiband rank averaging, and prefix bookkeeping.

No floating-point computation, heuristic optimizer, or solver output is
used in the proof. The checker is supplementary exact arithmetic, not a
replacement for the imported analytic arguments.

The remaining unproved step is the countably infinite-band limit.
