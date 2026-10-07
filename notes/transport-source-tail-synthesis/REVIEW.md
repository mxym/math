# Mathematical synthesis: exact statement, provenance and independent-review boundary

This note presents the exact density-root characterization and its conditional transport consequences. Its mathematical review is model-based, with the scope and attribution boundaries stated below.

## Exact information order and overlap functional

Fix 1<s<infinity. For transport targets with a finite q-th moment, 2<q<infinity, the relevant conjugate source order is

s=q/(q-2), and sigma=r^(1/s)=r^((q-2)/q).

The source-method theorem itself allows any 1<s<infinity independently of a target law. Let d>=1, and let r be a finite, measurable, nonnegative representative of a Lebesgue probability density on all of R^d. Set rho=r dx. If originally supported in a set, extend r by zero to all of R^d. No positivity, smoothness, support connectivity, convexity of the support, log-concavity or source second moment is assumed for this source-method theorem.

For every coordinate j and h>0 define

d_{j,+h}(x)=(1-r(x+h e_j)/r(x))_+,
d_{j,-h}(x)=(1-r(x-h e_j)/r(x))_+

where r(x)>0, and set BOTH deficits to zero where r(x)=0. The exact functional is

W_{j,h}=6|d_{j,+h}-d_{j,-h}|+2d_{j,+h},  0<=W_{j,h}<=8.

Equivalently, m_{j,h}(x)=min(r(x),r(x+h e_j)), with the same zero quotient convention, gives

W_{j,h}=6|m_{j,h}(x-h e_j)-m_{j,h}(x)|/r(x)+2[1-m_{j,h}(x)/r(x)].

The linear-overlap condition is ||W_{j,h}||_{Ls(rho)}=O(h) as h decreases to zero for EVERY coordinate j. It is not a raw ratio condition on r(x+h)/r(x). It is equivalent, up to the stated constants, to Xi_j(h)=max_±||(1-r(x±h e_j)/r(x))_+||_{Ls(rho)}=O(h).

## Precisely proposed equivalence and limit

sigma belongs to global W^(1,s)(R^d) if and only if, for each j,

limsup_{h down to 0} ||W_{j,h}||_{Ls(rho)}/h < infinity.

For each coordinate, a finite liminf is already sufficient; the sequence of increments may be chosen separately for different coordinates. No conclusion is asserted at s=1 or s=infinity. At s=1 the translation criterion characterizes BV and retains boundary jumps, so an iff-W1,1 extension would be false.

With b_j=partial_j sigma, the proposed exact first-order limit is

sigma W_{j,h}/h -> s[6|b_j|+2(-b_j)_+]

strongly in Ls(dx). In particular,

lim_{h down to 0} ||W_{j,h}||_{Ls(rho)}/h = s ||6|b_j|+2(-b_j)_+||_{Ls(dx)}.

A weighted form sets S_j=s b_j/sigma on {sigma>0} and S_j=0 on {sigma=0}; then W_{j,h}/h -> 6|S_j|+2(-S_j)_+ strongly in Ls(rho). It is the classical score only when the density is positive and sufficiently regular. Boundary jumps are tested by the global root condition and are not discarded as an interior score integral.

## Existing versus proposed additions

- Already in001v5 Theorem6.1 and008 Lemma2.1 / Theorem1.2: global root Sobolev regularity IMPLIES linear overlap control and conditional one-third interpolation/transport upper bounds. Recounting this sufficient direction is not a new project result.
- Proposed additional converse: linear bounded-overlap control IMPLIES global root Sobolev regularity, including the finite-liminf formulation. This makes a sufficient source condition into an exact characterization of this interpolation method. No literature-novelty claim is made.
- Proposed additional limit: the strong Ls(dx) limit of sigma W/h, and hence strong Ls(rho) convergence of W/h to its generalized score weight. The earlier001v5 Proposition5.1 proves the exact L1(dx) limit of rW/h for every W1,1 density. The new rooted-Ls statement refines first-order control on the root-Sobolev subclass; it does not replace or strictly contain that broader W1,1 result.
- Existing result recovered: multiply the new limit by sigma^(s-1) and use Holder to recover rW/h -> 6|partial_j r|+2(-partial_j r)_+ in L1 on the root subclass. The recovered L1 formula is already001v5 and is not counted anew.
- The profile envelope is a DERIVED REFORMULATION of001v5 Lemma3.1 using elementary layer-cake rearrangement, not a new sharpness theorem. It assumes neither independence nor non-atomic target laws; no converse or realizability of optimizing profiles by convex gradients is asserted.

“Proposed additional” describes what this draft adds relative to the cited repository statements, not publication priority. The proposed proof and its imported statements have undergone an independent model audit. This does not constitute external human peer review, proof-assistant verification, or a literature-novelty certification.

## Proof mechanism and transport boundary

For B_j(h)=||sigma(.+h e_j)-sigma||_{Ls(dx)}, elementary inequalities give

2 Xi_j(h) <= ||W_{j,h}||_{Ls(rho)} <= 14 Xi_j(h),
B_j(h) <= 2^(1/s-1)||W_{j,h}||_{Ls(rho)},
||W_{j,h}||_{Ls(rho)} <= 14s B_j(h).

The root increment is split into downward and upward parts. Reversing the latter by translation retains zero-support boundary terms. Bounded difference quotients yield weak derivatives by reflexivity for s>1. Sobolev translation continuity supplies the sufficient direction. For the limit, the divided difference (1-t^s)/(1-t) is bounded between1 ands and tends tos; its product with strong Sobolev difference quotients converges in Ls. On {sigma=0}, the weak derivative vanishes almost everywhere. The proof handles zeros rather than assuming positivity.

This theorem is about a density and needs no convex potentials. Its TRANSPORT application is conditional: rho must be an absolutely continuous source in P2 with proper convex Brenier representatives finite rho-almost everywhere, square-integrable gradients and centered differences, satisfying the separately proved potential estimate (P): ||U_mu-U_nu||L2(rho)<=A_rho W2(mu,nu). Effective convex domains may be extended by +infinity. Arbitrary root/BV density regularity, including disconnected supports, does NOT supply (P).

The potential estimate is001v3 Theorem1.1 for full-dimensional r=Z^-1 exp(-kappa|x|^2/2-W), kappa>0, W proper lower-semicontinuous convex, with A=sqrt(2/kappa). Its compact companion, Theorem1.4, assumes a full-dimensional log-concave probability density supported on a compact convex body K contained in B_R, R>0, and has A=(1+sqrt162)R. Centered potentials lie in L2(rho), are finite and convex on int K, and use proper convex extensions to R^d for interpolation. Upper transport consequences depend on these proof inputs; standalone interpolation and directly constructed lower examples have separate hypotheses. Failure of linear overlap does NOT prove failure of one-third map stability. The boundary/source threshold and logarithmic TARGET-tail threshold are not identified.

## Readable frozen proof references

All references below use base c897a556e12e460380c7cf521e88f84286994915. DEPENDENCIES.json provides exact Git blobs and SHA-256 hashes for 57 inputs; byte-exact copies are included under sources/.

- [001v3, Theorems1.1 and1.4: full potential foundations](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex)
- [001v5, Lemma3.1, Proposition5.1 and Theorem6.1: exact weight, L1 limit and root sufficient direction](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/001-strongly-log-concave-brenier/v5/manuscript.tex)
- [008v1, Lemma2.1, Theorem2.2 and Theorem1.2: root-to-overlap and Fisher criterion](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/008-density-overlap-phase/v1/main.tex)
- [007v2: sharper coarea tail bound and smooth full-support sharpness](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/preprints/007-tail-brenier-stability/v2/main.tex)
- [Critical slowly-varying supplement: family-specific modulus and necessity](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/notes/critical-boundary-slow-variation/manuscript.tex)
- [Existing source-regularity reconciliation](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/comparisons/2026-10-07-source-regularity-reconciliation.md)
