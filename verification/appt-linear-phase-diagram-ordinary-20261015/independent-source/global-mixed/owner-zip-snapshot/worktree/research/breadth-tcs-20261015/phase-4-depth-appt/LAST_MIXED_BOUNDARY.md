# Last mixed boundary: interior coexistence without a no-islands assumption

Author: Yongxian Zhang (张永贤), South China University of Technology.
Contact: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
Date: 2026-10-15. Author research manuscript, pending independent ordinary review.
No Lean claim, no submission, no new-major claim. No funding. OpenAI assisted
the mathematical investigation and writing. Original text: all rights reserved;
third-party results retain their original attribution and rights.

## Scope and credited inputs

This note concerns the scalar variational problem arising from the original
complex-density, every-global-unitary APPT problem. It does not replace that
problem by a restricted family of states. The previously established linear-order
value theorem L and the actual-spectrum nearoptimizer theorem S are credited
inputs only to the transfer statement at the end. Their exact main-source bytes
are recorded in CREDITED_SOURCES.json. The scalar argument below is self-contained.

The earlier frozen author note PURE_ENVELOPE_GE_ONE.md, SHA-256
ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9,
contains the c >= 1 estimate used here. Its proof is repeated in Appendix A so
that no unreviewed collaborator's scalar draft is a dependency. The present note
does not assume uniqueness of a mixed boundary, nor that the mixed-c set is an
interval. Independent review of this note remains required.

## Definitions

For c > 0, r >= 0, 0 <= L <= 2 and 0 <= h <= 1, put

    G(L) = 2L^2 / [3(2-L)]                         (L < 2),
    B(c,L,h) = exp(-c L h) [1+h(exp(cL)-1)],
    P(c,L,h) = exp[-c(Lh+G(L))]                   (L < 2),
    P(c,2,h) = 0,
    F(c,r,L,h) = B(c,L,h) + r P(c,L,h),
    V(c,r) = max_[0,2]x[0,1] F(c,r,L,h).

At L=0, B=P=1 and h is a redundant coordinate. Write

    q(t) = t/(exp(t)-1),
    b(t) = (exp(t)-1)/t * exp[-1+q(t)],
    g(t) = log b(t),
    h_b(c) = 1/(2c)-1/(exp(2c)-1),
    r_0(c) = b(2c)-1.

The maximum of B at fixed positive L is b(cL), attained at the unique
h=1/(cL)-1/(exp(cL)-1), which lies strictly between zero and one.
Also b'(t)>0 for every t>0; Appendix A proves the needed strict derivative.
Consequently b(2c)>1 and r_0(c)>0. The two pure branches have values b(2c)
at (2,h_b(c)), and 1+r on {0} x [0,1].

Define the strict mixed-c set

    M = {c>0 : for some r>=0, V(c,r)>max(b(2c),1+r)}

and the crossing excess

    A(c) = V(c,r_0(c))-b(2c) >= 0.

The word mixed here always means strict improvement in value. An interior point
tying the two pure branches at a boundary is explicitly distinguished from a
positive open interval of strict mixed values.

## Theorem

1. M={c>0:A(c)>0} is open. It contains every 0<c<=1/10 and has supremum
   c_dagger satisfying 1/10<c_dagger<1.
2. At every positive finite boundary point c_bar of M, the complete value is

       V(c_bar,r)=max{b(2c_bar),1+r}               for every r>=0.

   For r<r_0(c_bar) the only maximizer is (2,h_b(c_bar)). For r>r_0(c_bar)
   the complete maximizer set is {0}x[0,1]. At r=r_0(c_bar), these two pure
   maximizers coexist with at least one point satisfying 0<L<2 and 0<h<1.
   This conclusion applies in particular to c_bar=c_dagger.
3. All the interior ties in part 2 are bounded away from the four scalar
   boundary faces locally uniformly in positive c. More precisely, on every
   compact c interval I subset (0,infinity), all strict-crossing maximizers
   belong to a common compact rectangle contained in (0,2)x(0,1).
4. By the credited APPT value and nearoptimizer theorems, at every such c_bar
   and r_0(c_bar), there are at least three distinct attainable limiting body
   laws for actual APPT nearoptimizers: the pole law, the pure bulk law, and
   an interior mixed law. The conclusion includes the actual loss conditions
   of S; it is not a scalar-only existence claim.

No assertion here says M=(0,c_dagger), excludes additional components of M,
or establishes uniqueness or nondegeneracy of an interior tie. Those are open
in this note. The symbol c_dagger is the last boundary, not an assertion of a
unique transition.

## 1. Continuity and the crossing test

On every compact interval of c>0, P tends to zero uniformly in h as L tends
to 2. Thus F is jointly continuous, including L=2, on the relevant compact
scalar rectangles. Its maximum V and A are continuous. The pure points give
A>=0.

Suppose A(c)=0. Abbreviate b=b(2c), r_0=b-1. For 0<=r<r_0,

    F(c,r,L,h) = (r/r_0)F(c,r_0,L,h)+(1-r/r_0)B(c,L,h) <= b.

Equality requires B=b, including when r=0; strict increase of b(cL) and the
unique h maximum force (L,h)=(2,h_b(c)). For r>r_0,

    F(c,r,L,h)-(1+r)
      = F(c,r_0,L,h)-b+(r-r_0)(P(c,L,h)-1) <= 0.

Equality requires P=1. Since G(L)>0 for 0<L<2 and P(2,h)=0, this means L=0.
At r=r_0 the value is b by definition of A. This proves the complete pure
envelope and the strict-r argmax assertions whenever A=0.

Conversely A>0 supplies a strict mixed value already at r=r_0. The crossing
test M={A>0} follows, and continuity makes M open.

## 2. A fully explicit small-c witness

Let X be Bernoulli(h)-h. It has mean zero, |X|<=1 and variance h(1-h).
For t>=0, Taylor's formula with integral remainder gives

    E exp(tX)-1 <= (t^2 exp(t)/2) h(1-h).

Indeed the first-order expectation vanishes and the exponential in the
second-order integral is at most exp(t). Since B(c,L,h)=E exp(cL X),

    b(t)-1 <= t^2 exp(t)/8.

Choose L=1,h=1/2. Here B=cosh(c/2), P=exp(-7c/6), and therefore

    F(c,r_0,1,1/2)-b(2c)
      = cosh(c/2)-1-r_0(1-exp(-7c/6))
      >= c^2/8 - (c^2 exp(2c)/2)(7c/6)
      = c^2[1/8-(7/12)c exp(2c)].

For 0<c<=1/10, exp(2c)<=1/(1-2c)<=5/4; the first inequality follows by
integrating 1/(1-t)>=1, or from -log(1-x)>=x. Hence c exp(2c)<=1/8 and
the last display is at least (5/96)c^2>0. Thus (0,1/10] subset M.

Appendix A proves M has no point c>=1. In particular M has a positive finite
supremum c_dagger, and openness already implies c_dagger>1/10.

## 3. Uniform exclusion of L near zero

Fix a compact interval I=[a,b] with 0<a<=b<infinity, and set

    r_min=min_I r_0(c)>0,   r_max=max_I r_0(c)<infinity.

The preceding centered-Bernoulli remainder estimate implies

    B(c,L,h)-1 <= (cL)^2 exp(2b) h(1-h)/2
                <= (cL)^2 exp(2b) h/2.

For h>0 and L>0, using 1-exp(-t)>=t exp(-t),

    1-P >= 1-exp(-cLh) >= cLh exp(-2b).

Consequently the crossing excess of this point is bounded above by

    B-1-r_0(c)(1-P)
      <= cLh[(cL)exp(2b)/2-r_min exp(-2b)] < 0

whenever 0<L<ell_0 for a sufficiently small positive ell_0 depending only
on I. For h=0 the same strict negativity follows directly from B=1 and
P=exp(-cG(L))<1. Thus no positive-width point sufficiently near L=0 can
reach or exceed the pure crossing value, uniformly for c in I.

This estimate deliberately keeps the small h factor; mere pointwise
convergence of B and P to one would not prove the necessary uniform result.

## 4. Uniform exclusion of L near two

Restrict first to L>=1. Since b'(t)>0 continuously on [a,2b],

    beta=min_[a,2b] b'(t)>0,
    b(2c)-B(c,L,h) >= b(2c)-b(cL) >= a beta(2-L).

Writing delta=2-L, we have

    P <= exp[-cG(L)] <= exp[-2a/(3 delta)].

Thus

    F(c,r_0,L,h)-b(2c)
      <= -a beta delta+r_max exp[-2a/(3 delta)] < 0

for all sufficiently small positive delta, uniformly in c in I and h.
Here exp[-C/delta]/delta tends to zero for C>0. The derivative beta is
strictly positive because its explicit formula is positive; strict
monotonicity by itself would not have justified this step.

Choose ell>0 small enough that both width exclusions hold outside
[ell,2-ell]. On this remaining compact width interval the crossing excess
at h=0 or h=1 is strictly negative: B=1, P<1 and b(2c)=1+r_0(c).
Continuity and compactness exclude common neighborhoods of both h faces.
Every point with crossing excess >=0 and 0<L<2 therefore lies in a fixed
compact rectangle [ell,2-ell]x[eta,1-eta] with eta>0.

This proves part 3, in fact for every nonnegative-excess positive-width
point, which is stronger than the stated assertion for strict maximizers.

## 5. Passage to every positive boundary

Let c_bar>0 be a finite boundary point of the open set M. Then A(c_bar)=0.
Choose c_j in M tending to c_bar, and choose global crossing maximizers
(L_j,h_j) at c_j. Their excess is A(c_j)>0. They cannot have L=0 or L=2,
whose crossing excess is zero. Sections 3-4 put all sufficiently late
(L_j,h_j) into a common compact subset of (0,2)x(0,1). A subsequence
converges to an interior point (L_bar,h_bar). Joint continuity, including
continuity of r_0, gives

    F(c_bar,r_0(c_bar),L_bar,h_bar)=b(2c_bar).

Because A(c_bar)=0, this is a global maximum, tied with the two pure
maximizers. Section 1 supplies the complete all-r value and strict-r
argmax statements. No uniqueness of the interior point was used.

Apply this to c_bar=c_dagger. It is a boundary because it is the supremum
of a nonempty bounded open set. If c_dagger=1, the resulting interior
tie contradicts the exact argmax assertion of Appendix A at c=1. Hence
c_dagger<1. In particular the exclusion of c>=1 is strengthened to a
strict gap between the last mixed boundary and one, without a numerical
estimate for that gap.

## 6. Transfer to actual APPT spectra

Here we invoke the credited original APPT results L and S, rather than
reprove their matrix statements. Let m<=n, m tend to infinity, alpha>1,
alpha/m tend to c_bar, and 3^alpha/(mn) tend to r_0(c_bar)>0. The scalar
argmax at the crossing contains at least:

    the pole class L=0;
    the bulk point (L,h)=(2,h_b(c_bar));
    an interior point (L_bar,h_bar).

S gives actual complex-density APPT nearoptimizers attaining every scalar
argmax and characterizes every nearoptimizer by distance to the full scalar
argmax, vanishing body-spread defect J and vanishing actual peak loss.
The resulting limiting empirical body laws, for the scaled centered body
eigenvalues used in S, are respectively

    delta_0,
    (1-h_b) delta_{-2h_b} + h_b delta_{2(1-h_b)},
    (1-h_bar) delta_{-L_bar h_bar}
                 +h_bar delta_{L_bar(1-h_bar)}.

These are pairwise distinct: the last two have positive atom weights and
different atom gaps 2 and L_bar in (0,2); neither is a point mass. Their
existence and the loss conditions pertain to genuine APPT matrices under
every global unitary, as in S. They can also be alternated along a dimension
sequence without changing the nearoptimal value. This does not assert that
these three laws exhaust all laws at the boundary: additional interior ties
are deliberately retained through the full argmax condition.

For interior ties the scalar P lies strictly between zero and one. The
two pure branches have P=0 and P=1. Thus their coincidence at the last
boundary is not captured by asserting only equality of the two pure values.
The complete value at that particular c still equals the pure envelope for
all r, while its crossing argmax contains additional spectral phases.

## Appendix A. Self-contained pure-envelope estimate for c >= 1

Put K=2c and, at a positive nonterminal width, k=cL in (0,K), u=K-k and
a(k)=2k^2/(3u). Define

    s(t)=exp(t)/(exp(t)-1)-1/t.

Direct differentiation gives q'=-sq and g'=s(1-q)>0. Moreover s(t)>1/2:
after multiplication by 2t(exp(t)-1), this is equivalent to

    H(t)=(t-2)exp(t)+t+2>0.

Here H(0)=H'(0)=0 and H''(t)=t exp(t)>0. Since

    g(t)=max_(0<=h<=1) log E exp[t(Bernoulli(h)-h)],

and each log moment-generating function is convex, g is convex. In
particular g(K)-g(k)>0 and g(K)-g(k)>=(K-k)g'(k).

Fix the crossing r=r_0=b(K)-1>0. Both width endpoints have value b(K).
For a positive nonterminal width, h=0 or h=1 has B=1,P<1, hence value
strictly below b(K). Suppose a global maximizer exists with 0<L<2. It
therefore has 0<h<1 and is a smooth interior stationary point after
maximizing h. The exact maximization is obtained by differentiating

    exp(-kh)[1+h(exp(k)-1)+r_0 exp(-a)].

Its interior maximizer is h=1/k-[1+r_0 exp(-a)]/(exp(k)-1), and its
logarithmic optimized value is

    g(k)+T(k),     T(k)=r_0 q(k)exp(-a(k))>0.

The second derivative at its h stationary point is negative; in particular
the optimizer formula holds smoothly in a neighborhood of this point.
The width stationary equation is

    g'(k)=T(k)[s(k)+a'(k)],
    a'(k)=2k(2K-k)/(3u^2).

The global value is at least b(K), so T>=g(K)-g(k)>=u g'(k). Substitution
and cancellation of T>0 give 1>=u[s(k)+a'(k)]. On the other hand,

    u[s+a'] > u/2+2(K^2-u^2)/(3u)
              = 2K^2/(3u)-u/6
              = K/2+(K-u)(4K+u)/(6u) > K/2.

This is impossible for K>=2. Consequently at the crossing for c>=1 there
is no global interior-width maximizer, including no interior tie, and the
argmax consists exactly of the two pure classes. Section 1 extends that
crossing statement to the complete all-r value and the strict-r argmax.

## Status

The scalar boundary theorem and its credited APPT transfer are complete
author arguments, pending independent ordinary review. They do not close
the no-islands or unique-boundary problem in 0<c<1. A floating-point
candidate boundary near 0.25967 is discovery information only and is not
used anywhere in this note.
