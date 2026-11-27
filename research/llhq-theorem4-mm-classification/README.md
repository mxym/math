# The Li–Li–Helleseth–Qu Theorem 4 family is entirely in \(\mathcal M^\#\)

**Theorem.** Every function in Theorem 4 of Li, Li, Helleseth and Qu
(JCTA, 2023) is linearly equivalent to a Maiorana–McFarland bent
function. In particular their family contains no examples outside the
completed Maiorana–McFarland class, in any of its dimensions.

This is an answer to the explicit class-membership question after their
Theorem 4, not a claim of new bentness. The 2023 paper proves bentness,
reports membership experimentally at \(m=6\), and leaves open whether a
larger \(m=3k\) yields an example outside \(\mathcal M^\#\). See the
[version of record](https://doi.org/10.1016/j.jcta.2023.105779) and
[author-posted manuscript](https://www.researchgate.net/publication/374351274_Further_investigations_on_permutation_based_constructions_of_bent_functions),
Section IV, Theorem 4 (p. 32), discussion (p. 34), Table I (p. 35).
This question is separate from Conjectures 1 and 2 of that paper.

## Proof

Let \(k\ge1,\ q=2^k,\ E=\mathbb F_{q^3}\), and let
\(\operatorname{tr}\) and \(\operatorname{tr}_q\) be the absolute
traces on \(E\) and \(\mathbb F_q\), respectively. The original family
on \(E^2\), with \(m=3k\), is
\[
 f(x,y)=\operatorname{tr}\!\left(y^{q+1}+
        (x+x^{q+1}+x^{q^2+1})y\right).
\]
Use the relative trace \(\tau(x)=x+x^q+x^{q^2}\) and its kernel
\(U\). For \(s\in\mathbb F_q\) one has \(\tau(s)=s\), because the
extension degree is odd. Thus \(E=\mathbb F_q\oplus U\), with
\(\dim_{\mathbb F_q}U=2\). Write \(x=s+u,\ y=t+v\) in that decomposition.
The absolute trace pairings on \(\mathbb F_q\) and \(U\) are both
nondegenerate: the two summands are orthogonal for
\(\operatorname{tr}(a b)\), since
\(\operatorname{tr}(s u)=\operatorname{tr}_q(s\tau(u))=0\), and the full
trace pairing on \(E\) is nondegenerate. Indeed, the absolute trace is
a nonzero linear functional (its defining polynomial is nonzero of
degree less than \(|E|\)), and multiplication by any nonzero \(a\) is
bijective. Restricting to either of the two complementary orthogonal
blocks therefore leaves a nondegenerate form.

The coefficient of \(y\) in the original formula simplifies exactly:
\[
 \begin{aligned}
 x+x^{q+1}+x^{q^2+1}
   &=x+x(x^q+x^{q^2})=x^2+(s+1)x\\
   &=s+u^2+(s+1)u.
 \end{aligned}
\]
Here \(u^2+(s+1)u\in U\), because \(\tau(u^2)=\tau(u)^2\).
Also
\(\tau((t+v)^{q+1})=t^2+\tau(v^{q+1})\):
the two cross terms are \(t v^q,t v\), both of relative trace zero.
Using the orthogonal split, taking absolute traces, and using
\(\operatorname{tr}_q(t^2)=\operatorname{tr}_q(t)\) now yields
\[
 f(s+u,t+v)=
 \operatorname{tr}_q\bigl(t(s+1)\bigr)
 +\operatorname{tr}\bigl(u(\sqrt v+(s+1)v)\bigr)
 +\operatorname{tr}(v^{q+1}).
 \tag{1}
\]
The square root denotes the unique square root in \(E\).
The second term uses
\(\operatorname{tr}(v u^2)=\operatorname{tr}(\sqrt v\,u)\).
Additionally \(\sqrt v\in U\) for \(v\in U\), since
\(\tau(\sqrt v)^2=\tau(v)=0\).

In (1) choose \((t,u)\) as the first block and \((s,v)\) as the
second block; each has binary dimension \(3k\). With the trace-dual
bases established above, the pairing of these two blocks is a dot
product. The associated permutation of the second block is
\[
 \Pi(s,v)=(s+1,\sqrt v+(s+1)v).
\]
For \(c=s+1=0\), the second component plainly permutes \(U\). For
\(c\ne0\), its kernel on \(U\) consists of solutions of
\(\sqrt v=cv\); after squaring, any nonzero solution would be
\(v=c^{-2}\in\mathbb F_q^\times\), which is not in \(U\).
The map is binary linear on \(U\) for fixed \(c\), hence is
bijective there in both cases. Thus \(\Pi\) is a permutation.
Formula (1) is precisely Maiorana–McFarland form with offset
\(\operatorname{tr}(v^{q+1})\) on the second block. The decomposition
and reordering are invertible binary linear changes, proving the
claimed membership for every \(k\ge1\).

For completeness, for frequencies \(a,d\in E\) set \(A=\tau(a)\),
\(D=\tau(d)\), \(a_0=a+A\), and \(d_0=d+D\). The Walsh sum of the
original expression at \((a,d)\), using
\((-1)^{\operatorname{tr}(ax+dy)}\), is
\[
 q^3\,(-1)^{\operatorname{tr}_q(A(D+1))+
                    \operatorname{tr}(v^{q+1}+d_0v)},
 \qquad \sqrt v+Dv=a_0,\quad v\in U.
\]
Indeed, character sums over \(t,u\) in (1) force \(s+1=D\) and
the displayed equation in \(v\), which is uniquely solvable as above.
This recovers the known bentness as well.

## Verification and scope

    python3 verify_symbolic.py
    g++ -O3 -std=c++17 -Wall -Wextra verify_finite.cpp -o /tmp/theorem4-mm-verify
    /tmp/theorem4-mm-verify

The first script verifies the relative-trace identity in a formal
binary polynomial ring before passing to the absolute trace.
The second uses polynomial-basis finite fields, independently
checks the absolute identity and the resulting permutation, and
runs a full Walsh transform of the original function in four
dimensions \(6,12,18,24\). It checks every coefficient and sign
against the formula above. Both reject an exponent-changed
identity as a negative control. These calculations are independent
finite checks of the formula; the proof is uniform and not based
on exhaustive tests.

The literature search on the 2023 DOI, its Theorem 4/relative-trace
formula, and searches for completed Maiorana–McFarland membership
through 2026-11-27 did not locate a prior all-\(k\) answer to this
question. The 2026 related analysis by [Bartoli and Timpanella](https://doi.org/10.1007/s10623-026-01815-z)
treats a different family obtained by composing with a
relative-trace-based permutation, not this Theorem 4.
No novelty is claimed for the classical Maiorana–McFarland
construction or for the already known bentness of the source
family.
