# Removing a positive population from the uncentered odd-composite Goldbach comparison

Let \(P\to\infty\) through the even integers; \(n\in I=[P/3,2P/3]\),
\(r=P-n,\ X=P/3,\ L=\log P,\ S(P)\) is the binary singular series.
Write \(\langle h,k\rangle=\sum_{n\in I}h(n)k(r)\),
\(V(n)=(\log n)1_{n\ {\rm prime}}\), \(G=\langle V,V\rangle\).
Use the [smooth midpoint theorem](../midpoint/Proof.md): with a nonincreasing
complementary transition \(f\) around \(1/2\), put
\[
 U(n)=(\log n)\sum_{d\mid n}\mu(d)f(\log_n d),\qquad
 J(n)=(V(n)-U(n))/2,\qquad {\cal F}(B)=\langle V,B\rangle-\langle B,B\rangle .
\]
Here \(\log_n d=\log d/\log n\). In particular \(G/4={\cal F}(J)+o(XS(P))\).
The weights used here are the actual ones, not squarefree Euler-model weights.

**Theorem.** Fix \(0<u<1/12\). Choose \(0<e\le .0004\) small enough that
\(7e<1/2-6u\), and choose the midpoint \(f\) identically one through
\(1/2-e\), zero starting at \(1/2+e\), smooth, compactly extended to negative
arguments, with \(f(x)+f(1-x)=1\) on \([0,1]\). Set
\[
  T(n)=\max(0,J(n))\,1_{P^-(n)\le P^u}.
\]
Then, uniformly in the target with these parameters fixed,
\[
 \langle U,T\rangle=o(XS(P)),\qquad
 \langle V,T\rangle-\langle J,T\rangle
       =\tfrac12\langle V,T\rangle+o(XS(P))\ge-o(XS(P)),           \tag{1}
\]
and
\[
 G/4={\cal F}(J-T)+\langle T,T\rangle+o(XS(P))
      \ \ge\ {\cal F}(J-T)-o(XS(P)).                              \tag{2}
\]
One may restrict \(T\) to any fixed set of ranks, e.g. precisely the
squarefree triprimes. The *entire* triprime midpoint weight is nonnegative,
including its nonconstant transition. One may instead take the
nonpositive part \(\min(J,0)\) on the same low-least-factor sector:
the correlation equality and (2) still hold, though the last inequality
in (1) is no longer asserted. These are separate choices: no nonnegativity
of the self-correlation of a *mixed-sign* weight is inferred.
Equations (1)–(2) assert no positive quantitative lower for
\(\langle V,T\rangle\) or \(\langle T,T\rangle\) by themselves.

## 1. Restrict to smooth functions of bounded-length prime lists

Let \(D(n)=L\sum_{d\mid n}\mu(d) f((\log d)/L)\).
The uniform Fourier-envelope proof of (6) of the midpoint theorem, with
\(|T|\le |J|\le (|U|+V)/2\), also gives
\(\sum_{n\in I}|(U(n)-D(n))T(r)|\ll_f XS(P)/L\).
That theorem's absolute estimate (5) applies also to \(|D(n)T(r)|\)
since \(D/L\) has a fixed Schwartz Fourier envelope. Thus we may temporarily
restrict the inputs \(r\) of \(T\) to \(P^-(r)>P^\alpha\), for any fixed
\(0<\alpha<u\), at a cost \(\ll_f XS(P)\alpha^{1/2}\).
Prime powers, other nonsquarefree \(r\), and \((r,P)>1\) on this restricted
set have \(o_\alpha(XS(P))\) cost by the elementary large-prime-square
and target-divisor counts in the same proof. As \(n=P-r\), no divisor of
\(n\) can share a prime with \(P\) on the retained set; we may impose
\((d,P)=1\) on the modulus. No independent coprimality of \(n\) and \(r\)
has been assumed.

Write the retained \(r=p_1\cdots p_j\) with strictly increasing primes.
We have \(j\le 1/\alpha\), \(P^\alpha<p_1\le P^u\) and only odd \(j\ge3\)
have nonzero \(T\). For fixed \(j\) and squarefree inputs,
\(J(r)/L=-(\log r)/(2L)\sum_{A\subseteq[j]}(-1)^{|A|}
 f(\sum_{i\in A}\log p_i/\log r)\).
This and its positive part are Lipschitz functions of the \(j\) normalized
logarithms on the central domain; constants may depend on \(\alpha,f\).
The positive-part map is itself 1-Lipschitz. There is no assumption of
a gap around zeros of \(J\), nor substitution of a step for the transition.

Mesh each prime coordinate independently in multiplicative intervals of
ratio \(1+L^{-B}\), split at the two exact least-prime cutoffs, and omit
boundary boxes at the physical endpoints \(r=P/3,2P/3\).
The discarded physical strips have total length \(O_\alpha(PL^{-B}+1)\).
Discard also sorted tuples having two primes in a single cell; their
physical support size is at most
\[
  P\sum_{p<s\le(1+L^{-B})p}\frac{1}{ps}
       \ll P L^{-B}\log\log(3P).
\]
Indeed the number of integers \(s>p\) in the indicated interval is at most
\(L^{-B}p\); a nonempty original pair has \(ps\le P\).
On both exclusions the cost is \(O_{\alpha,f,H}(PL^{-H})\) on choosing
\(B\) large, by Cauchy and standard divisor moments against
\(O_{\alpha,f}(L^2\tau(P-r))\). No error is paid per discarded box.
Approximate \(T(r)/L\) by its value at the lower endpoints in every
remaining box with uniform pointwise error \(O_{\alpha,f}(L^{-B})\);
the resulting total loss is again arbitrarily log-small.
These boxes are disjoint and their number \(L^{O_{\alpha,B}(1)}\).

In one such box put \(\ell=p_1,\ m=p_2\cdots p_j\). The remaining primes
are in disjoint cells; the normalized weight is a constant times the
convolution of the prime indicator in the \(\ell\)-cell with the
indicator on the integers \(m\) having exactly these specified prime
factors. This representation of \(m\) is unique. Enforce target-unit
conditions on each factor. Products in the box are entirely central.
Let \(C,M\) be the products of the **fine lower endpoints** for \(\ell,m\),
respectively (for \(\ell\) a single endpoint). The supports fit the
two dyads \([C,2C]\), \([M,2M]\) and \(MC\ge(1-o(1))P/3\) for
a retained nonempty box, so \(P\le 4MC\). The long coefficient is
bounded and otherwise arbitrary. Extra endpoint truncations of a prime
cell and removing target primes respect the short Siegel–Walfisz
condition: subtract endpoint PNT-in-progressions, remove at most
\(\omega(P)\) prohibited primes, and handle the extra unit mask in
the progression theorem in exactly the same way (with its allowed
divisor loss). The original arithmetic target in the residue is \(P\).

## 2. Complete modulus range for the signed transfer

We require the discrepancy against the reduced-residue mean of
the above convolution, summed against any 1-bounded coefficient on
\(d\le P^v,\ (d,P)=1\), where \(v=1/2+e\). It is \(O_A(PL^{-A})\)
for each fixed \(A\) and each box, with constants depending on the
fixed \(\alpha,u,e\). Here are the precise ranges.

* Put \(k=\log C/L\). At \(.002\le k\le u\), use
  [Fouvry (1987), Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf),
  with ambient \(x=4MC\asymp P\), short length \(C\).
  It takes arbitrary bounded modulus coefficients, a Siegel–Walfisz
  short sequence, and is uniform in \(|a|\le x\). Its two upper
  level exponents here are \((1+k)/2\) and \((4-6k)/7\);
  both exceed \(v\) by a fixed positive margin. End dyads shift
  exponents by \(o(1)\) only.
* When \(\alpha-o(1)\le k\le .002\), the same corollary covers
  \(d\le\sqrt P\), with a margin depending on \(\alpha\).
  On \(\sqrt P<d\le P^v\), apply the uniform macroscopic-residue
  extension of [Fouvry–Radziwill's dispersion proof](https://arxiv.org/pdf/1811.08672)
  for a prime short coefficient, as proved in
  [§C of the polynomial-survivor estimate](../PanPolynomiallyRoughSurvivors.md)
  using [the macroscopic-shift dispersion lemma](../PanUnbalancedCofactor.md).
  This is *not* the unmodified theorem restricting \(|a|\le MC/3\).
  For \(w=\log d/L\in[1/2,v]\), its two required strict inequalities
  \(36k+33w<17,\ 15(k+w)<8\) hold even at \((.002,.5004)\).
  The modulus scale exceeds \(C\) and \(M/d\) grows by a fixed power.
  The small factor is at least \(P^{\alpha-o(1)}\), exceeding every
  \(\exp(KL/\log L)\) eventually; its prime interval has the required
  short-variable distribution in the sense of bounds relative to \(C\),
  not a relative error against the mass of one fine cell.

If a cell crosses .002, split it there. The comparison applies to the
actual coefficient \(\mu(d)f((\log d)/L)\) divided by a fixed bound.
Take arbitrary additional log savings to pay the fine boxes and the
two external \(O(L)\) factors. To be explicit, the main term per box
is obtained by replacing \(1_{r\equiv P\bmod d}\) with
\(1_{(r,d)=1}/\phi(d)\). After recombination this is
\[
 L\sum_{r\in I} T_{\rm box}(r)
       \sum_{\substack{d\ge1\\(d,Pr)=1}}\frac{\mu(d)}{\phi(d)}
                         f((\log d)/L),                            \tag{3}
\]
where \(T_{\rm box}\) includes the outer logarithmic normalization and
the restrictions already imposed on \(r\).

Uniformly in \(h\le P^2\) and \(Z\in[P^{.49},P]\),
\(\sum_{d\le Z,(d,h)=1}\mu(d)/\phi(d)\ll_A L^{-A}\).
One direct proof is convolution with \(\mu(n)/n\): the local auxiliary
coefficient at \(p^\nu,\nu\ge1\), is \(p^{-\nu}\) if \(p\mid h\),
and \(-p^{-\nu}/(p-1)\) otherwise. This follows by dividing the local
factor \(1-1_{p\nmid h}z/(p-1)\) by \(1-z/p\).
The absolute reciprocal-scale mass of this auxiliary convolution up to
infinity costs \(O(\log\log(3P))\) (bounded convergent factor away
from \(h\)). At powers weighted by \(n^{1/\log L}\) the mass is at most
\((\log L)^{O(1)}\): the unrestricted factors away from \(h\) converge
uniformly, and the Euler product for the primes of \(h\) is bounded
by splitting at \(p=L\) as in the midpoint theorem. Therefore auxiliary
integers \(>\sqrt Z\) cost arbitrary log savings by Rankin, even with
a trivial inner harmonic sum \(O(L)\). For smaller ones apply the
classical PNT harmonic Möbius bound at \(Z/m\ge\sqrt Z\).
Integrate sharp cutoffs \(Z=P^t\) against \(-f'(t)\) at
\(t\in[1/2-e,1/2+e]\). The inner expression in (3) is thus
\(O_{A,f}(L^{-A})\) uniformly even as \(h=Pr\) varies over the
entire physical support. The outer normalized absolute weight is
\(O_{\alpha,f}(PL)\) and (3) is negligible. The case of the endpoint
\(r\in\{P/3,2P/3\}\) was already covered by the physical strip estimate.

We have shown \(\limsup_{P\to\infty}|\langle U,T\rangle|/(XS(P))
 \ll_f\alpha^{1/2}\) for every fixed sufficiently small \(\alpha>0\).
Let \(\alpha\downarrow0\); the estimate with this power was taken **before**
the fixed-\(\alpha\) meshing constants were introduced. This proves the
first equality in (1). Since \(2J=V-U\), all other claims in (1)–(2)
follow from bilinearity and symmetry:
\({\cal F}(J)-{\cal F}(J-T)=\langle U,T\rangle+\langle T,T\rangle\).
For \(T\) of one sign the last product is termwise nonnegative.
In particular, on the restricted rank-three population the equality
pairs the actual \(1\times3\) contribution with its complete *signed*
opponent; it does not bound the \(3\times3\) contribution in isolation.

**Example and limits.** Take \(u=.082,e=.0004\). This includes the
whole positive transition as well as all triprimes
\(\ell p q\) with \(P^{.002}\le\ell\le P^{.082}\) and
\(p,q\le P^{.4994}\); on the latter \(J=\log(\ell pq)\) for
large \(P\). The surviving unsuppressed positive composites can still have
three comparable factors around \(P^{1/3}\). No equidistribution
theorem for such a short prime factor at level \(P^{1/2+e}\) with these
arbitrary moduli is being invoked. Negative profiles remain if one
removes the positive class. There is no proof that the remaining
\({\cal F}(J-T)\) is nonnegative or that \(G>0\).

**Dated comparison.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) treats weighted Type I and a separate rough benchmark; [Arneth, October 19 v1](https://zenodo.org/records/23477014) uses a different cubic prime minorant. Here the actual odd-composite profile can be removed from the specified raw comparison after preserving its signed coupling and its nonnegative self term. Neither the underlying dispersion nor the missing balanced prime versus composite estimate is claimed new or resolved here.
