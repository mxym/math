# A reverse Type I deletion in the giant-prime remainder

Let \(N\) be a prescribed sufficiently large even integer, \(L=\log N\),
\(\ell=\log L\), \(S=\exp(\ell^4)\), and \(B=N/S\). Let \(J\) be any
interval inside a fixed compact interval \(J_0\Subset(0,1)\). For an actual
prime \(p\in NJ\) put \(y=N-p\), \(T_y=y/B\), and
\[
 Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d).
\]
For any interval \(I\subset[\sqrt N S^2,B]\), let
\[
 C_I=\sum_{p\in NJ\,\mathrm{prime}}\log p
       \sum_{\substack{r\in I\,\mathrm{prime}\\rm=y}}\log r\,Q_y(m).
\]
This is part of the original [giant-prime divisor remainder](../giant_prime_divisor_remainder/Proof.md), with no parity twist or change of its short cutoff.

**Theorem.** For any fixed \(A>0\), one can choose \(D=D(A)\) so that,
with \(Q=\sqrt N/L^D\), uniformly in \(I,J\),
\[
 C_I=\sum_{p\in NJ\,\mathrm{prime}}\log p
       \sum_{\substack{akm=y,\ ak\in I\\am>Q}}\mu(a)\log k\,Q_y(m)
       +O_{A,J_0}(NL^{-A}).                                            \tag{1}
\]
In the expanded sum \(a>1\) because \(m<Q\); the factor \(k=1\) has zero
logarithmic weight. Thus the expanded \(ak\)'s are composite integers,
not original giant prime labels.

Alternatively put \(z=\exp(\ell^2)\), \(V=S^{1/3}\), and
\(\lambda_{>V}(k)=\sum_{j\mid k,\ j>V}\Lambda(j)\). Both genuine rough
Vaughan Type I terms on the giant slot may be deleted:
\[
 C_I=\sum_{p\in NJ\,\mathrm{prime}}\log p
       \sum_{\substack{akm=y,\ ak\in I\\a>V,\ P^-(ak)>z}}
           \mu(a)\lambda_{>V}(k)Q_y(m)+O_{A,J_0}(NL^{-A}).             \tag{2}
\]
Neither statement restricts \(\operatorname{rad}(N)\). The use of an
interval \(I\), rather than an arbitrary mask on the giant prime, is
essential to the progression step below. The remaining signed sums
in (1) and (2) are not bounded here; in particular neither is a
Goldbach lower bound.

For related reverse decompositions, see
[the tagged semiprime double residual](../ReverseVaughanDoubleResidual.md)
and [the asymmetric smooth-residue residual](../AsymmetricVaughanSmoothResidual.md).
The former starts with an independently tagged semiprime source;
the latter uses a different squarefree weighted residue estimate.
Here the untagged \(Q_y(m)\) comes from the literal giant-prime
remainder, and the progression input is only ordinary prime BV.

## 1. A uniform harmonic on the actual quotient

For a target unit \(H\le N^{O(1)}\), a dyadic scale \(M\gg_{J_0} S\), an
interval \(J_M\subset[M,2M]\cap[T_y,\infty)\), and a weight \(F\) of
supremum plus total variation \(O(L^C)\) there, we claim
\[
 \sum_{\substack{m\in J_M\\(m,N)=1}}Q_y(m)\frac{F(m)}{\varphi(Hm)}
       \ll_{A,C,J_0}\frac{L^{-A}}{\varphi(H)}.                         \tag{3}
\]
We use two signed harmonics: the coefficients
\(\varphi(H)\mu(d)1_{(d,N)=1}/\varphi(Hd)\) and \(\mu(d)g_H(d)\), where
\(g_H\) is multiplicative on squarefree inputs and
\[
 g_H(q)=\begin{cases}
 0,&q\mid N,\\
 1/q,&q\mid H,\ q\nmid N,\\
 q/(q^2-q+1),&q\nmid HN.
 \end{cases}                                                        \tag{4}
\]
Both complete harmonics vanish, and both tails starting at \(X\gg S^c\)
are \(O_A(L^{-A})\) for any fixed \(c>0\). Indeed the series for \(d\)
times either coefficient is \(\zeta(s)^{-1}G(s)\). The extra Euler factor
is \((1-q^{-s})^{-1}\) at \(q\mid N\), is 1 at \(q\mid H\), and elsewhere
has numerator \(1-(1+O(1/q))q^{-s}\) over \(1-q^{-s}\). At
\(\sigma=1-1/(10\ell)\) the absolute coefficient norm of \(G\) is
\(\ell^{O(1)}\): the non-target product converges uniformly, and in the
target product split at \(q=L^2\), use prime reciprocals below the split
and at most \(O(L)\) primes above. Splitting the convolution with \(\mu\)
at \(\sqrt X\), classical Mertens on its first part and Rankin on its
second give a relative summatory bound
\(\ell^{O(1)}(e^{-c_1\sqrt{\log X}}+X^{-(1-\sigma)/2})\). Partial
summation gives the tails, and the zero of \(\zeta(s)^{-1}\) at 1 gives
the complete values. Both assertions are uniform over real endpoints.

Open \(Q_y\) in (3). For \(d>\sqrt S\) fix \(n=m/d\), use the first
harmonic with \(Hn\) and partial summation against \(F(nd)\), then sum
\(n\) using \(\varphi(Hn)\ge\varphi(H)\varphi(n)\).
For \(d\le\sqrt S\), the exact opening is
\[
 \frac1{\varphi(Hdn)}=\frac1{\varphi(Hd)n}
     \sum_{\substack{e\mid n\\(e,Hd)=1}}\frac{\mu^2(e)}{\varphi(e)}.
\]
Set \(n=ej\). In any interval of scale \(X\), the count of positive integer units \(j\)
at \(N\) equals \(\varphi(N)/N\) times its length, with error
\(O(X^\sigma\prod_{q\mid N}(1+q^{-\sigma}))\). This follows by
inclusion–exclusion over divisors of \(\operatorname{rad}(N)\): split
at a fixed multiple of \(X\), bounding the floors and the uncounted
main tails by the same Rankin sum. Thus no \(\tau(N)\) loss at scale
\(S\) is needed. Partial summation at \(X\asymp M/(de)\), with the
factor \(1/e\), bounds the total error of the \(e\)-opening by
\[
 \frac{L^{O(1)}(M/d)^{\sigma-1}}{\varphi(Hd)}
        \sum_{e\ge1}\frac1{e^\sigma\varphi(e)}.
\]
It is arbitrarily log-small since \(M/d\gg\sqrt S\); the bounded-scale
case uses the same bound with \(X\) replaced by \(\max(1,X)\). The
omitted \(e\)-main tail beyond \(2M/d\) is also negligible. The main for
this fixed \(d\) is
\[
 \frac{\varphi(N)}{N\varphi(Hd)}
       \prod_{q\nmid HdN}\left(1+\frac1{q(q-1)}\right)
         \int_{J_M} F(t)\,\frac{dt}{t}.
\]
Relative to \(d=1\) it is exactly multiplied by \(g_H(d)\) on squarefree
\(d\). In particular, for \(q\nmid HN\) the conditional weight of
\(q\mid m\) is \((q-1)^{-1}/(1+[q(q-1)]^{-1})\), not \(1/(q-1)\);
for \(q\mid H\) it is \(1/q\). The second signed harmonic at \(\sqrt S\)
now pays the small \(d\)'s. This proves (3), including all shared
factors of \(H,d,n\). Dyadic summation costs only more logarithms.

## 2. The reverse progression step

Discard central true primes \(p\mid N\) at \(N^{o(1)}\) cost by fixed
divisor powers. Every divisor of \(y\) is now a unit at \(N\).
Replacing the genuine \(r\) by \(\Lambda(r)\) adds only proper prime
powers; counting multiples of those \(r\gg\sqrt N\), with the same
divisor envelope, costs \(N^{3/4+o(1)}\). The same applies after imposing
true \(r\)-roughness.

In \(\Lambda(r)=\sum_{a\mid r}\mu(a)\log(r/a)\) retain first the terms
\(am\le Q\). The actual prime \(p\) lies in the reduced class \(N\pmod{am}\),
including when \(a,m\) share a prime. For fixed \(a,m,d\mid m\) the
restriction \(r\in I\) makes an interval in \(p\) and \(d<T_y\) imposes
\(p<N-Bd\). The genuine log weight \(\log(y/(am))\) has sup plus
variation \(O(L)\) there. Use maximal-prefix
[Bombieri–Vinogradov](https://www.numdam.org/item/10.5802/jtnb.1098/) with
fixed divisor-power multiplicity at \(am\le Q\); the proper \(p\) powers
in a von Mangoldt formulation are negligible. Divisor multiplicities
are absorbed by truncating them at a log power, using a stronger BV
reserve there, and applying the trivial individual bound plus fixed
divisor moments on the complement.

In the resulting integral fix \(y=N-p\). The interval for \(m\) is
specified by \(y/m\in I\) and \(m\le Q/a\), hence lies in \(m\ge T_y\),
and is independent of the short divisor \(d\) after forming \(Q_y(m)\).
Apply (3) with \(H=a\) and \(F(m)=\log(y/(am))\). Sum \(a\) and dyadic
\(m\) ranges at log-power cost. This deletes the entire genuine below-root
branch and proves (1).

## 3. The genuine rough Vaughan variant

Apply [Vaughan’s identity, as in Sedunova §2](https://arxiv.org/abs/1705.06660), to \(\Lambda(r)1_{P^-(r)>z}\), with both cutoffs \(V\).
The small \(\Lambda_{\le V}\) vanishes in \(I\). The two Type I terms
\(\mu_{\le V}*\log\) and \(-\mu_{\le V}*\Lambda_{\le V}*1\) have \(r=ak\),
\(a\le V^2\), and free \(k\) of weight \(\log k\) or 1. The grouped
coefficients are \(O(L)\). Keep \(a\) genuinely \(z\)-rough and open
\(k\)-roughness by successive Bonferroni truncations near
\(K=\lfloor C_A\ell/\log(2\ell)\rfloor\). The selected squarefree
\(c\mid k\) is at most \(z^{K+1}=S^{o(1)}\). Target primes can be omitted;
\(c\) may share factors with \(m\). The physical modulus is \(amc\)
(not an lcm), and its upper bound \(\sqrt N S^{-2}V^2S^{o(1)}\) retains
the full BV reserve. The positive truncation error, with
\(|Q_y(m)|\le\tau(m)\), is paid by the same weighted BV and the
factorial bound \((O(\log\ell))^{K+1}/(K+1)!\) for the reciprocal
\(1/\varphi(c)\) sum. Choose \(C_A\) to absorb the remaining fixed log
powers. In each retained principal use (3) with \(H=ac\); the free log
is still \(\log(y/(am))\), not \(\log(y/(amc))\). This pays both Type I
terms. The genuine residual \(\mu_{>V}*\Lambda_{>V}*1\) gives exactly
(2). The argument is a switch on the giant slot, not an evaluation of
a prime or Möbius progression in the remaining long variable.

## Finite replay

Run `python -O -B check_local.py` for the exact local totient, prime-factor,
Vaughan, and product-modulus identities. The replay does not test the
analytic estimates or certify the remaining signed sums.
