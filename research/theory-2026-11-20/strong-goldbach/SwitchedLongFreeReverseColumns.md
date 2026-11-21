# Whole reflected branches after switching truly free reverse factors

Keep the setup of [WholeReverseColumns.md](WholeReverseColumns.md): \(N=2x\), \(I=(x/2,x]\), \(L=\log x\), \(s\sim S=x^\alpha\) is prime with \(.10\le\alpha\le.14\), and \((N,s)=1\). Put \(U=x^{.454}, V=x^{.004}, Q=x^{.466}\), and
\[
 C_m^{\rm hi}(m)=\sum_{\substack{d\ell\mid m\\d>U,\ \ell>V,\ d\ell>Q}}\mu(d)\Lambda(\ell).
\]
Use the fixed reverse cutoffs \(U_q=x^{.070},V_q=x^{.010},E=x^{.080}\) (valid simultaneously for all \(d>U\) in [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md)). The literal row is
\[
 \sum_{\substack{s\ {\rm prime},\ r>U_q,\ k>V_q,\ rk>E,\ j\ge1\\
                 n=s r k j\in I,\ (n,N)=1}}
       \frac{\kappa_s W_s(rkj)}{\log(rkj)}
         C_m^{\rm hi}(N-n)\,\mu(r)\Lambda(k).
\tag{1}
\]
Use the exact \(W_s(q)=K_{P_3}(sq)\) at its semiprime formula, or the stated smooth product versions. Independent additional intervals on \(r,k,j\) and \(A=s r k\) are allowed, in particular original \(A\) arbitrarily large. Do not insert a new cut on \(d\ell\), or a product mask \(d\ell A\), before the whole reflected reassembly.

Fix \(\delta>0\), put \(B=x^{1/2+\delta}\) and \(\mu_2=\mu*\mu\), and define
\[
 P_B(r)=-\!\!\sum_{\substack{t b=r\\b>B}}\mu_2(t),\qquad
 H_B(k)=\!\!\sum_{\substack{t b=k\\b>B}}
                  \{\mu(t)\log b-(\mu*\Lambda)(t)\}.
\tag{2}
\]
Then uniformly in the indicated restrictions, for every fixed \(D>0\),
\[
 (1)\text{ with }\mu(r)\Lambda(k)
   =(1)\text{ with }(\mu(r)-P_B(r))(\Lambda(k)-H_B(k))
                    +O_{D,\delta}(xL^{-D}).
\tag{3}
\]
These are precisely the free-factor pieces of reciprocal Heath--Brown identities on the true quotient factors \(r,k\); each allows the entire high reflected branch. The modulus in the proof is **not** the original \(A\). Even if \(A\) is a fixed fraction of \(x\), the switched modulus is below \(x^{1/2-\delta}\).

## 1. Exact origin of the two pieces

Let \(\mathbf1(n)=1\) and \(\delta_1=1_{n=1}\) be the Dirichlet unit. Put \(u=\mu1_{\le x^{1/10}}\), \(D_0=u*\mathbf1\), \(H=\delta_1-D_0\), where \(H\) has support \(>x^{1/10}\). For \(J=10\),
\[
 \mu*(\delta_1-H^{*J})
  =\sum_{i=1}^J(-1)^{i-1}\binom Ji u^{*i}*\mathbf1^{*(i-1)}
\tag{4}
\]
equals \(\mu\) on inputs \(\le x\). Convolving with \(\log\) gives \(\Lambda\) on the same inputs. Here \(r,k\le x/S\). At any physical summand at most one free slot from either identity exceeds \(B\), since \(B^2>x\). Its complementary product \(t\le x/B\) is below \(x^{.9}\).

For the \(\mu\) identity, mark one of the \(i-1\) free slots \(\mathbf1\) of value \(b>B\). With \(P(z)=1-(1-z)^J\) the combined remaining coefficient on \(t\) is
\[
 u^{*2}\frac{D_0P'(D_0)-P(D_0)}{D_0^2}
   =\mu_2*\{J D_0*H^{*(J-1)}-\delta_1+H^{*J}\}.
\tag{5}
\]
Products/powers here denote Dirichlet convolution; the left quotient is a polynomial and \(D_0(1)=1\). Indeed marking multiplies the \(i\)-th coefficient by \(i-1\), and \(u^{*i}*\mathbf1^{*(i-2)}=u^{*2}*D_0^{*(i-2)}\), for \(i\ge2\). The division gives \(\mu_2\), because \(u=D_0*\mu\). Both \(H\)-terms vanish on \(t\le x/B\); (5) is exactly \(-\mu_2(t)\). This derives the extended range for \(t\), possibly much larger than the \(u\)-cutoff, from support, not by dropping each \(u\)-cutoff. This is a broader-support variant of the \(\mu_2\) evaluation used separately in [HeathBrownLongFreeNotch.md](HeathBrownLongFreeNotch.md).

For the \(\Lambda\) identity, marking its \(\log\) slot leaves (4), so gives \(\mu(t)\log b\). Marking an ordinary free slot leaves (5) convolved with \(\log\), hence \(-(\mu_2*\log)(t)=-(\mu*\Lambda)(t)\). This proves (2) literally, even for nonsquarefree \(r,k\). Both marked pieces cannot occur at the same \(q=rkj\): otherwise \(rk>B^2>x\). Thus (3) removes exactly \(P_B(r)\Lambda(k)\) and \(\mu(r)H_B(k)\), with no intersection term.

## 2. Switch and exact reduced progression

In the first removed term write \(r=t b\), \(v=s k t j\); in the second write \(k=t b\), \(v=s r t j\). For either fixed tuple of four other labels,
\[
                    m=N-vb,\qquad v=(N-m)/b<x^{1/2-\delta}.
\tag{6}
\]
The central range, \(b>B\), \(rk>E\), and the original \(r,k,j,srk\) intervals are each intervals in \(b\) or outer conditions. Thus \(m\) ranges over one interval in \([x,3x/2]\), in the true progression \(m\equiv N\bmod v\). The physical \((n,N)=1\) forces \((v,N)=1\); for these \(v\), the remaining restriction is exactly \((m,N)=1\), which also forces \((b,N)=1\). Nonunit \(v\) give no terms. No squarefreeness is added.

The physical weight for fixed labels, including the \(\log b\) term when present, is of log-power sup norm and variation: \(q=(N-m)/s\asymp x/S\) and \(b=(N-m)/v\) make these logarithms one-variable smooth functions on the interval. The number of label tuples over a fixed \(v\) is \(\le\tau_4(v)\), and the outer arithmetic weights are bounded by \(L^C\tau_2(v)^C\), since \(|\mu_2(t)|\le\tau_2(t)\), \(|(\mu*\Lambda)(t)|\le\log t\), \(\Lambda(k)\le\log k\), and analogous factors depending on \(r\) are bounded. Intervals cut in \(b\) therefore do not require counting all *original* \(A\) at fixed \(v\).

## 3. Uniform whole high reflected bound at the switched modulus

Let \(\Delta(v)\) denote the maximal ordinary prefix discrepancy of \(\Lambda(m)\) from the length divided by \(\phi(v)\) on the reduced class \(m\equiv N\bmod v\). Restricting to \((m,N)=1\) costs negligibly in our total: the omitted values with \(\Lambda(m)\ne0\) are prime powers of primes dividing \(N\), at most \(O(L^2)\) such \(m\). Each has at most \(\tau_2(N-m)\) switched moduli, each with the above divisor-power multiplicity, so their total is \(x^{o(1)}\). The case \(m=N\) is absent.

Reassemble \(C_m^{\rm hi}\) at each physical \(m\) before applying any product cutoff:
\[
 C_m^{\rm hi}(m)=\Lambda(m)-(\mu_{\le U}*\log)(m)
       +(\mu_{\le U}*\Lambda_{\le V}*\mathbf1)(m)
       -\!\!\sum_{\substack{d>U,\ \ell>V\\d\ell\mid m,\ d\ell\le Q}}
                         \mu(d)\Lambda(\ell).
\tag{7}
\]
Every short divisor \(a\le Q\) in the last three pieces must be coprime to \(vN\). With \(m=a h\), expand \((h,N)=1\) over \(f\mid(h,N)\); then \(a h\equiv N\bmod v\) and \(f\mid h\) give a single reduced class for \(h/f\bmod v\). The resulting principal density in \(m\) is \(\phi(N)/(N a v)\), and the interval remainder is \(O(\tau_2(N))\) per \(a\), before log weights. This uses the true mask on \(N\), not just units modulo \(v\). For the first piece retain the exact \(\log(m/a)=\log m-\log a\), using the log variation in \(m\). Thus all CRT floors cost \(Q x^{o(1)}\) per \(v\) and \(x^{.966-\delta+o(1)}\) after the switched moduli and their multiplicities.

For \(F=vN\le x^{O(1)}\), the finite coprime Mertens identities (6) of the [whole-columns proof](WholeReverseColumns.md) give, uniformly,
\[
 \sum_{\substack{a\le U\\(a,F)=1}}\frac{\mu(a)\log(m/a)}a
     =\frac{F}{\phi(F)}+O_D(L^{-D}),\qquad
 \sum_{\substack{a\le U\\(a,F)=1}}\frac{\mu(a)}a=O_D(L^{-D}).
\tag{8}
\]
Their log reserve also applies to harmonic intervals starting at \(U\); in the last piece of (7) a nonempty \(d\)-range always starts there. The first mean of the short pieces in (7) is thus exactly \(-1/\phi(v)\) in the density, since \((v,N)=1\). This matches the actual \(\Lambda(m)\) main. The other two short means are \(O_D((x/v)L^{-D})\) by (8) and the harmonic \(\Lambda\)-sum over \(\ell\), with arbitrary log reserve. On any switched interval the total is therefore bounded by
\[
              2\Delta(v)+O_D\{(x/v)L^{-D}+Q x^{o(1)}\},
\]
apart from the excluded powers already paid. The bound holds on all subintervals needed for the partial summation of §2.

Ordinary maximal Bombieri--Vinogradov with divisor weights gives \(O_D(xL^{-D})\) for the sum of these \(\Delta(v)\) up through \(x^{1/2-\delta}\), uniformly in the actual \(N\bmod v\). The weighting uses Cauchy interpolation from the unweighted maximal estimate with the trivial log-weighted progression count and divisor harmonic moments, as in the previous note. These harmonic moments also absorb the \(x/v\) terms, and all floors were counted above. This proves (3) at the exact \(\kappa_s W_s(q)/\log q\) normalization. No replacement of \(k\) by primes or external change of prime-distribution scale is needed.

There is also an exact support improvement for the *new combined coefficients*, not a claim of cancellation on the corresponding original arithmetic subfamily alone. If \(r=P u\) with an actual prime \(P>B\), then \(P\nmid u\), \(u<B\), and the divisors \(b\mid r\) above \(B\) are exactly the multiples of \(P\). Hence
\[
 P_B(Pu)=-\sum_{t\mid u}\mu_2(t)=-\mu(u)=\mu(Pu).
\]
Similarly for \(k=P u\), the two sums in \(H_B\) are
\[
 \sum_{t\mid u}\mu(t)\log(Pu/t)
     -\sum_{t\mid u}(\mu*\Lambda)(t)
   =(\log P)1_{u=1}+\Lambda(u)-\Lambda(u)=\Lambda(Pu).
\]
Thus both remaining coefficients in (3) are literally supported on integers whose largest actual prime is \(\le B\). The restriction follows crucially from the long **free** slots including composite divisors \(b\); it would be false reasoning to apply the switched BV proof after adding a primality condition to that free slot.

This kills every such truly long free slot in the exact reverse expansions, even in unstructured original large \(A\) and without a convenient-factor condition. Apply it first on the full row, before any further division by coupled product masks. It does not bound the remaining actual centered coefficients in (3), whose free variables are all shorter, the full semiprime discrepancy, or binary Goldbach.

[Chan's November 2026 preprint, Appendix E](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also switches to direct progression estimates in long-factor charts of its sieve construction. Here the long factor belongs to either of the original reverse quotient coefficients, and the switched progression is for the reassembled reflected high Vaughan term. The explicit subtractions in (2) retain the original coupled support and leave the new coefficients with the stated smooth support. No priority claim for divisor switching or the truncated-inverse identity is made.
