# A flat-slope polynomial removes every prescribed bounded reflected rank

Keep the original \(C,W_s,U,V,Q_0,H\), adjusted \(D_B\), actual quotient families \(\mathcal Q_1,\mathcal Q_2\), and physical fixed-target row of [AdjustedLowRankAbsorption.md](AdjustedLowRankAbsorption.md). In particular \(D_B(q)/\log q=i>0\) **exactly** on \(\mathcal Q_i\), and all its \(q\)-prime factors exceed \(x^{.010}\). This extends rank seven to an **arbitrary fixed** rank bound, including repeated small factors. It does not assert uniformity in the rank.

Fix \(R_0\ge2\); take odd \(j\ge\max(3,R_0-1)\), and put
\[
 b_j=\frac{2^{j-1}}j,\qquad P_j(t)=(t-\tfrac12)-b_j(t-\tfrac12)^j,
 \qquad P_j(0)=-\tfrac12+\tfrac1{2j}.
\tag{1}
\]
Thus \(P_j(1-t)=-P_j(t)\), \(P_j(1/2)=0\), and \(P'_j(0)=0\). Set \(\epsilon_0=1/(200R_0)\), take any fixed \(0<\epsilon<\epsilon_0\), \(Z=x^\epsilon\), and use \(S_U,G\) of the low-rank note, now with \(f_\rho(u)=1\) for \(0\le u\le\rho\), \(f_\rho(u)=((1-u)/(1-\rho))^{R_0-1}\) for \(\rho<u<1\), and zero for \(u\ge1\). Here \(0<\rho<1/2\). Define the exact reflected weight
\[
 E_j(m)=C(m)+\log m\left\{\frac{S_U(m)}2
       -\sum_{\substack{d\mid m\\d\le U}}\mu(d)P_j(\log d/\log m)
       +\left(P_j(0)-\tfrac12\right)G(m)\right\}.
\tag{2}
\]
For either genuine profile, the **whole signed** sums with \(E_j\) and \(C\) differ by \(o(M_N)\), uniformly at fixed parameters. The shift is zero at genuine prime \(m\). For every \(\xi>0\) choose fixed \(\rho>0\) sufficiently small, then take \(x\) sufficiently large. On each original physical profile,
\[
 \boxed{\quad
 \sum_{\substack{(s,q)\ \mathrm{physical},\ q\in\mathcal Q_i\\ \Omega(m)\le R_0}}
          W_s(q)\frac{D_B(q)}{\log q}\,(E_j(m))_+
                  \le \xi M_N,\qquad i=1,2.
       \quad}
\tag{3}
\]
In particular any fixed polynomial roughness on \(m\) is covered by one choice of \(R_0\). No bound on the actual unbounded-rank remainder or other quotient profiles follows, and previous reserves for \(C\) need re-evaluation for \(E_j\).

## 1. Target-uniform finite Euler moments and paid whole shift

The \(S_U,G\) parts are null to arbitrary log precision by the actual \(\mathcal Q_i\) argument of §1 of the low-rank note. For the new short polynomial, expand the weight into the finitely many separated terms \((\log d)^h(\log m)^{1-h}\), \(0\le h\le j\). On central \(m\asymp x\) the \(m\)-factors are smooth with log-power variation, and the \(d\)-coefficients are log-power bounded. The same generalized BV on the independent prime \(s\) and \(1\)-bounded actual \(q\)-mask retains the true modulus \(d\le U=\sqrt x/H^4\), sharp central cut and true reduced residue \(N\). As previously, use relative log-fine meshes and no rapidly varying phase on \(s\). The discrepancy is \(O_A(xL^{-A})\). In the reduced principal fix \(n=sq\), and put \(M=Nn\), an even integer \(\ll x^2\).

For each fixed \(h\ge0\) and \(Y\ge x^c\), \(c>0\) fixed, we use
\[
 \sum_{\substack{d\le Y\\(d,M)=1}}
     \frac{\mu(d)(\log d)^h}{\varphi(d)}
             =(-1)^h F_M^{(h)}(0)+O_{A,h,c}(L^{-A}),
\quad
 |F_M^{(h)}(0)|\ll_h(\log L)^{C+h},\quad F_M(0)=0.
\tag{4}
\]
Indeed \(F_M(z)=\sum_{(d,M)=1}\mu(d)/(\varphi(d)d^z)=A_M(z)/\zeta(1+z)\) for \(\operatorname{Re}z>0\), where
\[
 A_M(z)=\prod_{p\nmid M}\frac{1-p^{-z}/(p-1)}{1-p^{-1-z}}
              \prod_{p\mid M}(1-p^{-1-z})^{-1}.
\]
The first product is uniformly bounded near zero by its absolutely summable \(O(p^{-2-\operatorname{Re}z})\) deviations. In \(|z|\le1/(20\log L)\) split the second product at \(p=L^2\). Below the cut, \(|p^{-1-z}|\le e^{1/10}/p\), giving logarithmic size \(O(1+\log\log L)\) by reciprocal primes and the bounded small denominators. Above the cut, \(\omega(M)\ll L\) and each factor has logarithmic size \(O(L^{-2}e^{1/10})\). Hence \(A_M(z)\ll(\log L)^C\) uniformly, and \(1/\zeta(1+z)\) is analytic bounded near zero and vanishes there. Cauchy's estimate gives the derivative bound. The uniform finite constant moment of [Huang–Li, arXiv:2005.03811v2, Lemma 1](https://arxiv.org/pdf/2005.03811) is \(O(\exp(-c'\sqrt{\log Y}))\) on \(Y\ge x^c\) since \(\log M\ll_c\log Y\). Partial summation controls its weighted infinite tails, and the corresponding absolutely convergent partial-summation integrals for real \(z\downarrow0\) identify the convergent log moments with their analytic derivatives. This proves (4), not merely an Abel limit for the finite sums.

In (2) the constant term uses \(F_M(0)=0\). The \(h=1\) term is absent by \(P'_j(0)=0\); its presence could create a full \(M_N\)-scale main. All \(h\ge2\) terms, after \((\log m)^{1-h}\), cost \(O_j((\log L)^{C+j}/L)\) per literal \(n\). Each actual quotient profile has \(O(x/L)\) source pairs \((s,q)\), by the PNT upper on the final genuine prime and bounded reciprocal sums in the other independent polynomial prime ranges. Therefore the combined principal is \(o(x/L)=o(M_N)\). At genuine prime \(m\asymp x\) the only short divisor is \(1\) and \(S_U=G=1\); the shift in (2) is exactly zero, as is the original \(C(m)\).

## 2. Actual rank accounting and the radical midpoint

For \(\Omega(m)\le R_0\), let \(F\) contain all prime-power multiplicities of primes \(p\le x^{\epsilon_0}\) in \(m\). Then \(F\le x^{1/200}\), \(m=Ft\), and \(t\) is a nonempty product of large genuine prime labels. The actual upper sieve of §2 of the low-rank note gives, uniformly at each fixed \(F\),
\[
       \#\{\text{actual rows on }F\}
          \ll_{R_0} \frac{\mathfrak S(N)x}{F L^2}
                    +O_{A,R_0}(x/(F L^A)).
\tag{5}
\]
Here use \(z_q=x^{\epsilon_0/4},D=x^{\epsilon_0/2}\), ratio \(2\), in that same upper sieve on the **actual** rough quotient \(q\). The modulus \(s d<x^{.15}\) and the reduced residue \(N\overline F\bmod s d\) follow from the real equation, after removing \((F,N)>1\) and sieving only \(d\) coprime to \(FN\). The source \(t\) is at scale \(x/F\ge x^{.995}\); its independently boxed prime labels \(>x^{\epsilon_0}\) give ordinary BV for a single label, or generalized BV with one SW prime and the other product polynomially long. The modulus has unique \(s\) because \(d<s\), and the \(d\)-primes do not meet \(t\). The exact coprimality \((s,t)=1\) remains in the mean. As before, after factoring the nonnegative sieve main the local product is \(\ll_{R_0}\mathfrak S(N)/L\), since \(F\) has at most \(R_0-1\) primes. PNT upper gives \(O_{R_0}(x/(FL))\) true \(t\)-products. The sharp central interval for \(t\) is paid by relative meshes, or by positive inside and slightly enlarged outside boxes for this upper. Thus (5) is an actual fixed-target bound, not independent PNT on two correlated prime products.

Drop repeats \(p^2\mid m,\ p>x^{\epsilon_0}\), at power-small cost from summing \(O(x/p^2)\), the bounded number of \(s\)-labels in \(N-m\) and the \(O_{R_0,j}(L)\) weight. On the rest put \(R=\operatorname{rad}m,\ T=\log(m/R)\), so \(T\) depends only on \(F\). Then \(\sum_F1/F\ll_{R_0}(1+\log L)^{R_0-1}\) and \(\sum_F T/F\ll_{R_0}(1+\log L)^{R_0-2}\) by \(\sum_p(\log p)/p^2<\infty\) and ordinary prime reciprocals for other slots. If \(m\) is composite with prime radical it was removed, because a prime-power \(m\asymp x\) with \(\Omega(m)\le R_0\) has base \(>x^{\epsilon_0}\). Genuine prime rows are exact zeros and other relevant \(R\) are squarefree composite.

The \(C'_U=\sum_{d\mid m,d>U}\mu(d)\log(m/d)\) of the low-rank note differs from \(C\) pointwise by \(O_{R_0}(\log H)\), since every omitted \(\ell\) on \(d>U\) obeys \(\ell\le H^2\). The combination \(C'_U+\frac12\log m S_U\) equals \(\sum_{d|R,d>U}\mu(d)(\frac12\log m-\log d)\). Moving this to the exact \(\sqrt R,\log R\) center costs \(O_{R_0}(\log H+1+T)\) per row: a changed divisor lies between \(U\) and \(\sqrt R\) and its weight is at most that size. The new short polynomial term also costs only \(O_{R_0,j}(\log H+1+T)\). At a changed divisor use \(P_j(1/2)=0\); on common divisors the derivative of \(vP_j(\log d/v)\) in \(v\) is bounded on the relevant argument range \([0,1]\). Finally \(G(m)=G(R)\) by \(\mu\)'s squarefree support, so its outer log changes by \(O_{R_0}(T)\). These checks allow \(U\) above or below \(\sqrt R\). By (5) and the harmonic moments above, the whole weighted error is \(o(M_N)\) for any fixed \(0<\sigma<1\), with \(H=\exp(L^\sigma)\). We have not dropped an unpriced \(O(L)\) cut jump or assumed squarefreeness at small repeated factors.

## 3. Pointwise signs at the exact midpoint

Use \(t_d=\log d/\log R\) and distinct-prime rank \(r\). The normalized exact midpoint version of (2) is
\[
 C_*(R)/\log R+\tfrac12 S_*(R)
       -\sum_{d|R,\ d<\sqrt R}\mu(d)P_j(t_d)
       -\left(1-\tfrac1{2j}\right)G(R).
\tag{6}
\]
Here \(C_*,S_*\) are as in the low-rank note. No exact midpoint divisor occurs for squarefree \(R>1\).

If \(r\ge3\) is odd, the first two terms of (6) vanish by the complement identity of that note. The short \(P_j\) moment is half the full moment, because \(\mu(R)=-1\) and \(P_j\) is antisymmetric. The full linear moment vanishes by the \(r\)-fold finite difference. The \(r\)-th derivative of \((t-\tfrac12)^j\) is nonnegative for odd \(r\le j\), since its remaining power \(j-r\) is even, and vanishes for \(r>j\). Successive integration over the positive exponent increments gives a **nonpositive** full Möbius moment of that power, with sign \((-1)^r=-1\). The coefficient \(-b_j\) therefore makes the full \(P_j\) moment nonnegative, as required for the minus short term in (6).

If \(r\) is even, \(S_*=0\) and complementing gives \(C_*/\log R=\sum_{\mathrm{short}}\mu(d)(t_d-\tfrac12)\). The short linear term of \(P_j\) cancels it exactly. The only signed polynomial left is
\[
 b_j\sum_{\mathrm{short}}\mu(d)(t_d-\tfrac12)^j
         =-\frac{b_j}{2}\sum_{d|R}\mu(d)|t_d-\tfrac12|^j .
\]
For every even \(r\le j+1\), the \(r\)-th distributional derivative of \(|t-\frac12|^j\) is nonnegative: below \(j+1\) it is a nonnegative multiple of \(|t-\frac12|^{j-r}\), and at \(j+1\) it is \(2j!\) times a positive unit point mass. First convolve with a nonnegative smooth mollifier if needed. Successive integration with sign \((-1)^r=+1\), followed by the limit in the finite difference, shows the full Möbius moment is nonnegative. The displayed polynomial is therefore nonpositive. Since \(j+1\ge R_0\), (6) is at most \((1-\frac1{2j})G_-(R)\) on the entire bounded-rank composite support, for both parities; no separate even-rank small-factor charge is needed.

The last defect obeys the same flat-taper estimate as before. There are at most \(R_0-1\) participating \(p\mid R,\ p\le Z\). The unflattened \((1-u)_+^{R_0-1}\) has nonnegative signed differences through this order; flattening changes its sup norm by \(O_{R_0}(\rho)\) and its Lipschitz bound remains uniform. Pairing the smallest divisor bit and comparing to the unflattened taper yield
\[
 G_-(R)\ll_{R_0}\min\left(\rho,\min_{p\mid R,\ p\le Z}\frac{\log p}{\log Z}\right)
\]
with zero defect if there are no such primes. Sum its \(\log x\) multiple using (5) at fixed \(F\). For \(k\) participating primes the layer integral
\(\int_0^\rho(\sum_{Z^v<p\le Z}1/p)^k\,dv
\ll_{R_0}\rho(1+|\log\rho|)^k\)
supplies the harmonic sum. The remaining \(F\)-factors in \((Z,x^{\epsilon_0}]\) have bounded reciprocal mass for fixed \(\epsilon,\epsilon_0\); their repeated powers only reduce the mass up to bounded multiplicity. The total defect is \(O_{R_0,\epsilon}(\rho(1+|\log\rho|)^{R_0-1}M_N)\). Choosing \(\rho\) and then \(x\) establishes (3).

The increment over seven comes from antisymmetry together with the canceled linear coefficient at zero, not extrapolation of the rank-six vertex bound. The degree, sieve constants, and harmonic factor counts all depend on \(R_0\); limits in \(R_0\) and \(x\) have not been interchanged. The full signed upper and binary Goldbach remain unproved.

## Comparison

[Arneth’s October cubic minorant](https://zenodo.org/records/23477014) and [Pham’s reflected-prime programme](https://www.preprints.org/manuscript/202610.3061) use different fixed-target sieve/correlation reductions. This cut-dependent polynomial acts on the reflected multiplicity ranks for the two literal adjusted triprime quotient supports; it does not produce their missing full signed correlation or assert priority. The [coupled fixed-rank detector](all_fixed_ranks/Proof.md) treats a squarefree product of both summands rather than this one-sided adjusted row.
