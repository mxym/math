# Smooth cutoffs localize the actual Vaughan III remainder to rare small-factor counts

Use the actual semiprime cell \(n=sq\in I=(x/2,x]\), \(s,q\) both prime, \(x=N/2\), \(s\sim S=x^\alpha\), \(.10\le\alpha\le.14\), \(m=N-sq\). Let \(K=K_{P_3}(sq)\), or any uniformly \(O(1)\) test on this cell to which the two Type I formulas and Type III slice of [the dual estimate](UnmarkedSemiprimeDualWeilTypeII.md) apply. Denote \(L=\log x\) and let \(b_*=(4-5\alpha)/7-\Delta\) be the proved cap. This note gives an **actual arithmetic** localization of the leftover, and a near-natural-scale absolute bound on the resulting remaining support. It does not give the necessary strict signed upper.

Fix a small constant \(\upsilon>0\), \(V=x^\upsilon\); choose fixed positive-width intervals \(\mathcal U=[u_0,u_1]\), \(\mathcal B=[b_0',b_1']\) with \(u_0>.40\), \(u_1+\upsilon\le b_0'<b_1'\le b_*\). They can depend on the label dyad, provided all widths and slack constants are uniform. For example \(\upsilon=.004,\ \mathcal U=[b_*-.020,b_*-.010],\ \mathcal B=[b_*-.004,b_*-.002]\). For every \(u\in\mathcal U,b\in\mathcal B\), the known estimates evaluate the two Type I terms and the part of Type III below \(d\ell\le x^b\), with log-saving errors uniform in the sharp cutoffs. Average each such exact identity with \(U=x^u\) against two independent nonnegative probability densities supported in the indicated intervals. Those densities may depend on \(x\) and our prescribed precision; no shrinking-window uniformity of an asymptotic theorem besides the already uniform Type I and Type III bounds is presumed.

We shall take the densities to be \(k\)-fold convolutions of uniform boxes of respective lengths \(|\mathcal U|/k,|\mathcal B|/k\), translated to have the given supports. Let \(F_U,F_b\) be their cumulative distributions and
\[
 C(m)=\sum_{d\ell h=m}\mu(d)\Lambda_{>V}(\ell)
             F_U(\log_x d) F_b(\log_x(d\ell)).
\tag{1}
\]
This is the actual averaged high-product Vaughan III coefficient. The weighted sum \(\sum_{s,q}K(sq)C(N-sq)\) is the entire remaining part after the explicit principal term and arbitrary-log errors. No parity weights have been substituted for it.

## 1. A uniform finite difference on the actual reflected integer

Put
\[
      z=\exp\big(L/(\log L)^4\big),\qquad
      k=\left\lceil C_0\frac{\log L}{\log\log L}\right\rceil ,
\]
with fixed \(C_0\) chosen for the requested log precision. Write \(\omega_z(m)=\#\{p\le z:p\mid m\}\). For each fixed \(B>0\), with large enough \(C_0\),
\[
 \sum_{\substack{s,q\ {\rm as\ above}\\\omega_z(N-sq)\ge k}}
              |K(sq) C(N-sq)|\ll_B x L^{-B}.
\tag{2}
\]
This includes nonsquarefree \(m\), after a power-small proper prime-power disposal.

Indeed the contribution of integers divisible by some \(p^a>V\) with \(p\le z\) is power small in total: for each \(p\) impose its least such power \(p^{a(p)}>V\). There are \(O(xz/V+z)=x^{1-\upsilon+o(1)}+x^{o(1)}\) possible \(m\) in the central interval, even by floor counts. Each \(N-m\) has at most \(O(1)\) small prime labels \(s\sim S\), and \(|C(m)|\le\tau_2(m)\log m=x^{o(1)}\) by \(\sum_{\ell\mid m}\Lambda(\ell)=\log m\). Thus for all retained \(\ell\) the prime divisor of \(\ell\) cannot be a chosen \(p\le z\).

If \(m\) has \(k\) distinct primes \(p_i\le z\), fix any \(k\) of them. For each fixed \(\ell\) in (1), and each \(d_0\mid m/\ell\) coprime to their product, nonzero Möbius terms run over \(d=d_0\prod_{i\in E}p_i\) for all subsets \(E\). Their signs are \(\mu(d_0)(-1)^{|E|}\), without regard to possible higher powers of the \(p_i\) in \(m\). The alternating sum is exactly the \(k\)-fold finite difference of \(F(y)=F_U(y)F_b(y+\log_x\ell)\) with increments \(\log p_i/L\). For the box convolutions one has \(\|F_U^{(j)}\|_\infty,\|F_b^{(j)}\|_\infty\le (Ck)^j\) for \(1\le j\le k\): differentiate \(j-1\) separate boxes as first differences of point masses divided by the box length, leaving at least one bounded box. The \(k\)-th derivative is interpreted a.e., and the preceding derivative is absolutely continuous, so the iterated fundamental theorem of calculus applies. By the product rule the finite difference is bounded by \((Ck\log z/L)^k\), uniformly in \(\ell\). This is \(O(L^{-B-3})\) for sufficiently large fixed \(C_0\). The remaining unsigned divisor/log sum is \(\le\tau_2(m)\log m\). Summing by \(\sum_{m\asymp x}\tau_2(m)\ll x L\) proves (2), without any average over targets or any prime-distribution estimate.

## 2. Near-natural-scale absolute bound on the true rare support

For the same \(k,z\), uniformly at each target,
\[
 \sum_{\substack{s,q\ {\rm as\ above}\\\omega_z(N-sq)<k}}
                 |K(sq) C(N-sq)|\ll x L^{-1+o(1)}.
\tag{3}
\]
The \(o(1)\) is allowed to depend on the fixed precision chosen in (2). This is not \(o(x/L)\); the sign is still needed to remove the \(L^{o(1)}\) loss or obtain a strict small constant.

Here is an upper-sieve proof retaining the true quotient prime. Put \(\rho=(\log\log L)^{-1}\) (taking \(x\) large), \(\eta=1-\rho\). On \(\omega_z(m)<k\), use \(1\le\rho^{-k}\rho^{\omega_z(m)}\). Bound \(|C(m)|\le\tau_2(m)\log m\) and split the divisor moment by \(\tau_2(m)\le 2\sum_{d\mid m,d\le\sqrt m}1\). The \(O(1)\) possible \(s\mid N\) or \(q\mid N\) in each macro-band are power-small even before these bounds (actual counts \(\ll (x/S+S)x^{o(1)}\)). Thus we may take \((d r,N)=1\), \(m=dr\), and \(s\nmid d\). For each such \(s,d\), parametrize
\[
 r=r_0+s j,\qquad q=q_0-d j,\qquad dr_0+s q_0=N,
\]
on an interval of \(j\) of length \(H\ll x/(sd)\). Here \(s>z\) and \(d\le\sqrt{3x/2}\). The exact soft weight in \(m\) is
\[
 \rho^{\omega_z(d)}
 \prod_{\substack{p\le z\\p\nmid d}}(1-\eta\,1_{p\mid r}).
\]
It is bounded above if primes \(p\mid N\) are omitted in the second product. The omission avoids deterministic overlap with the \(q=0\bmod p\) class. Write \(F_\rho(d,N)=\prod_{p\le z,p\nmid dN}(1-\eta/p)\).

**Sieve bound for each \(s,d\).** For every fixed \(B_1\) one has
\[
 \sum_{\substack{j\ {\rm in\ its\ interval}\\q\ {\rm prime}}}
       \prod_{\substack{p\le z\\p\nmid dN}}(1-\eta\,1_{p\mid r})
 \ll
    \frac{H\,F_\rho(d,N)}{L}(\log L)^C
     + H L^{-B_1}+x^{.03+o(1)} .
\tag{4}
\]
The proof uses only elementary Selberg sieve and CRT. Let \(R=x^{.01}\), and majorize the prime \(q\gg x/S\) by \((\sum_{e\mid q,e\le R}\lambda_e)^2\) with \(\lambda_1=1\), squarefree \(e\), \((e,d)=1\). This is nonnegative. Bound the soft \(r\)-product above by its even Bonferroni truncation of order \(J\asymp C_1\log L\), since every factor is \(1-\eta\,1_{p\mid r}\); this version follows, for example, by random independent selection with inclusion probability \(\eta\) on the finite set of divisors \(p\mid r\). Apply CRT in \(j\) to \([e,e']\mid q\) and each short divisor condition for \(r\). For a prime \(p\nmid dN,\ p\le z\), the two roots \(q=0,r=0\bmod p\) are distinct, because a shared root would imply \(p\mid N\). Conditional on \([e,e']\mid q\), the active \(r\)-roots therefore occur at primes not dividing \([e,e']\), each of relative incidence \(1/p\). The short expansion's density tail is bounded uniformly by
\(\ll 2(e\sum_{p\le z}p^{-1}/J)^J\ll L^{-B_1-C'}\)
for sufficiently large fixed \(C_1\). Its support is at \(z^{J}=x^{o(1)}\). The normalized joint main is therefore
\[
 H\,F_\rho(d,N)\sum_{e,e'}\lambda_e\lambda_{e'}g([e,e']),
\quad
 g(p)=
 \begin{cases}
 0 &p\mid d,\\
 1/(p-\eta)&p\le z,\ p\nmid dN,\\
 1/p &\text{otherwise}.
 \end{cases}
\]
Here \(g\) on squarefree integers is multiplicative. Each \(g(p)\le 1/2\), including \(p=2\) since \(N\) is even. Use the usual minimizing Selberg coefficients for this \(g\): their quadratic sum is \(G(R)^{-1}\), \(G(R)=\sum_{a\le R,\ a\ {\rm sf}}\prod_{p\mid a} g(p)/(1-g(p))\), and \(|\lambda_e|\le\prod_{p\mid e}(1-g(p))^{-1}\le\tau_2(e)\) (restrict to the positive \(g\) primes in forming the sieve). The truncation-tail cost after the \(e,e'\) sums is still \(O(HL^{-B_1})\) since their positive absolute majorant is
\(\sum_{e,e'\le R}\tau_2(e)\tau_2(e')/[e,e']\ll L^C\) by writing \(e=gu,e'=gv,g=(e,e')\) and using elementary divisor harmonic sums. CRT floor errors cost \(z^J R^2 L^C \le x^{.03+o(1)}\).

For the lower bound on \(G(R)\), keep primes \(p\le R^c\) with \(p\nmid dN\), where \(c>0\) is fixed small. Their full Euler-product mass is at least \(\prod_{p\le R^c,p\nmid dN}(1-1/p)^{-1}\gg L/(\log L)^C\); use the uniform \(dN/\phi(dN)\ll\log\log x\). Under its normalized subset distribution, \(\mathbb E\log a=\sum g(p)\log p\le 2\sum_{p\le R^c}\log p/p\ll c\log R\). Markov's inequality retains a fixed fraction of this product on \(a\le R\) for small fixed \(c\). This proves (4).

Now \(F_\rho(d,N)\ll(\log z)^{-\eta}(\log L)^C\) by its Euler product and the \(dN/\phi(dN)\) bound. Also
\[
 \sum_{d\le \sqrt{3x/2}}\frac{\rho^{\omega_z(d)}}d
 \ \le\ \prod_{p\le\sqrt{3x/2}}\left(1+\frac{\rho^{1_{p\le z}}}{p-1}\right)
 \ \ll L(\log z)^{-\eta}.
\]
Multiply (4) by \(L\rho^{-k}\rho^{\omega_z(d)}\), sum over \(s,d\), and use \(\sum_{s\sim S,s\ {\rm prime}}1/s\ll1\) (also valid summed over the entire macro-band). The power errors in (4) sum to \(\ll x^{.67+o(1)}\); the arbitrary-log error is negligible. The main is at most
\[
 x\,L\,\rho^{-k}(\log z)^{-2\eta}(\log L)^C=x L^{-1+o(1)},
\]
since \(\log z=L/(\log L)^4\), \(\rho^{-k}=L^{o(1)}\), and \(L^{2\rho}=L^{o(1)}\). This proves (3).

The sign and quantitative size within the rare support \(\omega_z(m)<k\) remain. In particular all balanced triple primes in [the positive-only counterchamber](UnmarkedVaughanPositiveRankThree.md) lie there, so one cannot simply discard the negative terms. Averaging cutoffs and the signed toggles do not solve Goldbach or give a full prime-shift asymptotic.
