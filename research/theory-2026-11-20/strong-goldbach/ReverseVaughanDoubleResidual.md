# Reverse Möbius BV and a genuine double-Vaughan cancellation region

Let \(x=N/2\), \(I=(x/2,x]\), and \(s\sim S=x^\alpha\) be an actual prime with \(.10\le \alpha\le.14\). Put \(m=N-sq\). Use the exact test \(W_s(q)=K_{P_3}(sq)\) of the actual semiprime cell, or the smooth product tests in [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md). Take arbitrary \(|\kappa_s|\ll L^C\), \(L=\log x\). Begin with the actual high-product reflected Vaughan III term from [UnmarkedSemiprimeDualWeilTypeII.md](UnmarkedSemiprimeDualWeilTypeII.md):
\[
 T=\sum_{\substack{s,q\ {\rm prime}\\s\sim S,\ sq\in I}}
  \kappa_s W_s(q)
  \sum_{\substack{d\ell h=m\\d>U,\ \ell>V,\ d\ell>Q}}
                      \mu(d)\Lambda(\ell).
\tag{1}
\]
Here \(U\ge x^{.40}\), \(V\ge1\), and \(Q\ge1\) may be the exact cutoffs in the preceding notes. The argument works with additional sharp individual intervals on \(d,\ell,h\), or with the cutoff averages in [SmoothedActualVaughanRough.md](SmoothedActualVaughanRough.md); in the latter case apply the uniform sharp-cutoff result before averaging. It requires no primality for individual terms of the reflected expansion.

Partition \(d\) into dyads \(D<d\le 2D\) in the initial linear sum. For each fix a small \(\epsilon_0>0\) with \(D^{1/2-\epsilon_0}/(2S)\ge x^{c_0}\) for a fixed \(c_0>0\), and write
\[
 E_D=\frac{D^{1/2-\epsilon_0}}{2S}.
\tag{2}
\]
Take cutoffs \(U_q,V_q\ge1\) with \(U_q V_q\le E_D\), \(V_q\ll x^{1-\alpha-\epsilon_1}\) for a fixed \(\epsilon_1>0\). They can vary across \(D\)-dyads. For example if \(U\ge x^{.448}\), the full band permits \(U_q=x^{.070}, V_q=x^{.010}\), with \(\epsilon_0=.005\); taking \(D\ge U/2\) gives \((.5-.005)(.448)-.14>.081\).

Then the entire expression (1) equals, up to \(O_{B,\epsilon}(xL^{-B})\) for every \(B\) and any fixed \(\epsilon>0\), the following **exact signed double remainder** summed over its \(D\)-dyads:
\[
 \sum_{\substack{
       d\ell h+s r\lambda j=N,\ s\sim S\ {\rm prime}\\
       n=s r\lambda j\in I,\ (n,N)=1\\
       d\sim D,\ d>U,\ \ell>V,\ d\ell>Q\\
       r>U_q,\ \lambda>V_q,\ e=r\lambda>E_D\\
       (d\ell)(s e)>x^{1-\epsilon}}}
 \frac{\kappa_s W_s(r\lambda j)}{\log(r\lambda j)}
                  \mu(d)\Lambda(\ell)\mu(r)\Lambda(\lambda).
\tag{3}
\]
In particular (i) **both** true quotient-side Vaughan Type I terms are negligible against the full actual high reflected branch, without any upper cap on \(d\ell\); (ii) the quotient's own Type III slice \(e\le E_D\) is negligible; and (iii) the genuine double Type III region \(d\ell\cdot s e\le x^{1-\epsilon}\) is negligible even when **both** products are beyond the other cuts. This is a signed result for a component of the original expansion, not an estimate for (3).

## 1. Uniform masked, maximal Möbius BV

For fixed \(c,H_0,\delta>0\), \(D\ge x^c\), and \(M\le x^{H_0}\), we use
\[
 \sum_{\substack{v\le D^{1/2-\delta}\\(v,M)=1}}\tau_2(v)^F
   \max_{(a,v)=1}\max_{z\le 2D}
   \left|\sum_{\substack{n\le z,\ n\equiv a\bmod v\\(n,M)=1}}\mu(n)\right|
                \ll_{B,F,c,H_0,\delta} D L^{-B}.
\tag{4}
\]
Here is a derivation so that the extra unit mask is not silently included in the theorem for unmasked \(\mu\). For the latter use [Granville–Shao, Theorem 1.1](https://arxiv.org/pdf/1706.05710) with \(f=\mu,g=1\) (the theorem's \(f\) is in their class \(\mathcal C\) since \(F=1/\zeta\)). Its restriction to primes is \(-1_{\mathcal P}\), for which ordinary prime BV holds, and ordinary Siegel–Walfisz for \(\mu\) at powers of \(\log D\) follows by the usual Dirichlet zero-free region and Siegel's bound; at larger \(v\) the trivial \(O(D/v+1)\) reduced class count gives the single-residue criterion. Remove their coprime principal term by uniform coprime Mertens, e.g. (8) of the former note, and \(\sum_{v\ll D}1/\phi(v)\ll L\). To obtain maximal prefixes at a fixed exponent below \(1/2\), use a mesh of \(L^{C_1}\) equally spaced endpoints up through \(2D\); the nonmaximal BV proof applies to each positive mesh point by the fixed power slack. The rounding error at most \(O(D/(vL^{C_1})+1)\) per modulus is negligible with fixed \(C_1\) sufficiently large. Lastly the factor \(\tau_2(v)^F\) is harmless: use Cauchy on the unweighted maximal errors \(\Delta(v)\), and the trivial \(\Delta(v)\ll D/v+1\) to bound \(\sum_v\tau_2(v)^{2F}\Delta(v)\ll D L^C\). This gives the unmasked form with log reserves, without equating prime BV to Möbius BV.

For the mask, use the exact convolution \(\mu(n)1_{(n,M)=1}=\sum_{a b=n,\ a\ M\text{-smooth}}\mu(b)\), where "\(M\)-smooth" here means that **all prime divisors divide \(M\)**, not that \(a\le M\). For \(a\le D^{\delta/2}\), apply the just-proved weighted maximal theorem at \(2D/a\) to \(b\equiv a^{-1}a_0\bmod v\), using the fixed power slack and \(\sum_{a\ M\text{-smooth}}1/a\ll L^C\). The allowed modulus \(v\) is coprime to \(M\), hence to all these \(a\). For the tail, use \(O(D/(av)+1)\) per progression. The harmonic tail of the \(a\)'s is power-small by Rankin at \(1/4\), with auxiliary product \(\prod_{p\mid M}(1-p^{-3/4})^{-1}=x^{o(1)}\). The floor term is power-small because
\[
 \#\{a\le 2D:\ a\ M\text{-smooth}\}
 \ll D^{1/4}\prod_{p\mid M}(1-p^{-1/4})^{-1}
    =D^{1/4}x^{o(1)} .
\]
For either product, split at \(p=L\): the total over small integers of \(p^{-t}\) is \(O(L^{1-t})\) for fixed \(0<t<1\); the number of higher prime divisors is \(O(L/\log L)\). Thus \(\sum_v\tau_2(v)^F\) times the floor cost is at most \(D^{3/4}x^{o(1)}\). This proves (4), uniformly in \(M\) of polynomial size and with moving reduced residues and endpoints.

## 2. Expansion on the true quotient side

First remove primes \(s\mid N\) or \(q\mid N\) in (1), at total power-small cost \((x/S+S)x^{o(1)}\) as in the forward argument. Replace the true ordinary prime indicator by \(\Lambda(q)/\log q\), now summing integer \(q\) with \((q,N)=1\), at cost at most \(S (x/S)^{1/2}x^{o(1)}=x^{(1+\alpha)/2+o(1)}\), since the extra points are proper prime powers and each reflected coefficient is \(\ll\tau_2(m)\log m=x^{o(1)}\). This replacement does not remove the \(1/\log q\) factor or use a weighted rather than unweighted target. For \(q\asymp x/S\), the term \(\Lambda_{\le V_q}(q)\) vanishes. Apply literal Vaughan \(\mu_{\le U_q}*\log - \mu_{\le U_q}*\Lambda_{\le V_q}*1 + \mu_{>U_q}*\Lambda_{>V_q}*1\) on \(q\).

For each of its first two terms let \(e\) be its divisor argument (respectively \(r\) and \(r\lambda\)); then \(e\le E_D\). The coefficient of \(e\) costs at most \(L\), and a free log in the first term becomes \(\log(q/e)\). The same estimate below also applies to the genuine third term sliced at \(e\le E_D\); its coefficient is the actual sum
\[
 C_q(e)=\sum_{\substack{r\lambda=e\\r>U_q,\ \lambda>V_q}}
                       \mu(r)\Lambda(\lambda),\qquad |C_q(e)|\le\log e.
\]
No new cutoff on \(m\) is needed.

For fixed \(k=\ell h\), the physical modulus from \(e\mid q\) and \(q=(N-k d)/s\) is \(v=s e\). The unit condition \((q,N)=1\) and \((s,N)=1\) is equivalent to \((k d,N)=1\). Retain \((k,N)=1\); if \((k,v)>1\) or \((v,N)>1\), the congruence \(kd\equiv N\bmod v\) is impossible on the retained support. Otherwise it is exactly
\[
                 d\equiv N\bar k\pmod{v},\quad (d,N)=1,
\]
a reduced class, with \(v\le D^{1/2-\epsilon_0}\). For fixed \(s,e,\ell,h\), all sharp conditions in (1) in the \(d\)-coordinate are intersections of ordinary intervals (for example \(d>Q/\ell\) and \(kd\in N-I\)). The coefficient \(W_s((N-kd)/s)/\log((N-kd)/s)\), with an optional factor \(\log((N-kd)/(s e))\), has log-power sup norm and bounded variation on that support, since \(q\asymp x/S\). Thus partial summation gives a fixed logarithmic multiple of the maximal prefix in (4). The number of \(s,e\) representations of \(v\) is \(\le\tau_2(v)\), as \(s\) and \(e\) are determined by choosing a divisor of \(v\). The total \(\ell,h\) weight for fixed \(k\) is \(\le\sum_{\ell\mid k}\Lambda(\ell)=\log k\). Hence for fixed \(k\), the summed cost over \(s,e,\ell,h\) is \(O_B(D L^{-B})\), by (4) with \(M=N\), all weights and endpoint dependence above absorbed. Finally \(k\ll x/D\), so the total is \(O_B(xL^{-B})\) on the dyad. This is the announced full reverse-side Type I cancellation and actual small-product quotient Type III cancellation at every \(N\).

## 3. The free/free under-hyperbola double sector

After the quotient opening, fix \(s,d,\ell,e\), where \(e=r\lambda\), \(a=d\ell\), \(A=s e\). The two genuinely free variables solve
\[
                 a h+A j=N,\qquad ah\in N-I,\quad (ah,N)=1.
\]
Only \((a,A)=1\), \((aA,N)=1\) contribute: any common divisor divides \(N\), which \(ah\) cannot share on this unit support. Expand \((h,N)=1\) by \(\sum_{f\mid(h,N)}\mu(f)\). For each \(f\) the \(h\)-class modulo \(A\) and \(f\mid h\) give one class modulo \(Af\). The active \(j=(N-ah)/A\) is automatically an integer and positive. Thus the free sum with original \(1/\log q\) is
\[
 \sum_{\substack{ah+A j=N,\ ah\in N-I\\(ah,N)=1}}
       \frac{W_s(ej)}{\log(ej)}
 =\frac{\phi(N)}{N a A}\!
       \int_{I}\frac{W_s(v/s)}{\log(v/s)}\,dv
       +O(L^C\tau_2(N)).
\tag{5}
\]
Use the integral in \(v=N-ah\), and the uniform log-power test variation for each progression's endpoint error. If extra free \(h\) intervals are imposed, the corresponding main integral has additional \(v\)-bounds depending on \(a\). Those integrals still have log-power normalized variation in \(d\) (each endpoint is linear in \(d\) up to clipping); the same argument below applies. Formula (5) includes the literal high reflected \(m\)-product inequality and quotient \(e\)-cut as outer conditions, not as free-coordinate surrogates.

In the region \(a A\le x^{1-\epsilon}\), the sum of the errors in (5) is \(O(x^{1-\epsilon+o(1)})\) by counting products \(s e d\ell\le x^{1-\epsilon}\), with the pointwise divisor envelope for the number of factorizations and weights. This bound includes \(e=r\lambda\) with its actual \(\mu(r)\Lambda(\lambda)\) coefficient. In the first term of (5), keep \(s,e,\ell\) fixed, and sum \(\mu(d)/d\) with the exact reduced mask \((d,N A)=1\). The \(d\)-interval is cut by \(d\sim D,\ d>U,\ d>Q/\ell,\ d\le x^{1-\epsilon}/(A\ell)\) and any other given intervals. Every nonempty interval is on the polynomially long \(D\) dyadic scale before endpoints, so (8) of the preceding whole-Type-I note and partial summation give \(O_B(L^{-B})\) for its harmonic Möbius sum, uniformly even when the surviving subinterval is short. The remaining factors are summed harmonically with
\(\sum_s|\kappa_s|/s\ll L^C\),
\(\sum_e|C_q(e)|/e\ll L^C\), and \(\sum_\ell\Lambda(\ell)/\ell\ll L\), and the central integral has cost at most \(xL^C\). This proves arbitrary-log cancellation on this full double Type III region.

For example with \(\alpha=.14,\ U_q=x^{.070}, V_q=x^{.010}\), a fixed log neighborhood of
\[
  \log_x d=.48,\quad\log_x\ell=.03,\quad
  \log_x r=.15,\quad\log_x\lambda=.05
\]
has \(d\ell\) at exponent .51 (beyond all proved forward bounds at this \(\alpha\)), \(s e\) at exponent .34 (beyond the reverse BV cutoff exponent about .238), and \(aA\) at exponent .85. It lies in the double region just canceled, for instance at \(\epsilon=.05\), whenever the original reflected cutoffs are those previously used. These are actual Vaughan factor labels in the expansion, not an assumption of factorability on an arbitrary different carrier.

Only (3) survives this argument. When \(aA\ge x\), factoring by the short complementary \(h,j\) does not give a free/free count of the same form: the variables then to be summed are \(d,r\), with the exact coefficients \(\mu(d)\mu(r)\) on a correlated affine relation. No ordinary separate progression theorem, or the sign of an isolated rank, estimates that remaining coupling. This note proves neither the required strict upper against the prime semiprime mask nor binary Goldbach.
