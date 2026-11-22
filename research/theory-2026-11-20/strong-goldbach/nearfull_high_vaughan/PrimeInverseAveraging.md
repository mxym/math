# Prime-reciprocal averaging for the true two-label high-cut score

Use the exact near-full score of [PrimeOuterReciprocal](PrimeOuterReciprocal.md): a fixed \(C_0>1\), an even integer \(N\), \(L=\log N\), \(\ell=\log L\), \(S=\exp(\ell^4)\), \(B=N/S\), \(I=[N/S^{C_0},B]\), \(W=\sqrt N/S^{C_0+10}\), \(U=\exp(\ell^3)\), \(z=\exp(\ell^2)\), and \(J\subset J_0\Subset(0,1)\). Write \(x=Af\in NJ\), \(y=N-x=mCh\), \(Ch\in I\), \(T_y=y/B\), and
\[
Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d),\qquad
H_U(n)=1_{n>1}\sum_{d\mid n,\ d\le U}\mu(d).
\]
The score of a prime-label box is the sum of
\((\log f)(\log h)H_U(A)H_U(C)Q_y(m)\) over these actual tuples, with \(P^-(AC)>z\), \((xy,N)=1\), and genuine primes \(f,h>W\).

**Theorem.** At each even \(N\), the whole part of this score with \(f,h\le N^{.532}\) is \(O_D(NL^{-D})\) for every fixed \(D>0\). More generally, in independent real intervals inside fixed dyads of scales \(N^\alpha,N^\beta\), number the two genuine prime scales so \(\alpha\le\beta\). Assume \(W\ll N^\alpha\), \(\beta\le .58\), and, for some fixed \(\Delta>0\),
\[
\tfrac12\beta+\tfrac{11}{8}\alpha\le 1-\Delta,
\qquad
\tfrac76\beta+\tfrac23\alpha\le 1-\Delta .                       \tag{1}
\]
Then the same bound holds on that entire actual box. In particular the asymmetric point \(\alpha=.501,\ \beta=.569\) is admissible. A direct application of Irving's Theorem 1.1, with no short progression variant, already gives the whole \(f,h\le N^{.526}\) region, with alternative sufficient rails
\[
\tfrac54\beta+\tfrac58\alpha,qquad
\beta+\tfrac9{10}\alpha,qquad
\tfrac76\beta+\tfrac{13}{18}\alpha\quad \le 1-\Delta.           \tag{2}
\]
All estimates are on the same literal grouped high-cut score as PrimeOuterReciprocal. There is no restriction on the radical of \(N\). The only averaging added is over actual moduli at this one target, not over the target. A remaining two-label score is not evaluated.

## 1. Open the score and keep its true principal

The expanded geometry and the zero-frequency calculation are those of [PrimeOuterReciprocal](PrimeOuterReciprocal.md). More precisely, freeze the \(m\)-window and the strict \(Q_y\)-divisor endpoint on the log-fine \(y\)-mesh there, using that each changing label is a genuine divisor of \(y\). At a moving endpoint there are \(O(NL^{-F}/w+1)\) possible multiples of each actual \(w=m\) or \(w\mid m\) label; \(w\le S^{C_0}\). This is a globally negligible collar, after choosing \(F\) large, by fixed divisor moments and Cauchy. Use smooth central test functions \(\Psi(x/N)\) on these cells, with arbitrary fixed derivative norms bounded by fixed log powers and thinner collars paid by the same divisor moments. The number of cells is a fixed power of \(L\).

Open \(d,e\le U\) with \(\mu(d),\mu(e)\) from the two \(H_U\)'s; both native cofactors exceed \(N^{.42-o(1)}\) here, so their \(>1\) mask is automatic. Retain actual \(z\)-roughness on \(d,e\). Open the free rough factors by the usual two consecutive short Bonferroni brackets with labels \(e_1,e_2\). All choices of \(m,d,e,e_1,e_2\) are \(N^{o(1)}\) for every fixed requested precision. Their omitted positive tails are paid by actual \(e_i\mid x\) or \(e_i\mid y\), before invoking spectral estimates: the row indicator of an omitted label is bounded by the positive sum of its actual multiples, of mean bounded by the factorial reciprocal tail. Cauchy with fixed divisor moments recovers any prescribed log saving. In this application an omitted-label multiplicity is at most the ordinary divisor function of that physical leg. This does not use over-root floor sums.

On each ordered pair of actual prime dyads, use \(p\) for the prime on the shorter-scale leg and \(r\) for the other prime, regardless of which physical leg contains \(m\). The exact enlarged equation is
\[
 F a+H c=N,\qquad F=F_0 p,\quad H=H_0 r,
\]
with fixed subpower \(F_0,H_0\) for each outer assignment. In particular neither is inferred from a modular inverse; in the original orientation they are \(d e_1, m e e_2\). Reversing the orientation replaces \(\Psi(x/N)\) by \(\Psi(1-x/N)\). Retain \((FH,N)=1\) and \((F,H)=1\). Cross incompatibility \((F_0,H)>1\) gives no rows; \(p\mid H\) is exactly the exclusion of nonunits in the prime inverse sum, since every factor of \(H_0\) is smaller than \(p\). A shared prime \(p=r\) is thus not counted. Target prime divisors \(p\mid N\) can be handled individually; there are \(O(1)\) in these polynomial ranges.

The exact target-unit condition on \(a,c\) is opened with \(u\mid N\), \(u\mid a\) if and only if \(u\mid c\). By fixed divisor moments and Cauchy the contribution of \(u>\exp(L^{3/4})\) is at most
\[
 N L^{O(1)}\sum_{\substack{u\mid N\\u>\exp(L^{3/4})}} u^{-1/2}=O_D(NL^{-D}).
\]
For this bound use Rankin at exponent \(0.01\) and \(\sum_{p\mid N}p^{-.49}=O(L^{.51})\), obtained by splitting at \(L\) and using \(\omega(N)=O(L)\) above it. The expansion itself uses only squarefree \(u\). Poisson in the free coordinate then gives zero mode
\[
 \frac{N}{uFH}\widehat\Psi(0)
\]
and nonzero summands
\[
 \frac{N}{uFH}\widehat\Psi\left(\frac{jN}{uFH}\right)
 e_H\big(j(N/u)\overline{F_0p}\big),\qquad 0\ne j\in\mathbb Z,       \tag{3}
\]
up to sign convention in Fourier transform. Here \(e_q(t)=\exp(2\pi i t/q)\), with the inverse taken modulo \(H\). Restoring all \(u\) in the model multiplies the zero mode by \(\varphi(N)/N\) relative to the unfiltered sample.

At fixed central integration point, actual \(m,p,r,e,e_1,e_2\), recombine any auxiliary product dyads before taking the original \(d\le U\) sum. The only extra \(d\)-condition is \(z\)-roughness and coprimality to \(N\) and the entire opposite product. This leaves the full short \(\mu(d)/d\) harmonic, arbitrarily log-small by [the high-cut calibration, §1](Proof.md), even when orientations are reversed in (3). Each other label is then charged by its absolute **reciprocal** sum and the true \(Q_y(m)\) is retained at its endpoint. Thus the zero mode is arbitrarily log-small. It is not asserted that uniform averaging of the two true primes on this support would itself follow from a one-variable prime theorem.

## 2. Cutoff and weights of the actual inverse frequencies

Write \(X=p_{\rm scale}\), \(R=r_{\rm scale}\), \(P_F=F_0 X\), \(P_H=H_0 R\), and \(J_*=uP_FP_H/N\). On each fixed box and for retained \(u\), all extra factors are subpower. For any sufficiently small fixed \(\varepsilon>0\), frequencies \(|j|>N^\varepsilon\max(1,J_*)\) have a power-small total, by arbitrarily high fixed derivatives in the central smooth transform. Indeed the bound per pair is a fixed log power times \(J_*^{-1}(1+|j|/J_*)^{-A}\); the fixed number of derivatives \(A\) can be chosen after the power margin. On the retained frequencies, \(0<|j|\ll N^{\alpha+\beta-1+\varepsilon+o(1)}<r\), since \(\alpha\le .58\) and both exponents are at least \(1/2-o(1)\). This proves \(r\nmid j(N/u)\), using \((r,N)=1\).

At fixed \(j,r\) the supremum and total variation in \(p\) of the smooth prefactor in (3) are bounded by
\[
 W_j\ll L^{O(1)} J_*^{-1}(1+|j|/J_*)^{-2}.
\]
By increasing the differentiated smooth norms one obtains this also for short independent \(p\)-intervals. Its sum over nonzero \(j\) is \(O(L^{O(1)})\) uniformly, including \(J_*<1\). The factor \(\log p\) adds only a log power. Partial summation can be done with a common real integration variable in \(p\), interchanging its integral with the sum of absolute estimates over \(r\); no theorem with a per-modulus maximizing endpoint is needed. In removing the \(O(1)\) target-prime values of \(p\), the total is \(O_D(N^{\beta+o(1)})\), using this summed harmonic bound and the fixed outer-label counts. Every other varying factor of (3) in \(r\) is dominated by its actual logarithm or its fixed unit/restriction mask.

## 3. Direct maximal-numerator estimate

For each fixed retained \(j\), put \(g=(j,H)=(j,H_0)\) since \(r\nmid j\). Thus \(g\) is fixed on this assignment and \(H/g\asymp H_0R/g=N^{\beta+o(1)}\). The phase of (3) is exactly an inverse modulo \(q=H/g\) with unit numerator
\[
 a_q=(j/g)(N/u)\overline{F_0}\pmod q.
\]
Here \(g\mid j\), \((j/g,H/g)=1\), (N/u) is a target unit modulo \(q\), and \(F_0\) shares no prime with \(H\). The map from actual genuinely prime \(r\) into moduli \(q\) is injective. Apply [Irving, Theorem 1.1](https://arxiv.org/pdf/1301.6372) to an upper bound over **all** moduli in that dyad, with \(q\)-dependent unit \(a_q\) within its stated maximum. The size range \(q_{\rm scale}^{2/3}\le X\le q_{\rm scale}^{3/2}\) holds with room in these boxes. The proof in his §4 permits any real fixed prefix of \(X<p\le2X\), with the same constants: the product condition in the Vaughan sums changes only its real endpoints, and the same Fourier separation (or ordinary inner partial summation for Type I) applies. Hence the three actual total exponents before the subpower factors are those of (2). The sum of \(W_j\) and all outer assignments keeps the strict fixed power margin. At \(.526\) the three upper exponents are \(.98625,.9994,.99356\) (last rounded up).

## 4. Fixed numerator and a genuine short-prime-class variant

Let \(a_*=jN/u\). The phase denominator \(H\) in (3) has not changed on the left of the exact identity
\[
 e_H(a_*\overline{F_0p})
 = e_{F_0H}(a_*\bar p)\ e_{F_0}(-a_*\bar H\,\bar p).             \tag{4}
\]
Indeed \(F_0\overline{F_0}\bmod H\) can be corrected by \(H\bar H\bmod F_0\) to give one via CRT. The formula includes \(F_0=1\). Split the actual \(p,H\) at fixed residues modulo \(F_0\); only \(F_0^2=N^{o(1)}\) classes occur, and the last factor is constant on each. At the actual new moduli \(q=F_0H\), \(Q=q_{\rm scale}=F_0H_0R\) and \(XQ=P_FP_H\). The numerator \(a_*\) is fixed across these moduli. It may share primes with the short \(F_0H_0\); in particular no claim of full coprimality is used. It is coprime to the true large prime \(r\). A negative numerator is handled by conjugation.

For clarity the needed **variant**, not the literal statement of Irving's Theorem 1.3, is proved at these moduli. For fixed integers \(q_0,F_0\) with \(F_0\mid q_0\), take any subset of \(q=q_0 r\asymp Q\), \(r\) prime, \(q_0=N^{o(1)}\), \(r\nmid a_*\), and a fixed unit \(b\bmod F_0\). In \(Q^{1/2}\le X\le Q^{4/3}\), the sum over these moduli of absolute prime inverse sums on any independent real prefix of \(X<p\le2X\) with \(p\equiv b\bmod F_0\), with \(\Lambda\) or prime logs, is at most
\[
 N^{o(1)+\eta}\left[
 X+Q^{3/2}{\mathsf V}
 +\left(1+\frac{|a_*|}{XQ}\right)^{1/2}
        \left(QX{\mathsf V}^{-1/2}+Q^{1/2}X^{11/8}\right)
 +QX^{1/2}\right],
\quad {\mathsf V}=\min\{X^{1/3}, Q^{-1/3}X^{2/3}\},              \tag{5}
\]
for any fixed \(\eta>0\) when \(|a_*|\le N^{O(1)}\). Here constants and the \(N^{o(1)}\) can depend on the displayed subpower label bounds. The final term covers the harmless replacement of prime logs by von Mangoldt. The expression \(X\) can be omitted when dominated by the other terms.

To verify (5), perform the same Vaughan splitting as Irving, §§4 and 4.3: in dyadic Type I ranges the short length \(D\le {\mathsf V}\), while the rest is Type II with both lengths between \(\mathsf V\) and \(X/\mathsf V\), product \(\asymp X\). A class \(l n\equiv b\bmod F_0\) separates by the unit residue of one variable. There are at most \(F_0\) choices. In Type II the separated coefficients are allowed by Irving's Lemma 3.2, including its reduction for arbitrary numerator and actual coprimalities. Enlarge the modulus sum after the absolute values to all \(q\asymp Q\). Separate the real product prefix by the same Fourier device of his §4. The longer variable lies in \([X^{1/2},X/\mathsf V]\); the two terms of Lemma 3.2 then give
\[
 \left(1+\frac{|a_*|}{XQ}\right)^{1/2}
       \big(QX{\mathsf V}^{-1/2}+Q^{1/2}X^{11/8}\big)N^{o(1)+\eta}.
\]
No estimate on the correlation of primes with a varying residue class is assumed at this step.

For Type I keep the actual moduli \(q=q_0r\). At fixed shorter \(l\) with \((l,q)=1\), the free longer variable \(n\) lies in a real interval of length \(M\) and one (fixed for that (l)) residue modulo \(F_0\) dividing \(q\). Expand that congruence in additive modes \(kq/F_0\bmod q\). In each full period its complete reciprocal exponential sum has a Ramanujan factor of absolute value one at \(r\), since \(r\mid kq/F_0\) and \(r\nmid a_*\bar l\). Its other factor has size at most \(q_0=N^{o(1)}\). On any incomplete period Fourier completion and the classical prime Weil bound on the \(r\) factor give \(O(q^{1/2}N^{o(1)})\), allowing any added completion mode modulo \(q\). Thus the true free interval contributes \(O((M/q+1+q^{1/2})N^{o(1)})\) uniformly in its position. Optional \(\log n\) follows by ordinary partial summation. Sum the \(D\) choices, using \(DM\asymp X\), then at most \(O(Q)\) moduli, to get \(X+Q^{3/2}\mathsf V\) with the asserted losses. This is the needed extra step for the short prime class in (4); merely adding a weight to the printed theorem would not justify it.

At the smaller prime scale chosen here \(X\le Q N^{o(1)}\), so the two \(\mathsf V\)-terms are bounded by \(Q^{7/6}X^{2/3}N^{o(1)}\). The term \(QX^{1/2}\) is smaller on these boxes. The ranges in (5) are automatic under the displayed restrictions of the theorem. From §2, \(|a_*|/(XQ)=|j|/J_*\) up to fixed dyadic constants, and since the supports start at \(W\) we have \(J_*\ge N^{-o(1)}\). Therefore (5) has the two exponents (1), with at most an added \(\varepsilon/2+\eta+o(1)\). Take these small against \(\Delta\), use the summed weight \(W_j\), and absorb all fixed outer counts and unit truncations. For \(.532\) the largest exponents in (1) are \(.9975\) and \(.97534\) (second rounded up). At \((.501,.569)\) they are \(.973375\) and \(.997834\) (second rounded up). This proves the stated genuine box removal and the threshold for the whole rectangular union.

The improvement over the arbitrary-coefficient reciprocal bound comes from the genuine primality of the shorter **outer** label \(p\), via averaging inverse exponential sums, not from projecting away the zero mode, altering the score, or averaging the Goldbach target. It does not price all over-root prime labels.
