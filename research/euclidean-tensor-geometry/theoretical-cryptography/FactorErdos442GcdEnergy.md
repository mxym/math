# Two-term harmonic-mass asymptotics at fixed reciprocal-LCM energy

Research note, 27 November 2026. This is a quantitative refinement of an already solved problem, not a new resolution of Erdős #442.

For nonempty \(D\subseteq[1,x]\cap\mathbb N\), write
\[
 H(D)=\sum_{n\in D}\frac1n,\qquad
 K(D)=\frac{1}{H(D)^2}\sum_{n,m\in D}\frac1{\operatorname{lcm}(n,m)} .
\]
The sum uses ordered pairs and includes the diagonal. Equivalently, \(K(D)=\mathbb E\gcd(\mathbf n,\mathbf m)\) for independent draws of law \(1/(nH(D))\) on \(D\). Fix \(c>0\). Set \(L=\log\log x\) and
\[
 \Phi_c(L)=\frac c2\sqrt L\log L+c(1-\log c)\sqrt L.
\]

**Theorem.**

1. If \(M_c(x)=\max_{K(D)\le e^{c^2}}H(D)\), then
   \[
   \log M_c(x)=\Phi_c(L)+O_c(\log L).
   \]
2. For each integer \(r\ge2\), a single infinite set \(A=A(c,r)\) of squarefree numbers satisfies for all sufficiently large real \(x\)
   \[
     K(A\cap[1,x])\le e^{c^2},\qquad
     \log H(A\cap[1,x])=\Phi_c(L)+O_{c,r}\!\left(L^{1/(2r)}(\log L)^2\right).
   \]
   In fact \(K(A\cap[1,x])\to e^{c^2}\). Thus for each fixed \(\varepsilon>0\) the remainder in this assertion can be made \(O_{c,\varepsilon}(L^\varepsilon)\) by choosing \(r\) large enough.

The first term in the upper bound is already due to Will Sawin in Appendix A of [Tao, arXiv:2407.04226v5](https://arxiv.org/html/2407.04226v5). The divisor moment below is Sawin's; the upper-bound refinement combines it quantitatively with the exponential tilting used in Tao's proof of Theorem 2(ii). The finite-cutoff lower bound uses Tao's squarefree layer, keeping the leading constant in the energy. For a single infinite set, Tao's Theorem 2(i) gives the leading growth with an implicit multiplicative constant in the defect bound, while his Proposition 1 applies in a specified range of cutoffs. The construction below uses \(r\) compulsory primes from the new interval, rather than varying the cofactor cutoff of a single new prime, and obtains both the exact eventual energy cap and the second growth term uniformly in the cutoff. The [2024 journal text](https://math.colgate.edu/~integers/y100/y100.pdf) predates the arXiv appendix.

## 1. Upper bound at one cutoff

Write \(\omega(n)\) for the number of distinct prime factors, and \(S^*(x)=\sum_{p\le x}1/(p-1)=L+O(1)\) by Mertens. Let \(b(d)=\mathbb P(d\mid\mathbf n)\). The identity
\[
 K(D)=\sum_{d\ge1}\varphi(d)b(d)^2
\]
follows from Gauss's totient sum and independence. For \(t>0\), sum over squarefree divisors and use Cauchy–Schwarz:
\[
 \bigl(\mathbb E(1+t)^{\omega(\mathbf n)}\bigr)^2
 \le K(D)\prod_{p\le x}(1+t^2/(p-1))
 \le K(D)e^{t^2 S^*(x)}.
\]
The product may include divisors exceeding \(x\), which only enlarges the upper bound. Put \(t=c/\sqrt L\); for all sufficiently large \(x\), \(0<t<1\). Jensen gives
\[
 \mathbb E\omega(\mathbf n)\le
 \frac{c^2+t^2 S^*(x)}{2\log(1+t)}=c\sqrt L+O_c(1).
\]
A second use of Jensen, to \(t^{\omega(\mathbf n)}\), gives
\[
 H(D)t^{\mathbb E\omega(\mathbf n)}
 \le \sum_{n\in D}\frac{t^{\omega(n)}}n
 \le \prod_{p\le x}(1+t/(p-1))
 \le e^{t S^*(x)}.
\]
The middle product includes all prime-power exponents: \(\sum_{a\ge1}p^{-a}=1/(p-1)\). Taking logs and using \(\log(1/t)=\tfrac12\log L-\log c\) proves the claimed upper bound. No squarefreeness assumption was made on \(D\).

## 2. Squarefree product boxes

For a finite prime set \(\mathcal P\), let \(W_m(\mathcal P)\) be the family of products of \(m\) distinct primes from it, and \(B_m(\mathcal P)\) the sum of their reciprocals. The empty product is \(1\). Set \(S=\sum_{p\in\mathcal P}1/p\) and \(S_2=\sum_{p\in\mathcal P}1/p^2\). For \(S>0\), the ordered-tuple collision bound is
\[
 \frac{S^m}{m!}\left(1-\binom m2 S_2/S^2\right)
 \le B_m(\mathcal P)\le \frac{S^m}{m!}.
 \tag{1}
\]
In fact the unrestricted ordered mass is \(S^m\), and the mass lost for each chosen equal pair is \(S^{m-2}S_2\). Also, for \(\mathcal P'\subseteq\mathcal P\), loss of at least one prime gives
\[
 B_m(\mathcal P)-B_m(\mathcal P')\le
 (S-S')S^{m-1}/(m-1)!\qquad(m\ge1).
 \tag{2}
\]

For any finite set \(F\), let
\[
 V(F)_d=\sqrt{\varphi(d)}\sum_{\substack{n\in F\\d\mid n}}1/n .
\]
Thus \(\|V(F)\|_2^2=H(F)^2 K(F)\) for nonempty \(F\). All coordinates are nonnegative. If \(F\) and \(G\) use disjoint prime supports, their product box \(FG\) has unique representations, and multiplicativity of \(\varphi\) gives
\[
 H(FG)=H(F)H(G),\qquad \|V(FG)\|_2=\|V(F)\|_2\|V(G)\|_2.
 \tag{3}
\]
For \(F=W_m(\mathcal P)\), a divisor \(d\) made up of \(\ell\le m\) distinct primes from \(\mathcal P\) has unweighted coordinate at most \(d^{-1} S^{m-\ell}/(m-\ell)!\). Since \(\varphi(d)/d^2\le1/d\), summing over rank \(\ell\) bounds its contribution to the squared norm by
\[
 \frac{S^{2m-\ell}}{\ell!\,(m-\ell)!^2}.
 \tag{4}
\]
Consequently when \(S\asymp_c m^2\) and \(m\to\infty\), (1), (4), and \((m)_\ell\le m^\ell\) yield
\[
 \|V(W_m(\mathcal P))\|_2
 \le B_m(\mathcal P)\left(1+O_c(m^{-2})\right)e^{m^2/(2S)}.
 \tag{5}
\]
Indeed, \(S_2\) is absolutely bounded, so the relative error in (1) is \(O_c(m^{-2})\), and the sum of (4) divided by \((S^m/m!)^2\) is at most \(e^{m^2/S}\).

For fixed rank \(r\ge2\) and any prime set \(\mathcal Q\) of reciprocal sum \(u\), (1) with \(S_2\le u\) gives
\[
 B_r(\mathcal Q)=u^r/r!+O_r((u+1)^{r-1}).
 \tag{6}
\]
The \(d=1\) coordinate is exactly this mass. Formula (4) sums the other ranks to \(O_r((u+1)^{2r-1})\) in squared norm. For large \(u\), divide the difference of squares by a denominator at least \(B_r(\mathcal Q)\gg_r u^r\); for bounded \(u\), both norms are bounded by (4). Hence uniformly, including when the family is empty,
\[
 \|V(W_r(\mathcal Q))\|_2\le B_r(\mathcal Q)+O_r((u+1)^{r-1}).
 \tag{7}
\]

**Finite-cutoff lower bound.** Let \(m=\lfloor c\sqrt L-1\rfloor\), and take \(D=W_m(\{p:p\le x^{1/m}\})\). Then \(D\subseteq[1,x]\) and \(S=L-\log m+O(1)\). We have \(m^2/S\le c^2-\Omega_c(L^{-1/2})\) since \(m\le c\sqrt L-1\) and \(\log m/L=o(L^{-1/2})\). The relative norm error in (5) is \(O_c(L^{-1})\), so \(K(D)\le e^{c^2}\) for sufficiently large \(x\). By (1) and Stirling,
\[
 \log H(D)=m\log L-m\log m+m+O_c(\log L)=\Phi_c(L)+O_c(\log L).
\]
This proves part 1.

## 3. One set that works at every sufficiently large cutoff

Fix \(r\ge2\) and, for sufficiently large integers \(j\), let
\[
 L_j=j^2/c^2+j^{1+1/r}\log j,\qquad Y_j=\exp(\exp L_j).
\]
For each \(j\ge j_0(c,r)\), take all products of \(j\) primes from
\(\mathcal P_j=\{p:p\le Y_j\}\) and \(r\) primes from
\(\mathcal Q_j=\{p:Y_j<p\le Y_{j+1}\}\), all distinct. Call this box \(A_j\) and let \(A=\bigcup_{j\ge j_0}A_j\). These are disjoint families, already by their largest prime. We reserve \(r\) fresh primes so that, during the transition to a new box, its mass grows like the \(r\)-th power of the newly available reciprocal prime mass, without concentrating a large proportion of the whole set on an initially short prime interval.

Choose \(k\) by \(Y_k\le x<Y_{k+1}\). Stages \(j>k\) cannot contribute. For \(j\le k\), define
\[
 B_j=B_j(\mathcal P_j),\quad S_j=\sum_{\mathcal P_j}1/p,\quad
 \mathcal Q_j(x)=\{p:Y_j<p\le\min(Y_{j+1},x)\},\quad
 u_j=\sum_{\mathcal Q_j(x)}1/p,
 \quad U_j=B_j B_r(\mathcal Q_j(x)).
\]
Here and below \(B_j\) without a prime-set argument denotes the reservoir mass. The full product box with \(\mathcal Q_j(x)\) before the product-size cutoff will be denoted by \(F_j(x)\); \(U_j\) is its mass. Put \(u=u_k\). By Mertens, \(S_j=L_j+O(1)\sim j^2/c^2\), \(L_{j+1}-L_j\sim 2j/c^2\), hence \(u_j\asymp_c j\) for \(j<k\) and \(u\ll_c k\). Also
\[
 B_{j+1}/B_j\asymp_c j.
 \tag{8}
\]
Indeed \(B_j=(1+O_c(j^{-2}))S_j^j/j!\) by (1), and \(S_{j+1}/S_j=1+O_c(1/j)\). Increasing \(j_0\) if needed, the ratios in (8) exceed \(2\). In particular
\[
 U_{k-1}\asymp_{c,r} B_k k^{r-1},
 \qquad \sum_{j_0\le j\le k-2} B_j(j+1)^r\ll_{c,r} B_k k^{r-2}.
 \tag{9}
\]

### Product-size cutoff

Put \(H_j=H(A_j\cap[1,x])\), using \(0\) for an empty family. Certainly \(H_j\le U_j\). For a lower bound, cap reservoir primes at \(x^{1/(2j)}\) and fresh primes at \(x^{1/(2r)}\): the selected products are at most \(x\). Since \(x\ge Y_j\), the first cap loses \(O(\log(2j))\) from \(S_j\). The second cap loses \(O_r(1)\) from \(u_j\), by Mertens on \((x^{1/(2r)},x]\); intersecting with the fresh interval cannot increase this loss. Apply (2) to each factor of the product mass and (1) to the reservoir:
\[
 0\le U_j-H_j\ll_{c,r} B_j\left((u_j+1)^{r-1}
           +\frac{\log(2j)}j\,u_j^r\right).
 \tag{10}
\]
For \(j=k-1\), this is \(o(U_{k-1})\). For \(j=k\), if \(u\ge k^{1-1/r}\), (6) and (10) give \(H_k\gg_r B_k u^r\) for large \(k\); for \(u<k^{1-1/r}\), the previous stage suffices. Together with (9) and \(H_j\le U_j\),
\[
 H:=H(A\cap[1,x])\asymp_{c,r} B_k(k^{r-1}+u^r).
 \tag{11}
\]
For all \(u\ge0\),
\[
 \frac{(u+1)^{r-1}}{k^{r-1}+u^r}\ll_r k^{-1+1/r}.
 \tag{12}
\]
Split at \(u=k^{1-1/r}\); below this point use \(k^{r-1}\) in the denominator, and above it use \(u^r\). Omitting the old stages in the lower bound costs only \(O_{c,r}(H/k)\) by (9). Equations (9)–(12), and \(\log k/k=O_r(k^{-1+1/r})\), yield
\[
 \sum_{j\le k}U_j=H\left(1+O_{c,r}(k^{-1+1/r})\right),
 \qquad \sum_{j\le k}B_j(u_j+1)^{r-1}
      \ll_{c,r} H k^{-1+1/r}.
 \tag{13}
\]

### Energy cap

Triangle inequality and nonnegativity give \(\|V(A\cap[1,x])\|_2\le\sum_{j\le k}\|V(F_j(x))\|_2\). By (3), (5), and (7),
\[
 \|V(F_j(x))\|_2\le
 (1+O_c(j^{-2}))e^{j^2/(2S_j)}
 \bigl(U_j+O_r(B_j(u_j+1)^{r-1})\bigr).
\]
The mass of the stages \(j\le k-2\) after including their norm contributions is \(O_{c,r}(H/k)\) by (9); their prefactors are bounded. For \(j=k-1,k\),
\[
 \frac{j^2}{S_j}\le c^2-\Omega_c(k^{-1+1/r}\log k),
\]
because \(S_j=j^2/c^2+j^{1+1/r}\log j+O(1)\). The relative loss here dominates both the error in (13) and \(O_c(k^{-2})\). Upon dividing by \(H\), the last three displays give \(\|V(A\cap[1,x])\|_2/H\le e^{c^2/2}\) for all sufficiently large \(x\), as required. This argument does not require independence of different stages, nor does it replace the common integer cutoff by a cutoff on each prime: the latter boxes were used only to upper-bound nonnegative coordinates, and (10) controlled the mass discarded.

### Uniform two-term growth and limiting energy

Equation (11) gives \(\log H=\log B_k+O_{c,r}(\log k)\). Since \(L\in[L_k,L_{k+1})\), \(S_k=L+O_c(k)\) and
\[
 k=c\sqrt L+O_{c,r}\!\left(L^{1/(2r)}\log L\right).
\]
From Stirling in (1),
\[
 \log B_k=k\log L-k\log k+k+O_{c,r}(\log L).
\]
The derivative in \(k\) of the three displayed main terms is \(\log L-\log k=O_c(\log L)\) on the intervening range. Substitute \(c\sqrt L\) to conclude part 2. If the energy stayed at most \(e^{(c')^2}\) infinitely often for any fixed \(0<c'<c\), part 1 applied at those cutoffs would contradict the leading term of this growth formula. Together with the eventual upper cap this gives the stated limit. Subtracting the diagonal and dividing by two, the normalized unordered sum in the original problem therefore tends to \(e^{c^2}/2\) for this set.

## Exact finite checks

Run [verify_erdos442_gcd_energy.js](verify_erdos442_gcd_energy.js) with Node.js. It uses integer arithmetic to check the divisor-square and divisor-moment identities, their Cauchy–Schwarz bound, the product-box identities, the weighted subset losses, and the elementary transition estimate on finite ranges. These are checks of the proof's finite identities, not a substitute for the asymptotic argument. No statements are made about exact maximizing subsets at each cutoff or about the \(O(\log L)\) remainder for a single infinite set.
