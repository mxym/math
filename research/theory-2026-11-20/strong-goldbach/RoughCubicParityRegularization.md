# Regularizing the cubic parity term on actual polynomially rough complements

This is an exact complementary-divisor decomposition and a uniform fixed-target **absolute bound** for its twisted summand. It transfers, rather than resolves, the parity debt. In particular the untwisted half-divisor expression still carries the physical roughness restriction. When the roughness exponent is greater than \(1/6\), the whole even debit in this version is precisely two actual cohorts, rank two and rank four, with opposite signs.

Let \(N=2x\), \(L=\log x\), \(n\in I=(x/2,x]\), \(m=N-n\), and \((n,N)=1\). Fix \(0<\kappa<1/2\), let \(z=x^\kappa\), and write \(\mathcal R_\kappa\) for the squarefree \(n\in I\) with \(P^-(n)>z\). Primality of the other leg is represented by actual \(\Lambda(m)\), not a model or arithmetic progression marginal. Write \(\mathfrak S(N)\) for the ordinary Goldbach singular series.

On squarefree \(n\), set
\[
 K_3(n)=3\frac{\Lambda_2(n)}{\log^2 n}-2\frac{\Lambda_3(n)}{\log^3 n},
 \qquad \Lambda_j=\mu*\log^j.
\tag{1}
\]
This is the unique linear combination of the two indicated normalized functions that equals 1 on primes and zero on squarefree semiprimes. At a product of three distinct primes of normalized logarithms \(t_i\), it equals \(-12t_1t_2t_3\), and it vanishes at all higher ranks. Thus it is a genuine prime minorant on this squarefree family. [Arneth, Gold-40, v1](https://zenodo.org/records/23477014) describes a cubic normalized minorant with these properties, its exact roughness bookkeeping, and an unproved signed long term. The public abstract supports that comparison; its full PDF was not accessible, so no assertion is made about the exact overlap of decompositions. [Gold-43, v1](https://zenodo.org/records/23560521) addresses growing Bonferroni depth under its own parity comparison. The present estimate is for the different explicitly regularized operator below.

## 1. Exact half transformation and suppression of its twist

For \(0\le t\le 1/2\) put \(F(t)=1-6t^2+4t^3\). The full divisor kernel in (1) is \((1+F(t))/2\), using the same polynomial on \([0,1]\). For squarefree \(n>1\) the full constant sum is zero. On the paired divisors \(d,n/d\), one has \(F(1-t)=-F(t)\), and \(\mu(n/d)=\lambda(n)\mu(d)\) with \(\lambda(n)=(-1)^{\Omega(n)}\). Hence, writing \(t_d=\log d/\log n\),
\[
 K_3(n)=\frac{1-\lambda(n)}2\sum_{d\mid n,\ d<\sqrt n}\mu(d)F(t_d).
\tag{2}
\]
No tied square-root divisor occurs for these \(n\).

For \(y=4t(1-t)\in[0,1]\), on this **half** interval
\[
 F(t)=(1+y/2)\sqrt{1-y}=1-\sum_{j\ge2}a_j y^j,
 \qquad a_j=b_j+b_{j-1}/2>0,
 \quad b_j=\frac{\binom{2j}j}{4^j(2j-1)} .
\]
This follows from the binomial series; the sum of the \(a_j\) is 1 by monotone convergence at \(y=1\). For any fixed \(J\ge2\) put
\[
 A_J=1-\sum_{2\le j<J}a_j=\sum_{j\ge J}a_j,
 \quad
 g_J(t)=1-\sum_{2\le j<J}a_j y^j-A_Jy^J,qquad h_J(t)=F(t)-g_J(t).
\tag{3}
\]
The polynomial \(g_J\) is symmetric under \(t\mapsto1-t\), has degree \(2J\), and \(g_J(0)=1\), \(g_J'(0)=0\), \(g_J(1/2)=0\). On the half interval \(0\le h_J\le A_J y^J\) and \(0\le g_J\le F\). In particular \(A_J\to0\). One may also use \(A_J\ll J^{-1/2}\) from the stated binomial coefficients, but no rate is necessary. Both \(F\) and \(g_J\) vanish at least linearly from the left at the midpoint, uniformly in \(J\) since \(F(t)=(1-2t)(1+2t(1-t))\) and \(g_J\le F\).

Define the following actual fixed-target sums, all over \(n\in\mathcal R_\kappa\) with the above unit restriction:
\[
\begin{aligned}
 \mathcal H_J(N)&=\sum_n\Lambda(m)\sum_{d\mid n,\ d<\sqrt n}
             \mu(d)\frac{F(t_d)+g_J(t_d)}{2},\\
 \mathcal T_J(N)&=\sum_n\Lambda(m)\sum_{d\mid n,\ d<\sqrt n}
                       \lambda(n/d)h_J(t_d),\\
 \mathcal E_J(N)&=\sum_n\Lambda(m)1_{\lambda(n)=+1}
                      \sum_{d\mid n,\ d<\sqrt n}\mu(d)g_J(t_d).
\end{aligned}
\]
Then the literal identity and estimate are
\[
 \sum_{n\in\mathcal R_\kappa,\ (n,N)=1}\Lambda(m)K_3(n)
      =\mathcal H_J(N)-\mathcal E_J(N)-\tfrac12\mathcal T_J(N),
 \qquad
 |\mathcal T_J(N)|\ll_\kappa A_J\frac{\mathfrak S(N)x}{L}
                                  +O_\kappa(\sqrt{x}L^2).
\tag{4}
\]
The algebra follows by expanding the even indicator in \(\mathcal E_J\), and \(\lambda(n)\mu(d)=\lambda(n/d)\) on these squarefree divisors. In particular no twist at \(d=1\) remains, since \(h_J(0)=0\). This matters: retaining \(\lambda(n)\Lambda(N-n)\) as an uncontrolled summand is unnecessary in this decomposition.

For the actual bound fix \(d\mid n\), \(d>1\), write \(n=dk\), and discard squarefreeness from the **upper** estimate. Both \(d,k\) remain \(z\)-rough, and \(d\le\sqrt{x}\), \(Y=x/d\gg\sqrt x\). The true forms in \(k\) are \(k\) and \(N-dk\). Sieve both using primes below \(w=x^{\min(\kappa/2,1/20)}\), keeping only an upper bound; the second is a prime of order \(x\), so none of the sifted primes equals that value. The number of removed classes is 2 at a prime not dividing \(dN\) and 1 at a prime dividing \(dN\), including at 2, because \((d,N)=1\). The standard two-linear-form Selberg upper bound gives
\[
 \#\{k\asymp Y: P^-(k)>z,\ N-dk\text{ prime in the physical range}\}
        \ll_\kappa \mathfrak S(Nd)Y/L^2 .
\tag{5}
\]
E.g. use the upper square on moduli \(\le w\) with exact CRT counts \(Y\rho(a)/a+O(\rho(a))\) for each squarefree joint modulus \(a\); the fixed exponent \(w\le x^{1/20}\) leaves polynomial room for the sum of floors \(w^{2+o(1)}\) versus \(Y\ge\sqrt x\). The sieve main has the factor \(\prod_{p\le w}(1-\rho(p)/p)\) up to an absolute constant. Its ratio to \(\mathfrak S(Nd)/\log^2 w\) is bounded absolutely by the ordinary Euler-factor calculation, since every additional prime divisor of \(Nd\) above \(w\) would only increase the singular factor. This use of the upper sieve is insensitive to the heights \(N,d\): only these roots and the actual free interval length enter. Since \(d\) is rough and has at most \(1/(2\kappa)\) prime factors, \(\mathfrak S(Nd)\ll_\kappa\mathfrak S(N)\). A one-dimensional rough upper sieve similarly bounds the harmonic count of rough \(d\) at most \(O_\kappa(1/L)\) on each dyad \([D,2D]\) with \(D\gg z\); choose a much smaller fixed power of \(z\) if necessary to reserve floors at \(D\asymp z\). The full harmonic sum over relevant \(d>1\) is therefore \(O_\kappa(1)\). Multiply (5) by \(\log m\ll L\), by \(h_J\le A_J\), and sum to obtain (4). The \(O(\sqrt x L)\) proper prime powers \(m\) give the stated negligible error because each physical rough squarefree \(n\) has at most \(2^{1/\kappa}\) divisors; any squareful \(z\)-rough \(n\) excluded at an earlier stage also has total count \(O(x/z)\) and costs power-small with bounded-degree polynomial divisor weights. Thus for every fixed \(\kappa>0\), given an arbitrary positive error fraction, one first chooses \(J\) sufficiently large depending on \(\kappa\) and the fraction, and only then takes \(x\) large. No estimate on signs of \(\lambda(k)\) is invoked.

The **logarithmic** neck of the untwisted half is harmless on this same support. Replacing \(d<\sqrt n\) in \(\mathcal H_J\) by \(d\le\sqrt{x}/L^C\) for any fixed \(C>0\) changes it by \(o_\kappa(\mathfrak S(N)x/L)\). Indeed the omitted \(d\) occupy only \(O_C(1+\log L)\) dyads, their rough harmonic sum is \(O_{\kappa,C}((1+\log L)/L)\), and \(|F+g_J|\ll_C (1+\log L)/L\) there. Use (5) again, separately paying prime powers as above. This does **not** justify ordinary BV with the polynomial rough mask at all the remaining divisors.

## 2. True even rank two and four

On any even squarefree rank the inner sum in \(\mathcal E_J\) equals half the full symmetric divisor sum for \(g_J\); it vanishes in ranks \(>2J\) by the elementary full finite difference of a polynomial of degree \(2J\). For \(J=2\), \(g_2=1-y^2=2(1-2t)^2-(1-2t)^4\). Its exact even rank-two contribution (before the minus in (4)) is \(16t_1^2(1-t_1)^2\), where \(t_1\) is the smaller logarithm. Its exact rank-four contribution is \(-192\prod_{i=1}^4t_i\) from the fourth difference of its leading coefficient \(-16\). All higher even ranks vanish for this choice, but \(A_2=1\) so it alone gives no small twisted error claim.

Suppose \(\kappa>1/6\). On the actual rough support \(\Omega(n)\le 5\), so the only true even cohorts are these same two ranks, **for every** \(J\). We may write their contributions up to an arbitrarily small fixed-target error using the limiting symmetric half kernel \(F\) on both cohorts. Indeed the pointwise difference at each such \(n\) is at most \(2^{1/\kappa} A_J\). The true rough-prime two-form count (5) with \(d=1\) and the log weight bound its total by \(O_\kappa(A_J\mathfrak S(N)x/L)\), also treating proper prime powers. On rank two the resulting even debit is
\[
                 1-F(t_1)=6t_1^2-4t_1^3>0.
\tag{6}
\]
On rank four the corresponding even term is negative. For a short proof, extend the half kernel evenly in \(u=1-2t\) as \(g_\infty(u)=(3|u|-|u|^3)/2\). Let \(\psi\) be the density of the sum of independent uniform variables on \([-t_i,t_i]\) for the four factors. This is even and unimodal (each convolution preserves the property by interval layer-cake) and is \(C^2\). Thus \(\psi''(0)\le0\) and \(\psi(0)\ge1/2\), since its support is \([-1,1]\). Integrating the four centered differences or their distributional derivative gives
\[
 2\sum_{d\mid n,d<\sqrt n}\mu(d)F(t_d)
   =\Big(\prod_{i=1}^4 2t_i\Big)
       \{3\psi''(0)-6\psi(0)\},
\tag{7}
\]
using \(g_\infty^{(4)}=3\delta''-6\delta\). For rigor one may first convolve \(g_\infty\) with smooth approximate identities; the left converges by continuity, and the right by \(C^2\) convergence of the smoothed test against the delta distributions. Thus the rebate, the negative of the half sum in (7), is at least \(24\prod t_i\).

There is an explicit stronger bound when \(t_4\) is the largest factor logarithm and \(t_4<1/2\), as always here for rank 4. The standard four-box convolution formula, obtained by expanding four finite differences of \(x_+^3/6\), gives
\[
 \Big(\prod 2t_i\Big)\psi''(0)
   =\sum_{d\mid n,d<\sqrt n}\mu(d)(1-2t_d)
   =-4\min(t_1,1/2-t_4)
\]
where \(t_1\) is the smallest. Indeed all singletons are short, no triples are, and the short pairs are \(t_1+t_2\), \(t_1+t_3\), and the smaller of \(t_1+t_4,t_2+t_3\) in increasing factor order. If any pair ties at \(1/2\), its linear summand is zero and the formula still holds. Thus the rebate is at least
\[
               6\min(t_1,1/2-t_4)+24\prod t_i .
\tag{8}
\]
In particular the reserve per **actual** rough rank-four input is strictly positive, since \(t_1>\kappa\), \(t_4<1-3\kappa<1/2\). This is not a lower bound for the occupancy of true rank-four inputs adjacent to a prime.

## 3. What is not paid

If \(1/6<\kappa<1/2\), (4) can consequently be read as follows, for any error fraction and all sufficiently large fixed targets: the true cubic minorant sum is the untwisted rough half moment, **minus the genuine semiprime sum with coefficient (6), plus the genuine four-factor sum with coefficient given exactly by (7)**, up to that error. Both physical even sums retain actual \(\Lambda(N-n)\). They cannot be evaluated by independent prime product counts or by treating the rebate as if its sign implied uniform occupancy. Unrestricted dyadic expectations are not a fixed-target inequality.

The untwisted rough half moment is also not replaced by its heuristic main. A divisor \(d\) of \(n\) requires retaining the condition \(P^-(n/d)>x^\kappa\). On a strict polynomial sublevel \(d\le x^{1/2-\rho}\) one can introduce ordinary fundamental-lemma weights for that mask with level approximately \(x^\rho\), because their coprime product with \(d\) must lie within BV. The available sieve ratio is only \(\rho/\kappa\). Shrinking the unused exponent-width \(\rho\) to zero with fixed \(\kappa\) does not preserve that ratio. The logarithmic-neck bound above does not authorize passing through all this intermediate range. There is thus no claim of a genuine fixed-target inequality for the comparison between (6) and (7), the whole untwisted rough half moment, or the binary Goldbach count.
