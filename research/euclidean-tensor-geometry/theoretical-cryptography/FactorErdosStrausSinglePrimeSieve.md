# Exact first-layer overlaps and an optimized single-prime Erdős–Straus sieve

A **first-layer class at \(q\)** here means a class furnished by one of the seven congruence families in [Elsholtz–Tao, Proposition 1.9](https://arxiv.org/pdf/1107.1010) whose displayed literal modulus divides \(4q\). For simultaneous conditions the literal modulus is the least common multiple. We project the class to its residue modulo \(q\) on inputs \(n\equiv1\pmod4\).

**Local result.** For a prime \(q>7\), put
\[
 A_q=\{-f\bmod q:f\mid4q+1,\ f\equiv3\pmod4\},\quad
 B_q=\{-g\bmod q:g\mid q+1,\ g\equiv3\pmod4\},\quad
 C_q=\{-g^{-1}\bmod q:g\mid q+1,\ g\equiv3\pmod4\}.
\]
For \(q\equiv1\pmod4\) the whole first layer is their union. Writing \(r_4(q),r_1(q)\) for the corresponding divisor counts of \(4q+1,q+1\), its exact size is
\[
 |A_q\cup B_q\cup C_q|=r_4(q)+2r_1(q)-2\,\mathbf1_{q\equiv2\ (3)}.
 \tag{1}
\]
For \(q\equiv3\pmod4\), the whole first layer is this union together with \(\{-4t\bmod q:t\mid((q+1)/4)^2\}\); formula (1) still counts the three-set portion, not the full four-set union. All these classes are quadratic nonresidues modulo \(q\). For \(q\equiv1\), the relative survivor fraction in any of the six residual prime classes modulo 840 after applying these first layers through \(B\) is
\[
     \exp\bigl(-3\kappa\log B+O((\log\log B)^2)\bigr),
 \qquad \kappa=\frac{\zeta(2)\zeta(3)}{12\zeta(6)}.
 \tag{2}
\]
As in the [earlier first-family calculation](FactorErdosStrausPrimePowerCoverage.md), the prime density here is taken first, for every fixed \(B\).

**Growing-sieve result.** Fix any integer numerator \(K\ge2\). At each prime \(q>\max(7,K)\) with \(q\equiv-1\pmod K\), mark the distinct residues
\[
 \Omega_K(q)=\{-a h^{-1}\bmod q:\ a,h\ge1,\ (a,h)=1,\
               a h\mid(q+1)/K,\ a h\le\sqrt q\}.
 \tag{3}
\]
Every marked residue gives a positive three-unit-fraction identity for \(K/n\). With
\[
  \gamma_K=
 \frac{\zeta(2)}{8\varphi(K)\zeta(4)}
       \prod_{p\mid K}\frac{p^2-1}{p^2+1},
 \tag{4}
\]
the exact mean number of marks is
\[
  \sum_{q\le X}|\Omega_K(q)|=
        \gamma_K X\log X+O_K(X\log\log X).
 \tag{5}
\]
Here and below absent auxiliary primes have no marks. The number of positive integers \(n\le N\) avoiding **these specified marks alone** at all \(q\le\sqrt N\) is at most
\[
 N\exp\left(-3(\gamma_K/16)^{1/3}(\log N)^{2/3}
                 +O_K((\log N)^{1/3}\log\log N)\right).
 \tag{6}
\]
In particular \(\gamma_4=9/(16\pi^2)\) and the leading coefficient in (6) is \(3(9/(256\pi^2))^{1/3}\approx0.4581653\). For this recipe the main exponent in the large-sieve denominator is an asymptotic equality, not just a lower estimate; §5 also supplies its exact trade-off when the prime cutoff is smaller.

**Relation to prior work.** [Vaughan](https://doi.org/10.1112/S0025579300002886) introduced the classical single-prime large-sieve method and the \(2/3\) exponent. [Pomerance–Weingartner, §4](https://math.dartmouth.edu/~carlp/ESS-ExceptionsV8.pdf) generalize it and give order-of-magnitude local weight estimates. [Dahan, §4](https://arxiv.org/abs/2608.24035) sharpens explicit constants for a different two-parameter witness-depth truncation, with separately bounded parameters and a lower restriction on the auxiliary prime. Here the product cutoff depends on that prime, the residue sets are specified exactly, and the entire squarefree denominator is evaluated by a tilt instead of a one-sided Rankin truncation. Neither (6) nor the local classification improves the \(3/4\) exponent for the unrestricted exceptional set in [Trybushnyi](https://arxiv.org/abs/2611.14167). These are statements about the specified congruences, not a solution of the conjecture or an optimality claim over other sieves.

## 1. The seven local families

In the first Type I display, \(ad=1\) gives no hit on \(1\bmod4\). At \(ad=q\), the option \(a=q,d=1\) gives \(f\mid4q^2+1\). This sum of two squares has no odd prime divisor \(3\bmod4\), so it has no divisor \(f\equiv3\pmod4\). The option \(a=1,d=q\) gives exactly \(A_q\). In the first Type II and fourth Type I displays, the nontrivial product \(ab=q\) has \(a+b=q+1\); the parity condition is \(g\equiv3\pmod4\), giving \(B_q,C_q\).

In the second and third Type I displays, the extra modulus \(f\) is coprime to the \(4\)-multiple, and hence is \(1\) or \(q\). Likewise the extra modulus \(e\) of the third Type II display is \(1\) or \(q\). If \(q\equiv1\pmod4\), these choices always force \(n\equiv-1\pmod4\), and the remaining (second) Type II display requires \(f\equiv3\pmod4\) with \(f\mid4q\), impossible. If \(q\equiv3\pmod4\), the only possible extra modulus in those three displays is \(q\), forcing the product contributing to the \(4\)-multiple to be 1. The second Type I then gives \(-1\bmod q\); the third Type I requires \(n^2\equiv-4\bmod q\) and gives nothing; the third Type II gives \(-4\bmod q\). In the second Type II we have \(f=q\), \(4ad\mid q+1\) and residue \(-4a^2d\). With \(M=(q+1)/4\), the possible values \(a^2d\) are exactly the divisors of \(M^2\): at each prime of exponent \(m\) in \(M\), every \(s\in[0,2m]\) is \(2i+j\) with \(i,j\ge0\), \(i+j\le m\). This set already contains the residues \(-1,-4\) (take \(t=M,1\)). This proves the local characterization.

The distinct \(f\)'s have different residues because their differences are divisible by 4, have magnitude less than \(4q\), and cannot be divisible by \(q\) too. For each \(g\), let \(h=(q+1)/g\); it gives \(g^{-1}\bmod q\). Both \(g,h\) are strictly between 0 and \(q\), and \(g\) is odd and \(h\) even, so \(B_q\cap C_q=\varnothing\). If \(f\equiv g\bmod q\) then \(f-g\) is divisible by \(4q\), hence zero. The only common divisor \(3\bmod4\) of \(4q+1,q+1\) is 3 when \(q\equiv2\bmod3\). For a collision \(f\equiv h\bmod q\), if \(q\equiv1\bmod4\) then \(h\equiv2\bmod4\), and if \(q\equiv3\bmod4\) then \(h\equiv0\bmod4\). In both cases \(f-h=kq\) implies \(k\equiv1\bmod4\) and \(-q<f-h<4q\), so \(f=q+h\). As \(h\le(q+1)/3\), the quotient \((4q+1)/f\) is odd, at most 3, and not 1. Thus \(f=(4q+1)/3\), giving \(h=(q+1)/3\), again precisely when \(q\equiv2\bmod3\). This proves (1).

For any such \(f\) or \(g\), reciprocity gives \(({-f}/q)=(q/f)=(-1/f)=-1\), and the same with \(g\), since the witness modulus has \(4q\equiv-1\) or \(q\equiv-1\). Inversion preserves this sign for the negative inverses. If \(q\equiv3\bmod4\), every odd prime factor \(\ell\) of \(M\) is a quadratic residue modulo \(q\) by reciprocity and \(q\equiv-1\bmod\ell\). If \(M\) is even, \(q\equiv7\bmod8\) gives the same for 2. Hence \(-4t\) has sign \(-1\) in that case.

## 2. Averaging the complete \(q\equiv1\) layer

Let \(P_o=\prod_{p>2}(1+1/(p(p-1)))\). The elementary reciprocal-totient sums used in the [earlier note](FactorErdosStrausPrimePowerCoverage.md) are
\[
 \sum_{d\le Y,\ d\ {\rm odd}}\frac1{\varphi(d)}
       =\frac{P_o}{2}\log Y+O(1),\qquad
 \sum_{d\le Y,\ d\equiv3\ (4)}\frac1{\varphi(d)}
       =\frac{P_o}{4}\log Y+O(1).
\]
For example, expand \(d/\varphi(d)=\sum_{e\mid d}\mu^2(e)/\varphi(e)\) and apply the harmonic sum and its bounded modulo-4 twist.

When \(q\equiv1\bmod8\), the odd integer \(M=(q+1)/2\) is \(1\bmod4\). Pairing divisors of \(M\) doubles the count of \(3\bmod4\) divisors below \(\sqrt M\), up to one in a square case. When \(q\equiv5\bmod8\), \(M\equiv3\bmod4\), and exactly one divisor of each pair is \(3\bmod4\); \(r_1(q)\) then counts all divisors below \(\sqrt M\). The square exceptions in a dyadic interval \((X,2X]\) contribute \(O(\sqrt X)\). In each case split divisors at \(Y=\sqrt X/(\log X)^A\). Below \(Y\) use [Bombieri–Vinogradov](https://doi.org/10.1112/S0025579300005313) on the single reduced class given by \(q\equiv-1\bmod d\) and its prescribed class modulo 8. Above \(Y\) use Brun–Titchmarsh and the reciprocal-totient sums, giving \(O(X\log\log X/\log X)\). The main coefficient is \(P_o/16\) for each of the two classes: for \(1\bmod8\) use double the \(3\bmod4\) divisor sum divided by \(\varphi(8)\); for \(5\bmod8\) use the full odd sum divided by \(\varphi(8)\). Thus
\[
 \sum_{\substack{X<q\le2X\\q\equiv1\ (4)}} r_1(q)
       =\frac{P_o}{8}X+O(X\log\log X/\log X).
\]
The same main coefficient for \(r_4(q)\) was proved in the earlier note by pairing the divisors of \(4q+1\). The overlap term of (1) contributes only \(O(X/\log X)\). Therefore the union has three times the previous first-family mean. As \(|A_q\cup B_q\cup C_q|\ll_\epsilon q^\epsilon\), the quadratic error in the logarithm of the fixed-\(B\) product converges. Use CRT, prime equidistribution in each fixed product modulus, and partial summation to get (2), since \(P_o/8=\kappa\).

## 3. The thin ratio set and its exact arithmetic mean

For (3), every \(a,h\le\lfloor\sqrt q\rfloor\). Two equal ratios modulo \(q\) have cross-products less than \(q\), hence equal as integers. Coprimality makes the pairs identical. Each product \(d=ah\) contributes \(2^{\omega(d)}\), by assigning every prime power in \(d\) wholly to one side. Thus
\[
          |\Omega_K(q)|
             =\sum_{\substack{d\mid(q+1)/K\\d\le\sqrt q}}2^{\omega(d)}.
 \tag{7}
\]
Given a mark, write \(c=(q+1)/(Kah)\), \(u=(n+Ka^2c)/q\), and \(b=hu-a\). The congruence implies \(u\in\mathbb N\) as \(Kach=q+1\). In fact \(b=(hn+a)/q>0\). Then \(Kabhc=hn+a+b\), so
\[
       \frac K n=\frac1{abc}+\frac1{ahcn}+\frac1{bhcn}.
\]
For \(K=4\) this is the thin product-restricted part of the second Type II family. We allow equal positive denominators in this general-numerator convention.

The reciprocal-totient sum needed for (7) is
\[
 \sum_{d\le Y}\frac{2^{\omega(d)}}{\varphi(Kd)}
       =\frac{c_K}{2}(\log Y)^2+O_K(\log(2Y)),\qquad c_K=8\gamma_K.
 \tag{8}
\]
To see this, write it as a sum over \(ah\le Y\), \((a,h)=1\). Normalize the two-variable local coefficients by pulling out \(1/\varphi(K)\). The function to be summed with weight \(1/(ah)\) then has at a prime \(p\) coefficient 1 at exponents \((0,0)\), coefficient \(b_p=1\) if \(p\mid K\) and \(p/(p-1)\) otherwise when exactly one exponent is positive, and zero when both are positive. Dividing its local series by the series for the constant function in both coordinates leaves
\[
 1+(b_p-1)(x+y)+(1-2b_p)xy .
\]
Consequently the Dirichlet-convolution coefficients left after removing the constant functions are absolutely summable with weight \(1/(ah)\), even with \((1+\log(ah))^2\). This follows from convergence of \(\sum_p(\log p)^2/p^2\). The harmonic sum of \(1/(ah)\) over \(ah\le Z\) is \(\tfrac12\log^2 Z+O(\log(2Z))\), by comparing the one-variable inner harmonic sum and then integrating \(\log(Z/t)/t\). Inserting this in the convolution gives (8), including the error from extending the leading coefficient to infinity. Its local factors are \((1-1/p)^2(1+2b_p/(p-1))\), equal to \(1-1/p^2\) if \(p\mid K\) and \(1+1/p^2\) otherwise. This gives (4).

For \(X<q\le2X\), use \(Y=\sqrt X/(\log X)^A\). All \(d\le Y\) are included in (7) when \(q\equiv-1\bmod Kd\). Apply Bombieri–Vinogradov with the multiplicity \(2^{\omega(d)}\). For clarity, if \(E_d\) is the absolute prime-count error for this dyadic interval and modulus \(Kd\), then
\[
 \sum_{d\le Y}2^{\omega(d)}E_d
 \le \left(\sum E_d\right)^{1/2}
       \left(\sum 4^{\omega(d)}E_d\right)^{1/2}.
\]
Brun–Titchmarsh gives \(E_d\ll_K X/(\varphi(Kd)\log X)\). Since \(4^{\omega(d)}/\varphi(Kd)\le\tau_8(d)/d\), the second squared factor is \(O_K(X(\log X)^7)\). Taking \(A\) large enough gives a negligible error by Bombieri–Vinogradov. The tail \(Y<d\le\sqrt{2X}\) is bounded by Brun–Titchmarsh and the difference of the two sums in (8), giving \(O_K(X\log\log X)\). The main term is \(\gamma_K X\log X\), since \(\log Y=\tfrac12\log X+O(\log\log X)\). Sum over dyadic intervals to get (5).

## 4. The large-sieve denominator and its saddle point

For a general collection of marks \(\Omega(q)\) of size \(w_q<q\), set \(a_q=w_q/(q-w_q)\), and for squarefree \(d\) put \(a_d=\prod_{q\mid d}a_q\), with \(a_1=1\). The large-sieve denominator is
\[
                H(D;B)=\sum_{\substack{d\le D,\ d\ {\rm squarefree}\\q\mid d\Rightarrow q\le B}}a_d .
\]
The number \(S\) of survivors through \(B\) in \([1,N]\) is \(\ll(N+D^2)/H(D;B)\). One way to see the relevant weight precisely is to take at each \(q\) a function which is 1 on the allowed residues and \(-(q-w_q)/w_q\) on the marks, omitting \(w_q=0\). Its mean is zero and its Fourier norm squared, with normalized counting measure, is \((q-w_q)/w_q\). Products of these functions have Fourier support on primitive residues modulo \(d\) by CRT, and equal 1 on all survivors. Cauchy–Schwarz therefore lower-bounds the primitive Fourier sum of squares of the survivor indicator at each \(d\) by \(S^2a_d\). Sum over \(d\le D\) and use [Montgomery–Vaughan's large sieve](https://doi.org/10.1112/S0025579300004708); \(d=1\) contributes \(S^2\).

In the case of (3), \(\sum_{q\le e^y} a_q =(\gamma_K/2)y^2+O_K(y\log(2+y))\) by (5) and partial summation. Replacing \(w_q/q\) by \(a_q\) costs a convergent sum because (7) gives \(w_q\le\tau(((q+1)/K)^2)=O_\epsilon(q^\epsilon)\). Put \(L=\log D\), \(\gamma=\gamma_K\), and
\[
 F(s)=\prod_q (1+a_q q^{-s}).
\]
Expansion and Stieltjes partial summation give, as \(s\downarrow0\),
\[
 \log F(s)=\gamma s^{-2}+O_K(s^{-1}\log(1/s)).
\]
Indeed the squares of \(a_q\) sum to a finite amount and the leading Stieltjes measure is \(\gamma y\,dy\). More generally multiplying that measure by \(y\) and \(y^2\) gives the first two tilted moments. Under probabilities proportional to \(a_d d^{-s}\) on squarefree \(d\), prime inclusions are independent with odds \(a_q q^{-s}\), so
\[
 {\mathbb E}_s\log d=2\gamma s^{-3}+O_K(s^{-2}\log(1/s)),
       \qquad \operatorname{Var}_s(\log d)=O_K(s^{-4}).
\]
The corrections from approximating the inclusion probabilities by their odds are bounded since \(\sum a_q^2(\log q)^2<\infty\). These estimates also ensure that the displayed probability distribution is well-defined for \(s>0\).

The upper bound \(H(D;\infty)\le e^{sL}F(s)\) at \(s_0=(2\gamma/L)^{1/3}\) gives the desired leading constant. For a matching lower bound take \(s=s_0(1+C s_0\log(1/s_0))\) with \(C\) a sufficiently large fixed constant. The expectation then falls between \(L-C_2s_0^{-2}\log(1/s_0)\) and \(L-C_1s_0^{-2}\log(1/s_0)\) for positive constants \(C_2>C_1\). Chebyshev places \(1-o(1)\) of the tilted mass between \(L-2C_2s_0^{-2}\log(1/s_0)\) and \(L\). Undoing the tilt on that interval gives the reverse bound up to \(O_K(L^{1/3}\log L)\) in the logarithm. We conclude
\[
 \log H(D;\infty)=3(\gamma_K/4)^{1/3}L^{2/3}
           +O_K(L^{1/3}\log L).
 \tag{9}
\]
Use \(B=D=\lfloor\sqrt N\rfloor\), for which \(H(D;D)=H(D;\infty)\), to obtain (6).

## 5. The exact finite-cutoff trade-off for the denominator

The same argument gives a generally applicable cutoff rule. Suppose nonnegative prime weights satisfy \(a_q=O_\epsilon(q^{-1+\epsilon})\) and
\[
 \sum_{\log q\le y}a_q=\frac{C}{\rho}y^\rho+o(y^\rho),
     \qquad C>0,\quad \rho\in\{1,2\}.
\]
With \(\log B=\beta L^{1/(\rho+1)}\), fixed \(\beta>0\), the logarithm of \(H(D;B)\) divided by \(L^{\rho/(\rho+1)}\) tends to
\[
 \inf_{u\ge0}\left\{u+C\int_0^\beta x^{\rho-1}e^{-ux}\,dx\right\}.
 \tag{10}
\]
To verify this, set \(v=L^{1/(\rho+1)}\) and tilt at \(s=u/v\). The log partition function divided by \(v^\rho\) tends to the integral with coefficient \(C\), by rescaling the cumulative weight measure and partial summation on \([0,\beta]\). The mean of \(\log d\), divided by \(L=v^{\rho+1}\), tends to \(C\int_0^\beta x^\rho e^{-ux}\,dx\); its variance is \(O(v^{\rho+2})=o(L^2)\). The upper bound follows from \(e^{sL}F(s)\). For the lower bound, if the minimizing \(u\) is positive, the limiting mean is 1 there; take instead any slightly larger \(u\), use the tilted mass near its smaller mean, and then let \(u\) decrease to the minimizer. At a minimizing \(u=0\) with limiting mean below 1, concentration at zero tilt works directly; at equality use the same small positive tilt. This proves (10). The switch is precisely \(C\beta^{\rho+1}/(\rho+1)=1\).

Take \(C=\gamma_K,\rho=2\) for (3), or \(C=3\kappa,\rho=1\) for (1) on \(q\equiv1\bmod4\). In the latter case the untruncated analogue yields \(\log H(D;\infty)\sim2\sqrt{3\kappa\log D}\), by the same tilt with Stieltjes measure \(3\kappa\,dy\) on \([0,\infty)\). Thus that complete \(q\equiv1\) layer alone gives a moving upper bound \(N\exp(-(\sqrt{6\kappa}+o(1))\sqrt{\log N})\) on survivors in the initial \(1\bmod4\) classes.

Run `python3 verify_erdos_straus_single_prime_sieve.py` for exact finite checks of all seven local projections, the overlaps and explicit decompositions, uniqueness of ratio labels, and Euler-factor identities. The script does not validate an analytic prime distribution theorem, and no formalization or extension of a numerical verification range is claimed.
