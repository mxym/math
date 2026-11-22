# The two zero-endpoint coefficients in the genuine giant correlation

Let \(N\) be an individual large even target, \(J\Subset(0,1)\)
a fixed nondegenerate central interval, \(L=\log N\), and
\(M_N=|J|N\mathfrak S(N)\). Write \(y=N-x\) and
\(R_J(N)=\sum_{x\in NJ,\ x,y\ {\rm prime}}\log x\log y\).
Take two fixed pairs of exponents
\[
       \lambda_F,b_F>0,\qquad \lambda_G,b_G>0,\qquad
       \lambda_F+b_F<1/2,\qquad \lambda_G+b_G<1/2,
\]
with \(U_F=N^{\lambda_F}\), \(U_G=N^{\lambda_G}\).
Use any fixed real smooth \(F,G\) on \([0,\infty)\) supported
in \([0,b_F]\), \([0,b_G]\), respectively. They need not be
flat at zero. With \(t_d(n)=\log(dN/n)/L\) define the true
composite giant weight
\[
 P_F(n)=
 \sum_{\substack{r\mid n,\ r\ {\rm prime}\\U_F<r<n}}
           (\log r)\sum_{d\mid n/r}\mu(d)F(t_d(n)),
\]
and analogously \(P_G\). Only actual prime marks occur.
Put \(a_F=F(0)-(1-\lambda_F)F'(0)\) and
\(a_G=G(0)-(1-\lambda_G)G'(0)\).

**Theorem.** At every large even target, without a radical
condition, the actual centered two-leg correlation is
\[
\begin{split}
 \sum_{\substack{x\in NJ\\(x,N)=1}}P_F(x)P_G(N-x)
    ={}&F(0)G(0)\bigl(R_J(N)-M_N\bigr)\\
      &+(1-\lambda_F)(1-\lambda_G)F'(0)G'(0)M_N
         +o_{F,G,J,\lambda_F,\lambda_G}(M_N).                     \tag{1}
\end{split}
\]
The sum is over integers \(x\); its weights use the stated
genuine primes inside \(x\) and \(N-x\).
Thus the derivative term is exactly rank one across profiles,
and choosing a zero-endpoint derivative on either leg leaves
only the old binary residual. This is not a positivity estimate
for the actual centered correlation. Compare
[the flat-profile correlation](JointSharpGiantCorrelation.md)
and the genuine one-prime
[zero-cutoff calibration](ZeroCutoffExponentialMoment.md).
The present proof uses fixed power slack in both moduli for
its all-even target-unit floors.

## 1. Physical identity, genuine prime crosses, and integer CRT

For each central integer \(n\) define the short divisor model
\[
 A_F(n)=\sum_{d\mid n}\mu(d)F(t_d(n))
            \left\{\log(n/d)
                  -\sum_{\substack{k\mid n/d\\k\le U_F}}\Lambda(k)\right\},
 \qquad
 \Pi_F(n)=1_{n\ {\rm prime}}(\log n)F(t_1(n)).
\]
The function in braces is exactly the sum of all actual
prime-power marks \(>U_F\) dividing \(n/d\). On central \(n\)
the prime \(r=n\) gives exactly \(\Pi_F\). The other genuine
prime marks give \(P_F\); the difference is supported on an
actual proper power \(p^j>U_F\), \(j\ge2\), dividing \(n\).
The number of such physical \(n\) is at most
\(N^{1-\lambda_F/2+o(1)}\), by reciprocal counting of proper
powers and actual multiples. All coefficients are bounded
by fixed divisor powers times \(L\). The same reasoning
applies to \(G\), so in all the products below
\(P_F=A_F-\Pi_F\) and \(P_G=A_G-\Pi_G\) up to \(o(M_N)\).
There is no replacement by unrestricted marks before this
identity.

On the true prime crosses the exact one-leg calibration is
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}A_F(x)\Pi_G(y)
     =a_F G(0) M_N+o(M_N),\qquad
 \sum_{\substack{x\in NJ\\(x,N)=1}}\Pi_F(x)A_G(y)
     =F(0)a_G M_N+o(M_N).                                       \tag{2}
\]
To justify even a varying spatial prime weight here, retain
\(G(t_1(y))\) inside the real prefix BV calculation for the
true prime \(y\) and the exact moduli \(d\) or \(dk\).
These are at most \(N^{b_F+\lambda_F}\), with fixed power
reserve. This weight and the free logs have bounded
log-power variation uniformly in the central interval.
The finite model and the small-endpoint calculation in
[ZeroCutoffExponentialMoment, §§1--2](ZeroCutoffExponentialMoment.md)
then hold *pointwise in the real central integration
parameter*, with the shorter fixed \(U_F=N^{\lambda_F}\).
The large-cutoff part yields \(F(0)\mathfrak S(N)\);
the finite signed \(n\)-prefix atom gives
\(-(1-\lambda_F)F'(0)\mathfrak S(N)\).
Only in the completed model may \(G(t_1(y))\) be replaced
by \(G(0)+O(1/L)\). This yields the first statement (2);
reflect \(x,y\) in the second. Replacing the extra weight
by an absolute error against unsummed \(A_F\) would not
suffice. The exact prime-by-prime product, by the ordinary
positive binary sieve \(R_J(N)\ll_J M_N\), gives
\[
       \sum_{\substack{x\in NJ\\(x,N)=1}}\Pi_F(x)\Pi_G(y)
             =F(0)G(0)R_J(N)+o(M_N).                            \tag{3}
\]
The boundedly many macroscopic primes dividing \(N\)
make a negligible difference.

For the remaining product expand \(A_F,A_G\) in the
integer CRT. In a term write \(n_1,n_2\) for the two
Möbius divisor variables, and \(k_1,k_2\) for the two
short prime-power marks when present. Use \(k_i=1\)
for an absent mark, with the corresponding free
\(\log(x/n_1)\) or \(\log(y/n_2)\) rather than \(\Lambda(1)\).
Exactly the two product divisors \(q_i=n_i k_i\)
divide the physical respective integers. On target
units they are coprime, since any common divisor
would divide \(N\). Thus both true \(q_i\) are also target
units and CRT has density
\((\varphi(N)/N)/(q_1q_2)\).
For this last factor open \((x,N)=1\) by the divisors
of \({\rm rad}(N)\); these are coprime to both products,
and each exact integer floor adds a \(\tau(N)\) loss.
The absolute number of \(q_1,q_2\) allocations is at most
\(N^{b_F+\lambda_F+b_G+\lambda_G+o(1)}\).
All actual coefficients and spatial variations have fixed
log or divisor costs, so the total floor is power-small
by the fixed strict inequalities. No condition of
coprimality between \(n_i\) and its own \(k_i\) is imposed.

## 2. Simultaneous short-\(\mu\) moments in the principal

We now work only inside the real CRT principal. At each
fixed real central \(x,y\), cut both \(n_1,n_2\) at
\(S=\exp((\log L)^4)\) **one at a time**. To cut \(n_1\),
fix \(k_1,k_2,n_2\), discard the incompatible cases
\((k_1,k_2)>1\) and any nonunit marks, and use the masked
tail of \(\mu(n_1)/n_1\) with actual mask \(N n_2 k_2\).
The mask is polynomial-sized. The profile and the
optional log factor in \(n_1\) are suitable for ordinary
partial summation, with bounded fixed log powers in
variation and supremum. The uniform masked zeta
harmonic tail at \(S\) is arbitrarily log-small, as
in the [original giant reduction, §1](../giant_prime_divisor_remainder/Proof.md)
or the bare \(1/n\) variant in
[the high-cut calibration, §1](Proof.md).
Other \(n,k\) harmonics taken absolutely cost only
fixed powers of \(L\); choose the tail accuracy after
these powers. Next cut \(n_2\) in the same manner,
now with \(n_1\le S\) and actual mask \(N n_1 k_1\).
This step retains the full signed divisor weights in
the principal and incurs \(O_A(NL^{-A})\).

Fix compatible \(k_1,k_2\) next. The two signed log
harmonics on the short box are the derivatives of
\[
 {\cal Z}(s,t)=
  \sum_{\substack{(n_1,Nk_2)=(n_2,Nk_1)=1\\(n_1,n_2)=1}}
              \frac{\mu(n_1)\mu(n_2)}{n_1^s n_2^t}
       =\zeta(s)^{-1}\zeta(t)^{-1}\mathcal E(s,t).                 \tag{4}
\]
Indeed, at a prime dividing neither target nor mark the
factor of \(\mathcal E\) is
\(1-p^{-s-t}/[(1-p^{-s})(1-p^{-t})]\).
At \(p\mid N\) it is
\((1-p^{-s})^{-1}(1-p^{-t})^{-1}\); at \(p\mid k_1\)
only the \(t\)-inverse is present, and at \(p\mid k_2\)
only the \(s\)-inverse. In particular a prime in a
mark is excluded only on the opposite \(n\)-side.
At \(\Re s=\Re t=1-1/(10\log L)\) the absolute two-variable
coefficient norm of \(\mathcal E\) is
\((\log L)^{O(1)}\) uniformly in all such marks.
The nonexceptional factors are absolutely summable;
for the factors at \(Nk_1k_2\), split at \(L^2\) as in
the same masked Mertens argument, using the \(O(L)\)
larger prime divisors and bounded \(p^{1/(10\log L)}\)
below that split. Derivatives through any fixed order
at \(s=t=1\) have \((\log L)^{O(1)}\) bounds by
the same absolute norm, with logarithmic factors
paid by decreasing the exponent reserve by a fixed
fraction.

For clarity, derivatives of (4) are genuine short-box
approximations. Convolve the coefficients of
\(\mathcal E\) with \(\mu(n_1)\mu(n_2)\) in its two
separate coordinates. If each convolving index is
at most \(\sqrt S\), complete each bare signed
\(\mu(n)\log^j n/n\) harmonic beyond its true length
\(S/d\ge\sqrt S\) by the ordinary Mertens tails,
uniform for every fixed \(j\); the factors \(\log d\)
cost only powers of \(\log S\). If either convolving
index exceeds \(\sqrt S\), the absolute norm at the
stated earlier abscissa gives arbitrary fixed
log saving; truncated inner absolute harmonics
are powers of \(\log S\), and completed inner
harmonics have bounded bare derivatives times
the stated powers of \(\log d\).
Thus at any fixed derivative order the actual
bilinear box differs by \(O_A(L^{-A})\) from the
corresponding signed derivative at \((1,1)\).
If either derivative order is zero this value
vanishes, from the two \(\zeta^{-1}\) zeros.
For first log-moment order in each variable the
two minus signs multiply and the value is
\(\mathcal E(1,1)\).

With the CRT unit density the local value for those
first moments is exactly
\[
             \frac{\varphi(N)}N\,\mathcal E(1,1)
                 =\mathfrak S(N)c(k_1k_2),\qquad
      c(k)=\prod_{p\mid k,\ p>2}\frac{p-1}{p-2}.                  \tag{5}
\]
At \(p\mid N\) the CRT factor removes one of the
two inverses; off \(N k_1 k_2\) the factor is
\(1-1/(p-1)^2\). At a prime in one mark the extra
ratio to this baseline is
\((1-1/p)^{-1}/(1-1/(p-1)^2)=(p-1)/(p-2)\).
The mark masks ensure these are odd primes.

Taylor expand each profile through degree three
at zero, only now on \(n_1,n_2\le S\).
Their physical spatial shifts \(\log(N/x)\),
\(\log(N/y)\) are bounded; the remainder per profile
is \(O((1+\log S)^4/L^4)\), which is \(o(1)\) after
even the other absolute short harmonic sums and
the two log/mark powers \(O(L^2)\).
All terms of derivative order zero in either variable
vanish up to arbitrary-log error as above. For an
unmarked leg its coefficient of the first \(\log n_i\)
is \(F'(0)-F(0)+O(1/L)\); higher coefficients are
\(O(L^{1-j})\) at order \(j\ge2\).
For a marked leg, before the multiplier
\(\Lambda(k_i)/k_i\), the coefficient is
\(-F'(0)/L+O(1/L^2)\), with higher ones \(O(L^{-j})\).
The same applies to \(G\). These follow directly
by multiplying the profile expansion by
\(\log(x/n_1)\) or the marked sign \(-1\),
and retain the bounded real spatial shifts at
the precision stated. Every term of order at least
two on one leg is \(o(M_N)\) after using the
polylogarithmic-in-\(\log L\) derivative bounds
of (4) and the two possible mark harmonics \(O(L)\).

Finally on compatible marks use (5).
For either leg,
\(\sum_{k\le U_F,(k,N)=1}\Lambda(k)c(k)/k
       =\lambda_F L+O(\log L)\):
the prime-power correction \(c(p)-1=O(1/p)\)
is absolutely summable after its harmonic factor,
and the missing target prime powers cost \(O(\log L)\).
If both legs have marks, omitting pairs of powers
of the same prime changes the resulting normalized
product by at most
\(O(L^{-2}\sum_p(\log p)^2/p^2)\).
Thus the effective first-log coefficient on the
\(F\)-leg is \((1-\lambda_F)F'(0)-F(0)=-a_F\),
and likewise \(-a_G\) on the other leg.
This proves the actual two-leg short-product identity
\[
             \sum_{\substack{x\in NJ\\(x,N)=1}}A_F(x)A_G(y)
                    =a_F a_G M_N+o(M_N).                        \tag{6}
\]
The only genuinely joint distribution used in (6)
is the compatible CRT principal and its exact
two-coordinate Möbius moments.

Expand \((A_F-\Pi_F)(A_G-\Pi_G)\), and insert
(2), (3), and (6), using the actual prime-power
exception bound from §1. The algebra is
\[
 a_Fa_G-a_FG(0)-F(0)a_G
    =-F(0)G(0)+(1-\lambda_F)(1-\lambda_G)F'(0)G'(0),
\]
which proves (1). In particular a positive comparison
using two exponential-shaped profiles must account
for the derivative product, rather than treating it
as free positive mass or omitting it. No such positive
comparison at the scale of the true binary term is
proved here.
