# Genuine compensation for a near-root prime divisor and its tiny cores

Use the [all-completed shoulder](../completed_gap_two_true_sectors/Proof.md), with
\(N=2x\) even, \(L=\log x\), \(\ell=\log L\),
\(z=x^\chi\), \(\ell^{-2}\le\chi\le\ell^{-1}\),
\(J=xJ_0\subset[x,1.5x]\), and genuine \(P=N-y\) prime.
Keep the actual squarefree \(z\)-rough partners \(y\).
The small factors for the all-completed score are the genuine
primes \(<C_y=y/x^{1-\epsilon}\) for fixed \(0<\epsilon<.005\).
Put \(T_y=\log y/(2L)\).

For parameters \(K\ge1\) and \(M\chi<U\), consider actual short
divisors \(d=pA\) with \(p\) genuine prime, \(1\le A\le z^K\),
and
\[
                      T_y-U<\log d/L<T_y-M\chi .                  \tag{1}
\]
We use these parameters for \(K\le 2\log\ell\), \(M\ge9\),
and \(U\le100\chi\log\ell\). In particular \(p\ge x^{.49}\)
eventually, \(A<C_y\), and the giant p is unique in d.
Different d on the same y are still different divisor orientations.
In this family the exact contribution in the completed shoulder
is
\[
 \mu(d)\log(y/d)-\mu(A)(\log d-2\log A)
                          =-\mu(A)(\log y-2\log A).               \tag{2}
\]
This uses all subsets of the tiny actual core A in the second
term, including the empty subset. A prime d (the case \(A=1\))
therefore gives precisely \(-\log y\), not a main-term sign
inferred from an artificial model.

Let \(B_K(M,U)\) be the true sum of (2) on these actual d,
weighted by \(\log P\) on the genuine opposite prime. Include
the factors \(R_z(y)\) and \(1_{\mu^2(y)=1}\) as above.
The complement prime count is never replaced by a conjectural
prime-pair density. Write \(\rho\) for the Dickman function
and \(c_0=e^{-\gamma}\).

**Fixed microscopic shell.** Fix \(K\ge1\), \(w>0\), \(M\ge9\),
put \(U=(M+w)\chi\) and \(s=M-1\), then let \(x\to\infty\).
Uniformly in the actual even target,
\[
\begin{split}
 B_K(M,U)
   &=-2c_0 w\,\rho(K)|J|\mathfrak S(N)
      + O_{J_0}\bigl(wK s^{-s/2}x\mathfrak S(N)\bigr)
      +o_{K,M,w,\epsilon,J_0}(x\mathfrak S(N)),\\
 B_1(M,U)
   &=-2c_0 w|J|\mathfrak S(N)
      + O_{J_0}\bigl(w s^{-s/2}x\mathfrak S(N)\bigr)
      +o_{M,w,\epsilon,J_0}(x\mathfrak S(N)).                      \tag{3}
\end{split}
\]
In particular the **genuine composite-d net** \(B_K-B_1\)
is positive for fixed \(K>1\) and sufficiently large fixed M.
By taking K large first and then M, it compensates an arbitrarily
large prescribed fraction of the prime-d debit, on this same
microscopic shell and in the same score. This is not a statement
about a binary prime-pair positive contribution.

**Growing union.** Uniformly in the ranges stated above, with
integer \(M\) and \(U>M\chi\), write
\[
 E_M=\sum_{j\ge M}(j-1)^{-(j-1)/2}.
\]
Then
\[
 B_K(M,U)-\rho(K)B_1(M,U)
   \ll_{\epsilon,J_0} x\mathfrak S(N)\bigl(K E_M+ K^2 U^2\bigr)
                    +O_{A,\epsilon,J_0}(xL^{-A}).                \tag{4}
\]
Both sides of (4) are actual prime-weighted signed counts;
the subtraction uses the actual \(B_1\), not a fitted model.
For example take
\[
 K=\log\ell,\qquad
 M=\left\lceil100\,\frac{\log\log\ell}{\log\log\log\ell}\right\rceil,
 \qquad U=100\chi\log\ell .
\]
For sufficiently large x these are admissible and
\(B_K(M,U)=o(x\mathfrak S(N))\), even though
\(-B_1(M,U)\asymp (U/\chi-M)x\mathfrak S(N)\).
The last, truly terminal interval of depths \(<M\chi\)
and the bigger attached cores \(A>z^K\) are not priced here.

## 1. True joint prime and rough count at the short modulus

For any fixed d in this selection the restriction (1) is a
single interval in physical y, intersected with J. Its weight
\(\log y-2\log A\) is nonnegative, with \(O(L)\) size and
variation, and \(\mu(A)\) has a fixed sign. Treat this restriction
by actual maximal prefixes. Drop the \(O(1)\) opposite primes
dividing N; the total cost is \(x^{o(1)}\).
Otherwise both d and \(y/d\) are units modulo N.
For squarefree d, we temporarily sum over all rough y; the
squareful \(y\)'s are \(O(x/z)\) by the floor sum over \(p^2\mid y\),
\(p>z\). Cauchy with fixed divisor moments applied to the
\(O(L\tau(y))\) score bound and the other log weight costs
\(O_A(xL^{-A})\). The squarefree d condition remains exact.

For the fixed shell, use dimension-one upper and lower fundamental
lemma with level \(D=z^{M-1}\) on the **free** \(y/d\);
see the primary sieve input in the [thin-gap proof](../thin_true_giant_gap/Proof.md).
Keep \(d\) rough. Its prime support is disjoint from the
squarefree sieve labels \(h\le D\), all supported at primes
\(\le z\) not dividing N. The genuine prime progression is
\(P\equiv N\bmod dh\), with \(dh\le\sqrt{1.5x}/z\).
The local density at each admissible prime is \(1/(p-1)\);
its dimension constant is absolute, since 2 divides N and
the ordinary Mertens bound applies at all remaining primes.
The bounded sieve coefficients and \(\log P\) are covered
by ordinary arbitrary-log maximal BV; \(z\) vastly exceeds
any fixed power of L. The modulus \(dh\) determines \(d,h\)
by splitting at z, and the d then determines \(p,A\).
Thus the actual weight in every modulus is at most a fixed
log power, with no multiplicity of free prime labels.
For every branch use both upper and lower inequalities
against positive weights before inserting the sign of \(\mu(A)\).

For the growing union, divide the depths
\((T_y-\log d/L)/\chi\) into disjoint intervals \([j,j+1)\);
the first or last interval can be trimmed at the chosen cuts.
For the j-th interval use \(D_j=z^{j-1}\).
Even with varying y, the exact inequality giving depth
\(\ge j\chi\) ensures \(dh\le\sqrt{1.5x}/z\).
For fixed d each such interval is again just a y-prefix
intersection, and using a different level in each of at most
\(O(\log\ell)\) intervals costs only a log factor in the
global BV error. Boundary conventions at each exact split
are made disjoint; endpoint atoms are handled by the same
maximal prefixes (equivalently the equality divisors
contribute only \(O(x^{1/2+o(1)})\) per split).
The relative fundamental-lemma error for the j-th model
is \(O((j-1)^{-(j-1)/2})\). This is not charged to every
interval at the original M cost.

In both uses the individually sifted leading term, inside
the y-integral, is \(V_N(z)/\varphi(d)\), with
\[
 V_N(z)=\prod_{p\le z,p\nmid N}(1-1/(p-1))
       =\mathfrak S(N)V_z(1+O(L/z)),\qquad
 V_z\sim c_0/(\chi L).
\]
Replacing \(\varphi(d)^{-1}\) by \(1/d\) costs a relative
\(O(L/z)\) pointwise. Removing any remaining excluded
\(p\mid N,\ p>z\) in the harmonic model costs an arbitrary
log error by opening one such prime and a divisor harmonic
bound. More explicitly, if an excluded giant p occurs it
contributes at most \(O(L x^{-.49})\) to the giant reciprocal
sum per A; if a core factor divides N, use
\(\sum_{r\mid N,r>z}1/r\ll L/z\) and the rough integer
harmonic bound after removing r. The absolute harmonic
bound for every core range here is
\[
 \sum_{\substack{A\le z^K\\P^-(A)>z}}\frac{\mu^2(A)}A
   \le\prod_{z<r\le z^K}(1+1/r)\ll K                            \tag{5}
\]
with absolute constant, including \(A=1\). Fix A and y.
For a depth interval of length \(u\chi\) with \(u=w\) in
the fixed case and \(u\le1\) in each variable interval,
the reciprocal prime p interval costs \(O(u\chi)+O_A(L^{-A})\):
\(p\ge x^{.49}\), and it has precisely this exponent width,
up to endpoints. Ordinary quantitative prime Mertens gives
this even uniformly in A and y. Thus, with \(\log y-2\log A\)
and \(V_N(z)\), the absolute model on such an interval
costs \(O(u K x\mathfrak S(N))\). This pays the error in (3)
and the total \(O(K E_M x\mathfrak S(N))\) in (4).
There is no small relative error asserted for each very
short **physical** arithmetic progression separately.

## 2. Exact giant prime harmonic and collective remainder

For fixed y and actual A, put \(a=\log A/L\). Partial summation
of the genuine giant prime harmonic, uniformly on the ranges
above, gives the following conditional main for (2):
\[
 -L\frac{\mu(A)}A\int_{T_y-U}^{T_y-M\chi}
                     \frac{2T_y-2a}{t-a}\,dt+O_A(L^{-A})
\]
before multiplying by \(V_N(z)\), with the error also allowed
after summing their absolute harmonic as in (5).
Only the \(1/p\) harmonic of the actual giant prime is being
evaluated here: the previous section evaluates the independent
**AP error for each actual fixed d** before this calculation.

The exact kernel admits the identity
\[
 \frac{2T_y-2a}{t-a}
       =2+\frac{2(T_y-t)}{t-a},\qquad
 \frac{2T_y-2a}{t-a}-\frac{2T_y}{t}
       =\frac{2(T_y-t)a}{t(t-a)}.                              \tag{6}
\]
All denominators are bounded away from zero in the stated range.
The second difference, integrated over the full interval,
is \(O(a U^2)\), not merely \(O(a U)\).
From (5) and \(a\le K\chi\) this costs \(O(K^2\chi U^2)\)
inside the harmonic divided by L. After \(L V_N(z)\)
and integration over J it is \(O(K^2 U^2 x\mathfrak S(N))\).

The remaining actual signed core harmonic is
\[
 \sum_{\substack{A\le z^K\\P^-(A)>z}}\frac{\mu(A)}A
                  =\rho(K)+O_B(L^{-B})                          \tag{7}
\]
for every fixed B in these uniform ranges. Apply the quantitative
prime-harmonic convolution comparison in §2 of the
[two signed sectors](../completed_gap_two_true_sectors/Proof.md):
the coefficient is \(-1\) at each genuine prime above z,
prime powers have zero coefficient, the density is \(dt/t\)
on \(t>\chi\), and the antiderivative is the Dickman function
scaled by \(\chi\). The endpoint \(K\chi\) is in \([0,2]\);
the argument there uses exponentially small Mertens errors
and locally bounded harmonic variation, so no fixed-rank or
fixed-K hypothesis is used in (7). Inclusion of a single
edge atom costs at most \(1/z\).
Combining (6), (7), and the actually evaluated model for
\(B_1\) proves (4). The same argument in a fixed microscopic
shell gives (3), since its interval width is \(w\chi\) and
\((2T_y-2a)/(t-a)=2+o_{K,M,w}(1)\).

For the growing example, \(K^2U^2\ll(\log\ell)^4/\ell^2=o(1)\).
The elementary factorial bound \(\rho(K)\le1/\lfloor K\rfloor!\)
then pays the factor \(U/\chi=O(\log\ell)\).
Also \(K E_M=o(1)\), since the leading decay of \(E_M\)
is \(\exp(-(\tfrac12+o(1))M\log M)\) and \(K=\log\ell\).
The A=1 main itself has size \((U/\chi-M)x\mathfrak S(N)\)
up to bounded positive constants, and its error by §1 is \(O(E_M x\mathfrak S(N))\).
This proves the asserted real cancellation on the varying union.
It does not justify moving the last cut to the actual square
root, where this proof has no spare modulus for sieving the
free cofactor.

A [literal terminal packet](../terminal_tiny_core_toggle/Proof.md) pays the actual narrow tiny-core terminal raw debit with distinct positive raw-only receiver pairs. It uses different coordinates of the same score and is not an estimate for the entire gap-minus-own-root difference.
