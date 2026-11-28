# Infinite log-concavity for all complete bipartite graphs \(K_{2,n}\)

Extend a finite sequence by zero, and write \((\mathcal L a)_i=a_i^2-a_{i-1}a_{i+1}\). The **absolute chromatic coefficients of \(K_{2,n}\), \(n\ge1\), are infinitely log-concave**. More precisely, after removing the zero constant coefficient, the first transform has \(n+1\) distinct negative roots as a polynomial. Thus the argument proves a real-rootedness assertion stronger than nonnegativity of every iterate.

This is a complete positive family for catalogue #076. [Amdeberhan and Moll, §6 and Conjecture 21](https://combinatorialpress.com/article/ojac/vol17/305.pdf) gave the complete bipartite chromatic formula and reported experiments in general, but the assertion for all graphs is false, as in the [repository's cycle classification](https://github.com/mxym/math/tree/main/notes/chromatic-infinite-logconcavity-counterexample). The [separate wheel result](FactorWheelInfiniteLogConcavity.md) perturbs a Jacobi polynomial in only three transformed coefficients. The perturbation below is supported throughout the sequence, and requires a comparison of the same Jacobi polynomial at two contracted arguments.

## 1. Normalization and exact transformed terms

Coloring the part of size two with the same or different colors gives
\[
P(q)=q(q-1)^n+q(q-1)(q-2)^n.
\]
The sign-adjusted polynomial is \(z[(z+1)(z+2)^n-(z+1)^n]\). Remove the factor \(z\), reverse the coefficient sequence, and rescale the variable by \(1/2\). These operations commute with \(\mathcal L\), with the variable factor squared after applying \(\mathcal L\). Thus it is enough to take \(N=n+1\) and
\[
A(z)=(1+z/2)(1+z)^{N-1}-(z/2)(1+z/2)^{N-1}
=\sum_{i=0}^N {N\choose i}\left(1-\frac{i}{2N}-\frac{i}{N2^i}\right)z^i .
\]
Its coefficients are positive for \(N\ge2\).

Let \(B(z)=\mathcal L((1+z)^N)\), so that
\[
B_i=\frac1{N+1}{N+1\choose i}{N+1\choose i+1},\qquad
B(z)=\frac{(1-z)^N}{N+1}P_N^{(1,1)}\!\left(\frac{1+z}{1-z}\right).
\]
The Jacobi identity follows from the classical binomial formula; it is also used in [Brändén, end of §3, p. 5](https://arxiv.org/pdf/0909.1927v3#page=5). For \(D=z\,d/dz\), put
\[
\begin{aligned}
L(i)&=1-\frac{i}{2N},\qquad \Delta(i)=\frac{i(N-i)}{N+1},\\
G(i)&=L(i)^2+\frac{\Delta(i)}{4N^2},\\
C(i)&=-2L(i)\frac{i}{N}
+\Delta(i)\left(\frac{L(i)i}{2N}-\frac{3}{2N}+\frac{5}{4N^2}\right),\\
Q(i)&=\frac{i^2+\Delta(i)}{N^2}.
\end{aligned}
\]
Then coefficient expansion, using
\({N\choose i-1}{N\choose i+1}/B_i=\Delta(i)\), gives
\[
 \mathcal L A=G(D)B(z)+C(D)B(z/2)+Q(D)B(z/4).                 \tag{1}
\]

At any \(z<0\), write \(z=-t^2\), \(u=t^2/(1+t^2)\), and \(Y=P_N^{(1,1)}(1-2u)\). With \(z\) replaced by \(s z\), use \(u_s=st^2/(1+st^2)\) and \(r_s=(1+st^2)^N/(N+1)\). For a given \(s\), suppress the subscript on \(u_s\) in the following differentiation rules and set \(v=u(1-u),\ V=DY\). The Jacobi differential equation gives
\[
D r_s=Nu r_s,\quad Du=v,\quad DY=V,\quad
DV=-(1-2u)V-N(N+3)vY.
\]
In particular, if \(D^j B(sz)=r_s(A_jY+B_jV)\), then
\[
 (A_0,B_0)=(1,0),\quad
 (A_{j+1},B_{j+1})
 =\big(Nu A_j+v A'_j-N(N+3)vB_j,\ 
         A_j+(Nu-1+2u)B_j+v B'_j\big),                       \tag{2}
\]
where primes mean \(u\)-derivatives. Applying (2) to (1), the two perturbation terms are \(r_s(A Y+B V)\) with \(s=1/2,1/4\), respectively, and
\[
\begin{array}{c|l|l}
 & A & B\\ \hline
C &\displaystyle \frac{u}{2}\{N(4u^3-10u^2+7u-1)+2u^3-5u^2+14u-13\}
 &\displaystyle\frac{N(8u^3-16u^2+7u)+4u^3-8u^2+26u-16}{4N}\\[1ex]
Q &u(2u-1)& 2u/N .
\end{array}                                                  \tag{3}
\]
At every interior extremum of the *unscaled* Jacobi polynomial, \(V=0\); there \(DB/B=Nu\) and \(D^2B/B=N^2u^2-N(N+2)u(1-u)\) by (2). Consequently
\[
     G(D)B(z)/B(z)=1-\frac54u+\frac12u^2.                    \tag{4}
\]
This multiplier is at least \(1/4\) everywhere and at least \(22/25\) for \(u\le1/10\).

## 2. Alternate signs at the Jacobi extrema for \(N\ge200\)

Write \(\theta=2\arctan t\), \(\theta_s=2\arctan(\sqrt{s}\,t)\) and \(\nu=N+3/2\). Define \(f(\theta)=(\sin\theta)^{3/2}P_N^{(1,1)}(\cos\theta)\). The Jacobi equation yields
\[
 f''+\left(\nu^2-\frac{3}{4\sin^2\theta}\right) f=0,\qquad
 F=f^2+\frac{(f')^2}{\nu^2},\qquad
 |(\log F)'|\le\frac{3}{4\nu\sin^2\theta}.
\]
For the inequality, differentiate \(F\), then apply \(2|ff'|\le\nu F\). The energy \(F\) is positive in the open interval, since zero initial value and derivative at one point would give the zero solution. At an unscaled Jacobi extremum \(f'/f=(3/2)\cot\theta\). Also,
\[
 V=DY=(\sin\theta_s)^{-3/2}\!
      \left(\sqrt{u_s(1-u_s)}\,f'(\theta_s)
                  -\frac34(1-2u_s)f(\theta_s)\right).
\]
Integrating the energy inequality from each argument to \(\pi/2\) and comparing to the unscaled extremal value gives
\[
\frac{|r_s(A Y+B V)|}{|B(z)|}
\le E_s\,s^{-3/4}
\left(\frac{1+st^2}{1+t^2}\right)^{N+3/2}
\Big(|A|+\big(\tfrac34+\nu\sqrt{u_s(1-u_s)}\big)|B|\Big),     \tag{5}
\]
where \(A,B\) on the right are the scalar entries of (3) and
\[
E_s=\exp\!\left(\frac{3}{8\nu}(|\cot\theta|+|\cot\theta_s|)\right)
       \sqrt{1+\left(\frac{3\cot\theta}{2\nu}\right)^2}.
\]
The power \(N+3/2\) accounts for \(r_s/r_1\) and the ratio of the sine prefactors.

**Coverage of all interior extrema.** Put \(c=19/10\). Every such extremum has \(c/N\le t\le N/c\). For this, the derivative in \(x=\cos\theta\) is proportional to \(P_{N-1}^{(2,2)}(x)\). On multiplying this polynomial evaluated at \(\cos\theta\) by \(\sin^{5/2}\theta\) we get a function \(h\) satisfying \(h''+(\nu^2-15/(4\sin^2\theta))h=0\), positive and increasing near \(0\). On \(0<\theta\le a=c/\nu\) the coefficient of \(h\) is nonpositive, since \(c^2<15/4\). Thus \(h\) stays positive, is convex there, and \(h'(a)/h(a)\ge1/a\). The solution of the constant-coefficient equation \(g''+\nu^2g=0\) with the same data at \(a\) remains positive up to at least \(a+(\pi/2+\arctan(1/c))/\nu\). Variation of constants gives
\[
 h(\theta)-g(\theta)=\int_a^\theta
          \frac{\sin(\nu(\theta-y))}{\nu}\frac{15}{4\sin^2 y}\,h(y)\,dy .
\]
Up to a hypothetical first zero before \(g\)'s first zero the integrand is nonnegative, since the latter is less than \(a+\pi/\nu\). This excludes such a zero. Since \(N\ge200\),
\[
\nu\,2\arctan(c/N)\le 2c\,\frac{403}{400}
    < c+\frac32+\frac1c-\frac1{3c^3}
    < c+\frac\pi2+\arctan(1/c).
\]
This proves the left bound; Jacobi parity gives the reflected bound.

**Bounds in (5).** Throughout this band,
\[
|\cot\theta|\le N/(2c),\quad |\cot\theta_s|\le N/(2c\sqrt{s}),
\quad E_{1/2}(1/2)^{-3/4}<7/3,\quad E_{1/4}(1/4)^{-3/4}<9/2.
\]
For example, use \(\nu\ge N\), \(\sqrt2<10/7\), \(2^{3/4}<17/10\), and \(\sqrt{1+(3/(4c))^2}<269/250\); the two exponential arguments are bounded by \(6/25\) and \(3/10\). With \(x=Nu\), the power in (5) is at most \(e^{-(1-s)x}\).

For (3), valid on \(0\le u_s\le1\) are
\[
 |A_C|\le (N/2+13/2)u_s,\quad
 |B_C|\le 7u_s/4+4/N,\quad
 |A_Q|\le u_s,\quad |B_Q|\le2u_s/N.
\]
Indeed \(4u_s^3-10u_s^2+7u_s-1\), written with \(y=1-u_s\), is \(y+2y^2-4y^3\), with absolute value at most 1 (split at \(y=1/2\)); the remaining scalar polynomials are bounded using monotonicity or \(8u_s^2-16u_s+7\in[-1,7]\). If \(u_s\le1/19\), the two terms of \(B_C\) have opposite signs, so the sharper bound is \(\max(7u_s/4,4/N)\).

* If \(u\le1/10\), then \(u_{1/2}\le(10/19)u\) and \(\sqrt{u_{1/2}}\le23/100\). Using \(7u_{1/2}/4\) for the \(B_C\) bound in (5), its final factor is at most \((19/20)N u_{1/2}\le x/2\). Thus the \(C\)-term ratio is at most \(7/(3e)<43/50\). Using \(4/N\) instead, the final factor is at most \((2/7)x+3/200+(21/100)\sqrt{x}\). Since \(\max x e^{-x/2}=2/e<37/50\) and \(\max \sqrt{x}e^{-x/2}=e^{-1/2}<61/100\), this again bounds the ratio by \(43/50\). For the \(Q\) term, \(u_{1/4}\le(10/37)u\) and \(\sqrt{u_{1/4}}\le1/6\); its final factor is at most \((27/20)u_{1/4}\). With \(\max x e^{-3x/4}=4/(3e)<1/2\), the \(Q\) ratio is less than \(1/200\). The sum is less than \(22/25\).
* If \(u\ge1/10\), then \(x\ge20\). The global bounds from (3), \(\sqrt{u_s(1-u_s)}\le1/2\) and \(u_s\le u\), bound the final factor in (5) by \((3/2)x+21/10\) for \(C\) and by 3 for \(Q\). Both upper bounds including the exponent decrease for \(x\ge20\), with sum at most \((7/3)(321/10)e^{-10}+(27/2)e^{-15}<1/4\).

In each case (4) is strictly larger than the relative perturbation bound. Hence \(\mathcal L A\), normalized by \((1-z)^N\), has the signs of \(P_N^{(1,1)}\) at all interior extrema. At \(u=0,1\), its signs are \(+\) and \((-1)^N\): the constant and leading coefficients are positive squares. The \(N-1\) interior extrema and the two endpoints supply \(N+1\) alternating signs, by the usual Jacobi zero and derivative interlacing. The continuous normalized polynomial in \(u\) has a zero between every successive pair. This gives \(N\) distinct negative zeros of \(\mathcal L A\) in \(z\), exhausting its degree.

## 3. Exact small cases and iteration

For \(2\le N\le199\), the [standalone Python verifier](verify_factor_k2n_infinite_logconcavity.py) supplies \(N+1\) rational sign points on the closed \(u\)-interval. It uses approximate zeros of the derivative Jacobi polynomial only to propose candidate points; all inequalities are checked on exact integers after homogenization, and the five cases \(2\le N\le6\) use fixed rational points. The checker also checks the rational bounds in §2 by rational arithmetic and upper and lower Taylor bounds for the exponential constants. No numerical root is assumed correct or used as evidence. Run with ordinary Python, not optimized mode:

```sh
python3 verify_factor_k2n_infinite_logconcavity.py
```

Finally apply [Brändén's preservation theorem](https://arxiv.org/abs/0909.1927) to the nonnegative first transform, which has only real negative roots before reintroducing the initial zero. All later transforms have nonnegative coefficients. This proof makes no claim for \(K_{m,n}\) with \(m\ge3\).
