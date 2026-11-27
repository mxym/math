# Infinite log-concavity for the chromatic coefficients of every wheel

For a coefficient sequence \(a=(a_0,\ldots,a_n)\), extend by zero and set
\[
      (\mathcal La)_j=a_j^2-a_{j-1}a_{j+1}.
\]
The sequence is infinitely log-concave if every iterate has nonnegative coefficients.

**Theorem.** If \(W=K_1\vee C_n\) is a wheel with \(n\ge3\) rim vertices, the absolute chromatic coefficient sequence of \(W\) is infinitely log-concave. In fact its first \(\mathcal L\)-iterate has only real nonpositive zeros as a polynomial. After removing its initial zero, those zeros are simple and negative.

More generally, for each \(n\ge3\) and every real \(0\le\varepsilon\le 2^{1-n}\), the first iterate of
\[
                     A(z)=(1+z)^n-\varepsilon(1+z)             \tag{1}
\]
has \(n\) distinct negative zeros. The same is true with the bound on \(\varepsilon\) replaced by the quantitative criterion in Section 2. An extension to cones over unicyclic graphs is given in Section 4. This is not a general positivity theorem for chromatic polynomials: the [cycle classification](https://github.com/mxym/math/tree/main/notes/chromatic-infinite-logconcavity-counterexample) already gives the opposite behavior for all cycles with at least 12 vertices.

## 1. Wheel normalization and the Jacobi baseline

For a graph with \(v\) vertices, write \(Q(z)=(-1)^v\chi(-z)\) for its sign-adjusted chromatic polynomial. Its coefficients are the absolute chromatic coefficients. Choosing the hub color first gives
\[
          Q_W(z)=z\big((z+2)^n-(z+2)\big).
\]
Multiplication by \(z\) just shifts the zero-extended transform. Also, if the coefficients are multiplied by \(C r^j\), with \(C,r>0\), then the transformed entries are multiplied by \(C^2r^{2j}\). Hence the reduced wheel is (1) with \(\varepsilon=2^{1-n}\), up to a positive scale of the variable and of the polynomial. Conversely more generally this treats \((z+c)^n-(z+c)\) for every real \(c\ge2\).

Put
\[
    B_n(z)=\sum_{j=0}^{n}\frac{1}{n+1}
                  {n+1\choose j}{n+1\choose j+1}z^j .
\]
The identity \(\mathcal L((1+z)^n)=B_n(z)\) follows coefficient by coefficient from the binomial product. Here and below \(\mathcal L\) applied to a polynomial means the operator on its coefficients. The substitution
\[
       x=\frac{1+z}{1-z}, \qquad
       (n+1)(1-z)^{-n} B_n(z)=P_n^{(1,1)}(x)                 \tag{2}
\]
follows from the explicit Jacobi polynomial formula and also appears in [Brändén, Example 4.3](https://arxiv.org/pdf/0909.1927). The map takes the negative real axis to \((-1,1)\). The key step is to control how far \(\mathcal L(A)\) is from the Jacobi baseline at its \(n+1\) alternating sign points, uniformly in \(n\), rather than to assume the original nonreal chromatic roots are harmless.

Let \(y=P_n^{(1,1)}\), \(\lambda=n(n+3)\). Its differential equation is \((1-x^2)y''-4xy'+\lambda y=0\). The function
\[
                 F(x)=y(x)^2+(1-x^2)y'(x)^2/\lambda
\]
has derivative \(6x\,y'(x)^2/\lambda\), so \(F\) has a minimum at 0. At each Jacobi extremum in \((-1,1)\) and at the two endpoints, \(|y|\ge\sqrt{F(0)}\). These \(n+1\) points have alternating signs because the \(n\) Jacobi zeros are simple in \((-1,1)\) and the interior derivative zeros separate them.

The usual central Legendre value \(P_{2r}(0)=(-1)^r{2r\choose r}/4^r\) and \(y=2P_{n+1}'/(n+2)\) give
\[
 \sqrt{F(0)}=
 \begin{cases}
 \displaystyle\frac{2(n+1)}{n+2}\frac{\binom{n}{n/2}}{2^n},
       & n\ \text{even},\\[6pt]
 \displaystyle\frac{2(n+1)}{\sqrt{n(n+3)}}\frac{\binom{n+1}{(n+1)/2}}{2^{n+1}},
       & n\ \text{odd}.
 \end{cases}                                                \tag{3}
\]
For the second line use the Legendre differential equation to compute \(P_{n+1}''(0)\). The central binomial coefficient is at least the average binomial coefficient of its row, so the displayed quantity is at least \(1/(n+2)\) in either parity. The Jacobi and Legendre identities used here are recorded in [DLMF §§18.5, 18.8–9](https://dlmf.nist.gov/18.8).

## 2. Uniform wheel perturbation bound

Only the first three transformed coefficients of (1) differ from those of \(B_n\); exact subtraction gives
\[
  \mathcal L(A)-B_n
   =\varepsilon\left[-2+\left({n\choose2}-2n\right)z+
                                  {n\choose3}z^2\right]
                       +\varepsilon^2(1+z).                 \tag{4}
\]
Let \(u=(1-x)/2=-z/(1-z)\in[0,1]\), so \((1-z)^{-n}=(1-u)^n\). When multiplied by \((1-z)^{-n}\), the terms of order \(\varepsilon\) in (4) are a linear combination of \({n\choose j}u^j(1-u)^{n-j}\), \(j=0,1,2\). The coefficients in this combination have magnitudes \(2,\ |n-5|/2,\ (n-2)/3\), respectively. The binomial weights are nonnegative and sum to at most 1 over these indices. The \(\varepsilon^2\) term is bounded by \(\varepsilon^2\), since \((1-2u)(1-u)^{n-1}\) has absolute value at most 1. Thus the change to the right side of (2), on the entire closed interval, is bounded by
\[
       (n+1)\varepsilon(M_n+\varepsilon),\qquad
       M_n=\max(2,|n-5|/2,(n-2)/3).                          \tag{5}
\]
Whenever (5) is strictly smaller than (3), the alternating signs survive, so the transformed polynomial has one zero between every pair of consecutive sign points. These give \(n\) distinct negative zeros of \(\mathcal L(A)\).

For \(n=6,\ldots,10\) and \(\varepsilon=2^{1-n}\), strict comparison follows by squaring and substituting the exact expressions (3) and (5); the verifier performs these five rational checks. For \(n\ge11\) use \(M_n+\varepsilon\le n/2\). The sufficient inequality \(n(n+1)(n+2)<2^n\) holds at \(n=11\) and persists because the ratio of left side to right side decreases, by a factor \((n+3)/(2n)\) on incrementing \(n\). The bound is monotone in nonnegative \(\varepsilon\), so all \(0\le\varepsilon\le2^{1-n}\) are covered.

The criterion (3)–(5) also applies if \(c\) is any real constant strictly greater than 1 and \(n\) is sufficiently large: for \((z+c)^n-(z+c)\) use \(\varepsilon=c^{1-n}\), whose exponential decay dominates the polynomial factors.

## 3. Small rims and infinite iteration

For \(3\le n\le5\), direct rational sign points for \(\mathcal L(A)\) complete the proof for the whole parameter interval. In the following table, the sign at \(-\infty\) is the opposite of the first displayed sign (the leading coefficient is 1).

| \(n\) | Sign points, left to right | Signs on \(0\le\varepsilon\le2^{1-n}\) |
|---|---|---|
| 3 | \(-3,-1/2,0\) | \(+,-,+\) |
| 4 | \(-7,-1,-1/2,0\) | \(-,+,-,+\) |
| 5 | \(-3,-2,-1/2,-1/3,0\) | \(+,-,+,-,+\) |

Each sign is checked by the expression (4) plus the baseline. As a simple certificate, bound the linear term separately over \([0,2^{1-n}]\) and the quadratic term over \([0,2^{2-2n}]\). For example at \(n=4,z=-7\), \(B_4(z)=-118\) and the linear term is at most 26, while the quadratic term is nonpositive. The script checks all twelve interval comparisons. Thus there are again \(n\) distinct negative zeros.

All coefficients in (1) were already nonnegative. Since the first iterate has only negative zeros and positive leading coefficient, subsequent transforms retain real nonpositive zeros by [Brändén's real-root preservation theorem](https://arxiv.org/abs/0909.1927). Consequently they have nonnegative coefficients, which proves infinite log-concavity with the stated zero-extension convention.

## 4. An extension to other cones

Let \(G\) be any connected unicyclic graph with cycle length \(n\ge3\) and \(s\) vertices outside the cycle. Its cone \(K_1\vee G\) has reduced sign-adjusted chromatic polynomial
\[
                 (z+2)^{n+s}-(z+2)^{s+1}.
\]
Indeed each successive deleted leaf contributes one factor \(z+2\) after shifting the colors for the hub. Thus set \(N=n+s,\ S=s+1,\ \varepsilon=2^{1-n}\) and consider \((1+z)^N-\varepsilon(1+z)^S\).

We obtain infinite log-concavity, with the first iterate again real-rooted, under the explicit sufficient condition
\[
                      2^{\,n-s-2}>(N+1)(2N+3)(N+2).        \tag{6}
\]
To see this more generally, write \(a_j={N\choose j}\), \(c_j={S\choose j}\), with zero boundary values. The \(j\)-th coefficient change in the first iterate is
\[
 \varepsilon(-2a_jc_j+a_{j-1}c_{j+1}+a_{j+1}c_{j-1})
             +\varepsilon^2(c_j^2-c_{j-1}c_{j+1}).
\]
For \(0\le j\le N\), \(a_j\ge1,\ c_j\le a_j,\ c_j\le 2^S\), and \(a_{j\pm1}/a_j\le N\). The second bracket is nonnegative by binomial log-concavity, and at most \(c_j^2\le 2^S a_j\). After division by \(a_j\), the change has magnitude at most \(2^S[2(N+1)\varepsilon+\varepsilon^2]\). Under (2) at degree \(N\), the binomial weights over all \(j\) sum to 1, so the transformed error is at most \((N+1)2^S\varepsilon(2N+3)\) for \(\varepsilon\le1\). Inequality (6) puts this below \(1/(N+2)\), the same guaranteed Jacobi sign margin. This proves the extension, without asserting anything when (6) fails.

## Related work and checks

[Amdeberhan–Moll](https://combinatorialpress.com/article/ojac/vol17/305.pdf), Conjecture 21, asked for chromatic infinite log-concavity in general. The existing repository result disproves that conjecture by cycles; the note here proves a complete positive family of cones over cycles despite the original wheel chromatic roots generally not being all real. The role of Jacobi polynomials for the unperturbed binomial sequence is classical; the new step is the uniform perturbation estimate and its application to this graph family.

The companion [exact script](verify_factor_wheel_infinite_logconcavity.py) checks the coefficient identities, rational signs, and inequalities, and independently counts roots by signed rational Sturm remainders in 95 samples. This is not a Lean formalization.
