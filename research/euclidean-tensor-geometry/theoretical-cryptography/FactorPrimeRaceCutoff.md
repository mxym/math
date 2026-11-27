# The modulo-4 semiprime bias after a polynomial lower factor cutoff

Let $0<\alpha<1/2$. For $x>2$ let $\mathcal P_\alpha(x)$ be the set of products $pq\le x$ of odd primes with $x^\alpha<p<q$, and let $N_\alpha(x)=|\mathcal P_\alpha(x)|$. Let $N_{\alpha,--}(x)$ count those products with $p\equiv q\equiv3\bmod4$. Define
$$
 Z_\alpha(x)=\frac{4\alpha(1-\alpha)(\log x)^2}{x^{1-\alpha/2}}
                  \left(N_{\alpha,--}(x)-\frac14N_\alpha(x)\right).
 \tag{1}
$$

**Theorem.** Assume RH for $\zeta(s)$ and for $L(s,\chi_4)$. For every fixed $\alpha$, the variable $Z_\alpha(x)$ has, in logarithmic averaging $dx/x$, exactly the same limiting distribution as
$$
 \frac{\log x}{\sqrt x}\bigl(\pi(x;4,3)-\pi(x;4,1)\bigr).
 \tag{2}
$$
No linear-independence hypothesis is needed for this equality of limiting distributions. If the positive ordinates $\gamma$ of zeros of $L(s,\chi_4)$ are also linearly independent over $\mathbb Q$ as a multiset, the law in (1) is continuous; both signs of $Z_\alpha$ have positive logarithmic density. The positive density is the classical modulo-4 prime-race density, about $0.9959$ from Rubinstein–Sarnak. Thus removing the products with a factor below $x^\alpha$, for any fixed $\alpha>0$, changes the permanent positive sign into a race with genuine reversals under these hypotheses.

The joint laws distinguish polynomial cutoffs that have the same marginal law. Under the same linear-independence hypothesis, for $0<\alpha<1/4$ the pair $(Z_\alpha,Z_{2\alpha})$ has an uncorrelated but dependent limiting law $(X_1,X_2)$. It satisfies
$$
 \mathbb E[(X_1-1)^2(X_2-1)]
       =\sum_{\gamma>0}\frac1{(1/4+\gamma^2)^2}>0 .     \tag{3}
$$
More generally, if the cutoff exponents have the form $m_j\tau$ for positive integers $m_j$ and $m_j\tau<1/2$, their limiting law is
$$
 \left(1+2\Re\sum_{\gamma>0}
            \frac{U_\gamma^{m_j}}{\frac12-i\gamma}\right)_j
 \tag{4}
$$
with a single shared family of independent uniform circle variables $U_\gamma$. For Lebesgue-almost every finite tuple of cutoff exponents in $(0,1/2)$, the limiting coordinates instead are independent.

### Comparison

[Dummit–Granville–Kisilevsky](https://arxiv.org/abs/1411.4594) show that the fraction of **all** odd semiprimes whose two factors are $3\bmod4$ is eventually larger than $1/4$. [Gyulev–Marinov](https://arxiv.org/abs/2405.06139) proved positivity for their unrestricted family for every $x\ge9$. Those results are unconditional and are not contradicted by (1); the polynomial cutoff discards the small primes that supply the unrestricted reciprocal-prime bias. [Rubinstein–Sarnak, §2 and §4](https://www.math.uwaterloo.ca/~mrubinst/publications/Chebyshev.pdf) establishes the classical single-prime law and its sign density; the claim here is its transport to a polynomially truncated product family, including the coupled laws across cutoffs. This is a statement of analytic number theory under the displayed hypotheses and provides no individual factor recovery method.

## 1. Expanding the semiprime bias

Use $\chi=\chi_4$, $Y=\log x$, $y=\alpha Y$, $u_0=e^y$, $u_1=e^{Y/2}$, and
$S(u)=\sum_{p\le u}\chi(p)$ over rational primes. The identity
$$
    4\left(N_{\alpha,--}-\tfrac14N_\alpha\right)
        =-\sum\chi(p)-\sum\chi(q)+\sum\chi(p)\chi(q)     \tag{5}
$$
holds by expanding $(1-\chi(p))(1-\chi(q))$, with every sum over $u_0<p<q$, $pq\le x$. Under the two RH assumptions, the usual prime counting bounds are
$S(u)\ll \sqrt u\log(2u)$ and $\pi(u)-\operatorname{Li}(u)\ll\sqrt u\log(2u)$.

For each $p$, the signed inner $q$-sum is a difference of values of $S$. Thus the last two sums in (5) are $O(x^{3/4}\log x)$ in absolute value, using
$\sum_{m\le\sqrt x}(\sqrt{x/m}+\sqrt m)\ll x^{3/4}$.
For the first term in (5), the inner count is $\pi(x/p)-\pi(p)$. Replacing $\pi(x/p)$ by $\operatorname{Li}(x/p)$ costs $O(x^{3/4}\log x)$ by the same summation. The term $\sum_{u_0<p\le u_1}\chi(p)\pi(p)$ is $O(x^{3/4}\log x)$ by summation by parts: the maximum of $|S|$ on $[2,u_1]$ is $O(\sqrt{u_1}\log x)$, and the monotone weight $\pi(p)$ has total variation $O(u_1)$. Consequently
$$
     4\left(N_{\alpha,--}-\tfrac14N_\alpha\right)
       =-\sum_{u_0<p\le u_1}\chi(p)\operatorname{Li}(x/p)
                         +O(x^{3/4}\log x).            \tag{6}
$$
After the normalization of (1) the error tends to zero with a power of $x$, since $1-\alpha/2>3/4$. Fixing $\alpha=0$ or $\alpha=1/2$ is outside this argument.

## 2. The lower boundary is a one-sided exponential transform

Write
$$
 F(y)=-y e^{-y/2}S(e^y).
$$
For a function $f$ on $y\ge1$ write
$\|f\|_{B^2}^2=\limsup_{T\to\infty}T^{-1}\int_1^T|f(y)|^2dy$.
The approximation of Rubinstein–Sarnak, equation (2.5) and Lemma 2.2, identifies
$$
          F(y)=1+2\Re\sum_{\gamma>0}
                              \frac{e^{i\gamma y}}{\frac12+i\gamma}
                  \quad\text{in }B^2.                \tag{7}
$$
For the modulus $4$, their coordinate for the class $3$ differs from $F$ only by the prime $2$, contributing $O(y e^{-y/2})$. The real value $L(1/2,\chi_4)$ is positive, by the alternating series for the Dirichlet beta function, so there is no missing central zero. In particular $\int_1^T|F(y)|^2dy\ll T$. The pointwise GRH bound used above gives $F(y)\ll (1+y)^2$.

Divide the main sum in (6) by $x$ and work in the logarithmic variable $v=\log p$. The resulting weight is $g_Y(v)=e^{-Y}\operatorname{Li}(e^{Y-v})$. Its derivative is exactly $-e^{-v}/(Y-v)$. The lower endpoint is
$g_Y(y)=e^{-y}(Y-y)^{-1}(1+O(1/Y))$.
Summation by parts followed by the factor $y(Y-y)e^{y/2}$ gives
$$
 \begin{split}
 Z_\alpha(e^{y/\alpha})
   ={}&-F(y)(1+O_\alpha(1/y))\\
     &+\int_0^{Y/2-y}e^{-v/2}
           \frac{y}{y+v}\frac{Y-y}{Y-y-v}F(y+v)\,dv
       +O_\alpha\!\left(Y^{O(1)}e^{-(Y/2-y)/2}\right).
 \end{split}                                           \tag{8}
$$
Here the upper endpoint term is exponentially small by $F(Y/2)\ll Y^2$. The sign of the lower term comes from the strict inequality $p>u_0$.

The two fractions in the integral of (8) converge to $1$ uniformly for bounded $v$, and their product is bounded by a constant for all $0\le v\le Y/2-y$. The extra factor $O(1/y)F(y)$ is $B^2$-null: after discarding a fixed initial segment it has norm at most $O(1/y_0)$ times the norm of $F$. The integral in (8) differs in $B^2$ from $\int_0^\infty e^{-v/2}F(y+v)\,dv$ by zero. More precisely, at $v\le A$, discard a fixed initial segment of $y$ and use uniform convergence. At $v>A$, the normalized $L^2$ norm of $F(y+v)$ on $1\le y\le T$ is bounded by $O((1+v/T)^{1/2})$, since its integrated square up to $T+v$ is $O(T+v)$. Minkowski's inequality and exponential decay bound both tails uniformly by $O(e^{-A/3})$, and then $A\to\infty$.

Thus in $B^2$ the boundary statistic is
$$
 G(y)=-F(y)+\int_0^\infty e^{-v/2}F(y+v)\,dv.           \tag{9}
$$
This operator also takes a $B^2$ approximation of $F$ to a $B^2$ approximation of $G$. For a fixed finite trigonometric approximation the normalized integral of its squared difference from $F$ up to $T$ is bounded for all large $T$; Minkowski and the $v$-tail argument above justify passing to the limsup and then to better approximations. Equivalently, on bounded $v$ the $B^2$ norm of each translate equals the original norm, and the exponential tail can be removed before taking the approximation limit.

For the constant mode the multiplier in (9) is $-1+2=1$. For frequency $\gamma$ it is
$$
    -1+\frac1{1/2-i\gamma}
       =\frac{1/2+i\gamma}{1/2-i\gamma}.
$$
It therefore conjugates the coefficient $1/(1/2+i\gamma)$. This yields a finite-mode approximation to $G$ with exactly the coefficients of $F$ with $y$ replaced by $-y$.

## 3. Marginal and joint logarithmic laws

A finite vector of phases $e^{i\gamma y}$ is Haar equidistributed on the closure of its one-parameter orbit: averaging any torus character gives zero except for the characters annihilating the orbit. Inversion preserves Haar on that closure. Therefore a finite trigonometric approximation to $F(y)$ and its reflected version $F_T(-y)$ have the same limiting law even if the ordinates satisfy relations. Passing to the $B^2$ limits preserves weak limits: for bounded Lipschitz tests the error is controlled by the $B^2$ norm, and the uniformly bounded averaged second moments give tightness. The change $y=\alpha\log x$ preserves logarithmic averaging. This proves the equality claimed in (2).

Under linear independence the circle coordinates of the Haar measure are independent. Their square summable coefficients, by classical zero counting, give an $L^2$ convergent random series. The law is atomless since the first nonzero term is continuous and independent of the tail. Both signs have positive probability: $\sum_{\gamma>0}|1/(1/2-i\gamma)|=\infty$ by zero counting, so finitely many phases can force either sign by a large margin on an open set of positive probability. Independently the remaining tail has arbitrarily small variance, so it stays within that margin with positive probability. Equation (2) then transfers the sign density from the classical prime race.

For the joint claim, the approximations at positive scales $\alpha_j$ have the frequencies $\alpha_j\gamma$, and the $B^2$ approximation errors are unchanged by each positive rescaling. If $\alpha_j=m_j\tau$, the finite Haar phases $e^{i\tau\gamma\log x}$ are independent under LI and the $j$-th coordinate uses their $m_j$-th powers. Passage to the limit gives (4). If the finite tuple of $\alpha_j$'s is outside the countable union of hyperplanes
$$
       \sum_j \alpha_j\sum_\gamma k_{j,\gamma}\gamma=0
       \qquad(k_{j,\gamma}\in\mathbb Z\text{ finitely supported and not all zero}),
$$
all cross-scale frequencies are linearly independent. Under LI each such hyperplane is proper. The associated phases then are independent also across different $j$, proving the almost-every-tuple statement.

For $(m_1,m_2)=(1,2)$, distinct circle powers have zero covariance for each phase and the phases at distinct ordinates are independent. To compute the mixed moment in (3), set $b_\gamma=(1/2-i\gamma)^{-1}$. The only constant terms in the circle integrals arise by taking two first powers and one conjugate second power, or their conjugates, at the same ordinate. They contribute
$2\Re(b_\gamma^2\overline b_\gamma)=2|b_\gamma|^2\Re b_\gamma=(1/4+\gamma^2)^{-2}$.
The finite calculations pass to the limit in $L^3$, since the centered independent bounded summands with square-summable amplitudes give sub-Gaussian moment bounds for their tails. This is a mixed moment of the limiting law, not a claim about convergence of empirical third moments. It is positive, excluding independence despite zero covariance.

The companion verifier checks the finite characteristic-function expansion by signs, the signed endpoint in partial summation, the exact complex multiplier, and the mixed circle moments using rational arithmetic. It does not test RH, LI, or the limiting error.
