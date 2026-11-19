# The eventual optimal Bernoulli sign count at rational bias with even denominator

Yongxian Zhang

In [Mihir Singhal, *Erdős–Littlewood–Offord problem with arbitrary probabilities*](https://arxiv.org/pdf/1912.02886), Theorem 1.2 reduces maximization of the largest atom of a weighted sum of $n$ iid Bernoulli($p$) variables over nonzero real coefficients to the choice of signs. If $\ell$ signs are positive and $n-\ell$ negative, write $t=2\ell-n$ and by global reversal take $t\ge0$. For fixed rational bias of even denominator and large odd $n$, Proposition 3.4 finds the asymptotic linear slope of $t$. Conjecture 4.1 asks whether the remainder is eventually periodic. We give its exact rounding rule.

**Theorem.** Reflecting $p$ to $1-p$ only translates and reflects the signed sums, so take $p=r/s<1/2$ in lowest terms, $0<r$, $s$ even. Write $d=s-2r>0$, $a=6/(5d)$, and
$$
 z_0=\frac{2(120d^2+95s^2-296)}{125d(d^2-s^2)} .
$$
For all sufficiently large odd $n$ (depending on $p$), the maximizing $t\ge0$ is **unique**. It is the element of the progression $rt\equiv1\pmod{s}$ nearest to $an+z_0$. The mode of this positively oriented sum is then $x=(rt-1)/s$. In particular the sign count $\ell^*=(n+t)/2$ minus $(1/2+3/(5d))n$ is eventually periodic on odd $n$. In units of $n$, its least positive even eventual period is
$$
 P=\frac{5ds}{\gcd(5ds,6)} .
$$
The theorem concerns fixed $p\in(0,1)\setminus\{1/2\}$ with even reduced denominator. At $p=1/2$ all sign patterns have the same peak, as Singhal already notes. We do not assert an effective starting $n$, a formula for every finite $n$, or a periodic law for irrational biases.

## 1. The previously located residue of the mode

Put $h=1-2p>0$, $v=p(1-p)$ and $\xi=x-tp$. Define $R(\theta)=|1-p+pe^{-i\theta}|$, and
$$
 g(\theta)=p\theta+\arg(1-p+pe^{-i\theta}).
$$
The argument is the continuous branch zero at zero; the real part of its argument's input is positive for our $p$. By Fourier extraction of the signed Bernoulli mass, maximizing it over $(t,x)$ is equivalent to minimizing
$$
 D_n(t,\xi)=\int_{-\pi}^{\pi} R(\theta)^n[1-\cos(\xi\theta+t g(\theta))]\,d\theta.
$$
This is Singhal's representation (7)–(8) up to fixed normalization. The proof of his Proposition 3.4 already identifies $\xi=-1/s$ for all sufficiently large odd $n$. We recall a derivation to specify the normalization and the positive orientation. A signed sum, upon adding $n-\ell$, is a sum of independent Bernoulli variables with parameters $p$ or $1-p$. By [Darroch's mode theorem](https://doi.org/10.1214/aoms/1177703287) every maximizing $x$ satisfies $|\xi|<1$. For admissible odd $t$, $\xi$ is a nonzero multiple of $1/s$ since $r$ is odd and $s$ even.

Let $U$ be a centered normal variable of variance $1/v$ and $G(u)=vh u^3/6$. For $|\xi|\le1$ and $0\le t\le n$, uniformly, with $\tau=t/n$,
$$
 D_n(t,\xi)=\frac{\sqrt{2\pi/v}}{2 n^{3/2}}
 \left(\mathbb E[(\xi U+\tau G(U))^2]+o(1)\right).
$$
Indeed near zero $\log R(\theta)=-v\theta^2/2+O(\theta^4)$ and $g(\theta)=vh\theta^3/6+O(\theta^5)$, while $R<1$ away from zero in $[-\pi,\pi]$. Put $\theta=u/\sqrt n$. On a fixed small neighborhood the Gaussian domination $R^n\le e^{-c u^2}$ and $n(1-\cos(\xi\theta+t g(\theta)))\le C(|u|+|u|^3)^2$ make this limit uniform. The quadratic is
$$
 v^{-1}\!\left[\frac25\xi^2+\frac{5h^2}{12}
             \left(\tau+\frac{6\xi}{5h}\right)^2\right].
$$
For $\xi=-1/s$ its continuous minimum is $2/(5vs^2)$ at $\tau=a$, and there is an admissible $t=an+O(s)$ in the residue $rt\equiv1\pmod s$. Such $t$ are odd and inside $(0,n)$ since $d\ge2$. The corresponding integer target suffices as a competitor whether or not it is its law's mode. At $\xi=+1/s$, the minimum for $\tau\ge0$ is at least $1/(vs^2)$; at $|\xi|\ge2/s$ it is at least $8/(5vs^2)$. The strict uniform gap proves the stated restriction. This leading localization and slope are prior, not the new rounding result.

## 2. Comparing neighbors rather than rounding a continuous minimizer

Keep $\xi=-1/s$ fixed and regard $D_n(t,\xi)$ as a function of continuous $t$. Its second derivative, obtained under the bounded-domain integral, is
$$
 \int R^n g^2\cos(\xi\theta+t g)\,d\theta
 = n^{-7/2}\sqrt{2\pi/v}\,(\mathbb E[G(U)^2]+o(1))
$$
uniformly on $[0,n]$. After rescaling, the cosine tends uniformly to one on bounded $u$; locally $n^3g^2\le C u^6$, and the tails are controlled as above. Since $\mathbb E[G(U)^2]>0$, this function is strictly convex on the entire interval for all sufficiently large $n$.

For bounded $z$ let $t=an+z$ be a **midpoint** of a potential step of length $s$, not necessarily a candidate itself. The discrete increment equals
$$
 D_n(t+s/2,\xi)-D_n(t-s/2,\xi)=
       2\int R^n\sin(\xi\theta+t g)\sin(sg/2)\,d\theta .
$$
Write $\kappa_4=v(1-6v)$, $\kappa_5=vh(1-12v)$ and $J(u)=-\kappa_5u^5/120$.
The expansions, from $\log(1-p+pe^{-i\theta})$ at zero, are
$$
 \log R=-v\theta^2/2+\kappa_4\theta^4/24+O(\theta^6),\qquad
 g=vh\theta^3/6-\kappa_5\theta^5/120+O(\theta^7).
$$
Set $A(u)=\xi u+aG(u)$ and $C(u)=zG(u)+aJ(u)$. Dividing the increment by $s\sqrt{2\pi/v}\,n^{-5/2}$ gives
$$
 \mathbb E[AG]+\frac1n\,\mathbb E\!\left[AJ+
        (C-A^3/6)G+\kappa_4 U^4 AG/24\right]+O(n^{-2}),
 \tag{1}
$$
uniformly on each bounded interval of $z$. All polynomials inside expectations are evaluated at $U$. For the remainder, split at $|u|=n^{1/24}$. On the inner interval, after taking out the Gaussian, the amplitude is $1+\kappa_4u^4/(24n)+O(n^{-2}(1+|u|^{12}))$. The first sine is $n^{-1/2}A+n^{-3/2}(C-A^3/6)+O(n^{-5/2}P_1(|u|))$; the second, multiplied by $2/s$, is $n^{-3/2}G+n^{-5/2}J+O(n^{-7/2}P_2(|u|))$, for fixed polynomials $P_1,P_2$. These follow from Taylor's theorem and the two displayed expansions; the exponential correction and phase are uniformly bounded on this window. Integrating polynomial errors against the Gaussian is uniform; the outer interval contributes less than any inverse power after the same Gaussian/exponential split.

Using $\mathbb E[U^{2j}]=(2j-1)!!/v^j$ and $h=d/s$, the leading expectation is zero. The coefficient of $1/n$ is
$$
 \frac{5h^2}{12v} (z-z_0).
 \tag{2}
$$
For explicit algebra, put $k=vh/6$, $j=-\kappa_5/120$, $A=\xi u+ak u^3$ and $m_i=\mathbb E U^i$. Then the constant part independent of $z$ in that coefficient is
$$
 j(\xi m_6+2ak m_8)
 -\frac{k}{6}\big(\xi^3m_6+3\xi^2 ak m_8+
             3\xi a^2 k^2 m_{10}+a^3 k^3 m_{12}\big)
 +\frac{\kappa_4 k}{24}(\xi m_8+ak m_{10}).
$$
The multiplier of $z$ is $k^2m_6=5h^2/(12v)$. Substitution gives (2).

## 3. Why no midpoint tie can persist

The numerator of $z_0$ in the displayed formula is $-592$ modulo 5, hence nonzero modulo 5. In its reduced denominator the exponent of 5 is at least $3+v_5(d)$, where $v_5$ counts factors of 5. The reduced denominator of $an=6n/(5d)$ has exponent at most $1+v_5(d)$. Consequently $an+z_0$ is never an integer. All midpoints of neighboring admissible $t$ are integers, since their common step $s$ is even. The rational numbers $an+z_0$ have a fixed common denominator independent of $n$, so their distances from such midpoints are bounded away from zero.

Take the admissible $t_n$ nearest to $an+z_0$. Its left and right neighbor midpoints are $an+z$ with $z$ bounded, one uniformly below $z_0$ and the other uniformly above. By (1)–(2) the left discrete increment is strictly negative and the right one strictly positive. Strict convexity now yields the unique global minimizer on the progression inside $[0,n]$, and §1 excludes all other modal pairs. This proves the rounding formula.

An even shift $P$ with $aP\in s\mathbb Z$ translates the eventual rounded optimum by $aP$, giving a period of $t_n-an$ and of half of it, the centered sign count. Conversely any positive even period requires $t_{n+P}-t_n=aP$ and this difference belongs to $s\mathbb Z$. The least positive integer with the divisibility is $5ds/\gcd(5ds,6)$; it is even because $4\mid ds$ and $v_2(6)=1$. This proves minimality among shifts preserving the odd domain.
