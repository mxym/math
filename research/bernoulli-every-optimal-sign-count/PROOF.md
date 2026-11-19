# Every sign count is optimal for some non-fair Bernoulli bias at each odd sample size

Yongxian Zhang

Juškevičius and Kurauskas ask in [§5 of their paper](https://web.vu.lt/mif/v.kurauskas/files/2020/08/general_200704.pdf) how many positive signs can optimize the largest atom of a signed iid Bernoulli sum as its bias varies for a given sample size. The nontrivial question concerns odd sample sizes and non-fair biases: balancing is known for even sizes, and at the fair bias all choices tie. Their [full version, §4](https://arxiv.org/pdf/1912.08770v2) reports numerical observations through 31. We give explicit biases realizing all the sign counts, uniquely up to global reversal. This does not describe all optimality intervals in the bias or classify all extremizing nonunit coefficients. [Singhal, Theorem 1.2](https://arxiv.org/pdf/1912.02886v2), already shows that some sign choice attains the global optimum over nonzero real coefficients.

**Theorem.** Let $n$ be odd, and let $1\le T\le n$ be any odd integer. For iid $X_i\sim\mathrm{Ber}(p)$, orient signs by global reversal so that $u=\sum_i\epsilon_i\ge0$. There exists a rational $0<p<1/2$ for which $T$ is the unique maximizer of $\max_x\Pr(\sum_i\epsilon_iX_i=x)$ over the possible $u$. In fact use
$$
p=\begin{cases}1/(4n),&T=1,\\[2pt](1-(1-1/n)/T)/2,&3\le T\le n.\end{cases}
$$
At $u=T$ the unique modal value is $(T-1)/2$. Negating all signs realizes the opposite orientation. Thus for each fixed odd $n$, as $p$ varies, all counts $0,1,\ldots,n$ occur (paired by reversal). By finiteness and strictness each such witness persists in an open bias interval.

For $T=1$, the no-success event has probability at least $1-np=3/4$, so zero is the unique mode for every imbalance. With $l=(n+u)/2$ the mass there is a positive weighted sum of $\binom li\binom{n-l}i$, each maximized at maximal balance: its numerator factors into $(l-j)(n-l-j)$ for $0\le j<i$ whenever both binomials are positive. For $n>1$ the $i=1$ term gives strictness; $n=1$ is immediate. This is the small-bias mechanism of Singhal's Lemma 3.2.

## Fourier comparison for $n\ge150$ and $T\ge3$

Set $h=(1-1/n)/T$, $\lambda=1-h^2\ge8/9$ and $B=uh$ (so $0<B\le n/3$). The signed sum of $1-2X_i$ is $u-2\sum_i\epsilon_iX_i$; its targets $j$ are odd. Its single-factor characteristic modulus is $(1-\lambda\sin^2w)^{1/2}$, and its oriented phase on $|w|<\pi/2$ is $u\arctan(h\tan w)$. Put $e=n(B-j)/2$. Over all pairs $(u,j)$, maximizing mass is equivalent to minimizing
$$
 J=\frac{n^3\lambda\sqrt{n\lambda}}{2\sqrt{2\pi}}
 \int_{-\pi/2}^{\pi/2} W(w)(1-\cos\psi(w))\,dw,
\quad W=(1-\lambda\sin^2 w)^{n/2},\quad
 \psi=2ew/n+B G_h(w),
$$
where
$$
 G_h(w)=\frac{\arctan(h\tan w)}h-w
       =\int_0^w\frac{\lambda\sin^2v}{1-\lambda\sin^2v}\,dv.
$$
Indeed the real Fourier integrand for the mass is $W\cos\psi$ and, since $n,j$ are odd, it is $\pi$-periodic. The normalization of $J$ is common to all competitors. It suffices to check competitors at a mode. By [Darroch's theorem](https://doi.org/10.1214/aoms/1177703287) for the sum of independent Bernoulli variables (translate the original signed sum by its number of negative signs), every such pair has $|B-j|<2$.

Write $x=\sqrt{n\lambda}\,w$, $P(x)=ex+Bx^3/6$ and $H(x)=\tfrac12 n^{3/2}\sqrt\lambda\,\psi(w)$. With $Z$ standard normal, the leading squared norm, in the orthonormal basis $x,(x^3-3x)/\sqrt6$, is
$$
 Q=\mathbb E[P(Z)^2]=(e+B/2)^2+B^2/6. \tag{1}
$$
The following explicit estimates hold for $|w|\le\pi/4$:
$$
 W(w)\le e^{-x^2/2},\qquad
 |G_h(w)-\lambda w^3/3|\le (2\lambda/5)|w|^5,qquad
 |H(x)-P(x)|\le \frac{B}{5n\lambda}|x|^5. \tag{2}
$$
For the first inequality differentiate $-\log(1-\lambda\sin^2 w)-\lambda w^2$ on $[0,\pi/4]$. Its derivative is nonnegative since $w-\sin w\cos w=2\int_0^w\sin^2v\,dv\le2w^3/3$ while $\lambda w\sin^2 w\ge(8\lambda/\pi^2)w^3\ge2w^3/3$ by concavity of sine and $\pi^2<10$. For the second, $1-v^2/3\le (\sin v/v)^2/(1-\lambda\sin^2v)\le1+2v^2$ on this interval (use $\sin v\ge v-v^3/6$, $\sin^2v\le1/2$); integrate. The last estimate follows by rescaling. By $\mathbb E[Z^{10}]=945$ the Gaussian $L^2$ error in the last estimate on any such window is at most $7B/n$, since $\sqrt{945}<31$ and $1/(5\lambda)\le9/40$.

**Upper bound for the desired pair.** At $(u,j)=(T,1)$ we have $B=1-1/n$, $e=-1/2$, and $Q=(1-1/n)^2/6+1/(4n^2)<1/6$. On the central window $|w|\le\pi/4$, use $1-\cos\psi\le\psi^2/2$. By (2) and the triangle inequality the contribution to $J$ is at most $(\sqrt Q+7B/n)^2$. Outside this window $W\le(5/9)^{n/2}$, so the contribution is at most $2n^4(3/4)^n<1/1000$ (check at $n=150$ by integer powers and note the successive ratio is at most $(151/150)^4(3/4)<1$). Thus
$$
 J\le(5/12+7/150)^2+1/1000<1/4. \tag{3}
$$

**Lower bound for any modal competitor.** Retain only the window $|x|\le3$, where $|w|\le3/\sqrt{150(8/9)}<3/11$. Since $1-\lambda\sin^2 w\ge1-x^2/n$, and $-\log(1-v)\le v+v^2/(2(1-v))$ on $[0,1)$,
$$
 W\ge e^{-x^2/2}\exp[-81/(4(n-9))]\ge(5/6)e^{-x^2/2}.
$$
By (2), $|G_h(w)|\le(3/8)\lambda |w|^3$ here. Thus $|\psi|\le 2|w|+(n/3)(3/8)\lambda |w|^3\le(2+9/8)3/11<1$ using $|B-j|<2$. Consequently $1-\cos\psi\ge (11/12)\psi^2/2$.

The restricted Gaussian norm of $P$ is at least $(3/4)\sqrt Q$. To see this, Cauchy–Schwarz in the orthonormal basis of (1) bounds the lost squared norm by $Q$ times the Gaussian tail integral of $Z^2+(Z^3-3Z)^2/6$ over $|Z|>3$. Write $A=\Pr(|Z|>3)$, $b=2e^{-9/2}/\sqrt{2\pi}$. Integration by parts gives that integral as $2A+42b$. The usual single integration bound $A\le b/3$ and $b<1/100$ give $2A+42b<7/16$. For the numerical bound use $\pi>3$, $\sqrt{2/3}<5/6$, and $\sum_{i=0}^8(9/2)^i/i!>250/3$. This proves the norm claim. Since $B\le\sqrt{6Q}$, subtracting the error $7B/n$ from that norm leaves at least $(19/30)\sqrt Q$ by $\sqrt6<5/2$. The weight and cosine bounds therefore imply
$$
 J\ge(5/6)(11/12)(19/30)^2Q. \tag{4}
$$

It remains to separate the arithmetic possibilities; in particular no bound on $u/T$ was assumed. We have $e+B/2=((n+1)B-nj)/2$. For $j\le-1$ this is at least $n/2$. For $j\ge3$, either its absolute value is at least one, or $B>(3n-2)/(n+1)>5/2$, in which case $B^2/6>1$. When $j=1$ and $u\ne T$, the distance from the candidate value $-1/(2n)$ of $e+B/2$ is at least $(n-1/n)/T$, because successive imbalances differ by two. Its absolute value is thus at least $1-1/n^2-1/(2n)>99/100$. In every other modal pair $Q>9/10$. Now (4) is greater than $3971/14400>1/4$, while (3) is less than $1/4$. This proves uniqueness, including the target mode in the chosen orientation.

## Exhaustion of the finite remainder

For $3\le n<150$ odd and $3\le T\le n$ odd there are exactly $1+2+\cdots+74=2775$ pairs. The supplied standard-library exact-integer verifier [finite.py](finite.py) checks them all, including uniqueness of *both* the count and target. Its method is as follows. Reduce $p=r/s$, put $q=s-r$, and at positive-sign count $l$ form
$$
 P_l(z)=(q+rz)^l(r+qz)^{n-l}.
$$
The coefficient of $z^a$ divided by $s^n$ is the mass at $a-(n-l)$. Initialize $P_0$ by binomial coefficients; step from $l$ to $l+1$ by exact division by $r+qz$ and multiplication by $q+rz$. For every $2l\ge n$ inspect **all** coefficients, accumulating all tied maxima, and require the resulting list to be exactly $[(T,(T-1)/2)]$ in imbalance and target coordinates. Positivity, normalization and division remainders (including the top coefficient) are checked. The recorded [output](CHECKS.txt) covers every required pair; the small-bias proof handles $T=1$ at every length. No floating-point comparisons or assumptions about the onset of an asymptotic are used.
