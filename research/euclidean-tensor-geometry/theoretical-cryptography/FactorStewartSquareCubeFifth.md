# A square, a cube and a fifth power in infinitely many square-root intervals

In §4 of [On heights of multiplicatively dependent algebraic numbers (2008)](https://doi.org/10.4064/aa133-2-1), C. L. Stewart conjectured infinitely many integers $N$ for which $[N,N+\sqrt N]$ contains three distinct integers, one a square, one a cube and one a fifth power. We prove this existence assertion, and give a quantitative family with $N$ itself a square.

**Theorem.** Fix $1/\sqrt5<\lambda\le1$. Among the explicit square starts constructed below, the number of distinct $N\le X$ with a square, a fifth power and a cube, in this order, in $[N,N+\lambda\sqrt N]$ is
$$
\left(\frac{\lambda-1/\sqrt5}{2\sqrt5}+o(1)\right)X^{1/30}.
$$
In particular at least $\big((\sqrt5-1)/10+o(1)\big)X^{1/30}$ integers $N\le X$ satisfy Stewart's existence condition.

## A cube and a fifth power less than a square root apart

For integers $n\ge1$ put
$$
a_n=125n^6+3n,\qquad b_n=3125n^{10}+125n^5+1,\qquad
F_n=a_n^5,\qquad C_n=b_n^3 .
$$
Direct expansion gives the exact identity
$$
C_n-F_n=78125n^{15}+5625n^{10}+132n^5+1=:D_n>0 .
\tag{1}
$$
Since $F_n^{1/2}\sim 5^{15/2}n^{15}$ and $78125=5^7$, it follows that
$$
D_n/F_n^{1/2}\longrightarrow 1/\sqrt5.
\tag{2}
$$
The polynomial choice starts with the binomial truncation
$$
t^6+d t,\qquad t^{10}+\tfrac53 d t^5+\tfrac59 d^2 .
$$
Taking $d=75$ and $t=5n$ permits division of the two bases by $5^3$ and $5^5$, respectively. The powers are then divided by the same $5^{15}$, but their normalized separation, measured in square-root units, changes. The resulting polynomials are exactly $a_n,b_n$, and the relevant constant falls below $1$. For reference, the two bases are coprime: $b_n\equiv1\bmod n$ and, setting $v=125n^5+3$, we have $5b_n=v^2-v-1$, so a common factor of $b_n$ and $v$ divides $1$.

## Insert the square and count the starts

Set $q_n=\lfloor\sqrt{F_n}\rfloor$ and $\alpha_n=\sqrt{F_n}-q_n$. With $\binom{5/2}{j}$ the generalized binomial coefficients,
$$
\sqrt{F_n}
=5^{15/2}\left(n^{15}+\sum_{j=1}^3\binom{5/2}{j}(3/125)^j n^{15-5j}\right)+O(n^{-5}).
\tag{3}
$$
The expression in front of the error is a polynomial with irrational leading coefficient $5^{15/2}$. By [Weyl's polynomial equidistribution theorem](https://doi.org/10.1007/BF01475864), its fractional parts are equidistributed modulo $1$. The $O(n^{-5})$ perturbation preserves equidistribution, for example by Weyl's criterion and the bound $|e^{2\pi i h u}-e^{2\pi i h v}|\le 2\pi|h||u-v|$ for each fixed integer $h$. Thus $\alpha_n$ is uniformly distributed on $[0,1)$.

The only conditions on this square start are $\alpha_n>0$, to give three distinct integers, and
$$
\frac{C_n-q_n^2}{q_n}
=\frac{D_n}{q_n}+2\alpha_n+\frac{\alpha_n^2}{q_n}
=\frac1{\sqrt5}+2\alpha_n+o(1)
\le\lambda .
\tag{4}
$$
The $o(1)$ in (4) is independent of where $\alpha_n$ lies in $[0,1)$. Therefore these conditions have natural density $(\lambda-1/\sqrt5)/2$ among the parameters $n$: bracket the threshold for $\alpha_n$ on either side by any fixed error and let that error tend to zero. Equidistribution also ensures the parameters with $\alpha_n=0$ have density zero. The integers $q_n$ strictly increase, since $a_n$ strictly increases by at least one and $t^{5/2}$ grows by more than one on every such step for $t\ge1$. Finally $q_n^2\sim 5^{15}n^{30}$, so the number of possible indices with $q_n^2\le X$ is $(1/\sqrt5+o(1))X^{1/30}$. Multiplying by the parameter density proves the theorem.

## Prior work and scope

[Beukers and Stewart, Neighboring powers (2010), Theorem 1.3 and Lemma 3.3](https://doi.org/10.1016/j.jnt.2009.09.006) obtain the cube/fifth-power separation exponent $1/2$ by binomial truncation. The exponent alone allows an unspecified constant and need not admit a third power inside a square-root interval. Here the specific common rescaling yields the constant $1/\sqrt5$, and the irrational square-root expansion supplies the third power in a positive proportion of the resulting one-parameter family. We did not find the three-power existence conclusion in that article, its [addendum](https://doi.org/10.1016/j.jnt.2010.03.006), or [Zhu's recent discussion of Erdős #458, §8](https://aixiv.online/pdf/2611.00013).

This proves the existence part of Stewart's conjecture. It does not show that every sufficiently large square-root interval contains at most three distinct perfect powers, or classify all intervals that contain three. In particular $a_n=n(125n^5+3)$ is composite for $n>1$; the prime-base question of [Erdős #458](https://www.erdosproblems.com/458) is not resolved.

The [exact verifier](verify_factor_stewart_square_cube_fifth.js) runs 275,918 integer assertions, including polynomial coefficients, an error bound for (3), and all interval decisions for $n\le40{,}000$. It finds 11,006 valid intervals for $\lambda=1$ among those parameters. The infinitude and asymptotic count follow from the proof, not the finite test.
