# The leading coefficient in high dimension

This optional consequence concerns (1) of RADIAL.md, not the fixed-length comparison. Let $b^*_{p,d}$ be the supremum of $b$ such that the spherical-to-Gaussian $p$-moment gap is at least $b\sum a_j^4$ for all finite coefficient lists with $\sum a_j^2=1$. For every fixed $0<p<2$,
$$
 \lim_{d\to\infty}d\,b^*_{p,d}=\frac{p(2-p)}4.
$$

For $d\ge4$ use (3)–(4) of RADIAL.md before its rough truncation at 5. Set $\varepsilon_d=d^{-1/4}$. On $|s-1|\le\varepsilon_d$, the expectation in (3) is at least $(1+\varepsilon_d+h^2)^{(p-4)/2}$, uniformly in $a$, because $a^2\le1$ and $\mathbb E|V|^2\le1$. The complementary tangent gaps are nonnegative as before. The fourth central moment bound for $T$ gives
$$
 \mathbb E[(T-1)^2;\ |T-1|\le\varepsilon_d]
 \ \ge\ 2/d-28/(d^2\varepsilon_d^2)=(2/d)(1-o(1)).
$$
The two integrations for the tangent gap introduce the same factor $1/2$ as in the main proof. After summing and sending $h\downarrow0$, the coefficient therefore satisfies
$$
 b^*_{p,d}\ge
 \frac{p(2-p)(d+p-2)(d+p-4)}{8d(d+2)}
 (1+\varepsilon_d)^{(p-4)/2}
 \mathbb E[(T-1)^2;\ |T-1|\le\varepsilon_d].
$$
This proves the claimed limit inferior. With only one coefficient the gap equals $1-\mathbb E|G|^p$, so the reverse limit bound follows from
$$
 \mathbb E|G|^p=
 \frac{\Gamma((d+p)/2)}{(d/2)^{p/2}\Gamma(d/2)}
 =1-\frac{p(2-p)}{4d}+O_p(d^{-2})
$$
by Stirling's formula. No finite-dimensional best coefficient is asserted. ∎
