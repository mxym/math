# The order deficit in a random product of two shifted-prime cyclic groups

Fix an integer $t\ge1$. Choose an ordered pair of distinct primes $p,q$ uniformly from $(X,2X]$ and form the **abstract** abelian group $G=C_{p-1}\times C_{q-1}$. Independently choose $t$ uniform elements of this group. Let $I_X$ be the group exponent divided by the least common multiple of the chosen element orders. This is a distributional question on abstract cyclic groups. No computation of an order, exponent, or factor of a supplied input is part of the statement or proof.

**Theorem.** There is an explicit positive-integer Euler-product law $I_*$, given below. For every fixed $A>0$, there is $B=B(A,t)$ such that uniformly for $1\le L\le\sqrt X/(\log X)^B$,
$$
\sum_{d\ge L}\big|\Pr(I_X=d)-\Pr(I_*=d)\big|
 \ll_{A,t} L^{-t}(\log X)^{-A}. \tag{1}
$$
There are constants $C_t>0$ and $D_t$ such that, for any fixed $\epsilon>0$,
$$
\Pr(I_*\ge L)=\frac{C_t\log L+D_t}{L^t}
 +O_{t,\epsilon}(L^{-t-1/2+\epsilon}) \qquad(L\to\infty). \tag{2}
$$
Thus the tail for $I_X$ in the same range has the same two terms, with the further additive error in (1). This is not just an asymptotic on fixed index values: the integer-valued conditional laws given the tails at $L$ differ by $O_{A,t}((\log X)^{-A})$ in total variation. For $L\to\infty$ in range, the conditional law of $I_X/L$ has limiting survivor $u^{-t}$ for $u\ge1$.

## The local model and its coefficients

For each prime $\ell$, let $A_\ell',B_\ell'$ be independent with survivor $\Pr(A_\ell'\ge j)=1/\varphi(\ell^j)$ for $j\ge1$, modeling the two valuations of the shifted primes. These have masses $\ell^{-j}$ at $j\ge1$ and $(\ell-2)/(\ell-1)$ at zero. Independently let $U_\ell,V_\ell$ have survivor $\ell^{-t j}$ for $j\ge0$. Each of the two variables models the order deficit in one cyclic $\ell$-primary component, before truncation at its size exponent: divisibility by $\ell^j$ of all $t$ uniform coordinates in a cyclic $\ell^a$ group has probability $\ell^{-tj}$ for $j\le a$. The primes' model variables at different $\ell$ are mutually independent. Define the independent local exponents
$$
K_\ell=\max(A_\ell',B_\ell')-
 \max(0,A_\ell'-U_\ell,B_\ell'-V_\ell),\qquad I_*=\prod_\ell\ell^{K_\ell}.
$$

Given the two size valuations $a,b$, if $m=\max(a,b)\ge k\ge1$, then $K_\ell\ge k$ means both sampled-order maxima are at most $m-k$. Its conditional probability is
$$
\ell^{-t k}\,\ell^{-t(k-|a-b|)_+};
$$
it is zero when $m<k$. Put $r_\ell=\ell^{-(t+1)}$. Averaging in the model gives the exact geometric difference
$$
\Pr(K_\ell\ge k)=A_\ell r_\ell^k-B_\ell r_\ell^{2k}, \quad
\begin{aligned}
A_\ell
 &=2\left(\frac1{1-\ell^{-1}}+
      \frac{-1/(\ell-1)+r_\ell/(1-r_\ell)}{1-\ell^{-2}}\right),\\
B_\ell&=\frac{1+r_\ell}{(1-r_\ell)(1-\ell^{-2})}.
\end{aligned} \tag{3}
$$
To see this, count the half with $a=k+j\ge b$ and double, subtracting the diagonal once. For $j\ge0$, summing the second local component's factor over all $b\le k+j$ gives
$$
\Pr(B_\ell'\le j)+\ell^{-j}\sum_{i=1}^k r_\ell^i
=1-\ell^{-j}/(\ell-1)+\ell^{-j}r_\ell(1-r_\ell^k)/(1-r_\ell).
$$
Multiply this by $2\ell^{-(k+j)}\ell^{-t k}$ and sum over $j$. The diagonal to subtract contributes $r_\ell^{2k}/(1-\ell^{-2})$. This yields (3). In particular $\sum_\ell\Pr(K_\ell>0)<\infty$, and $I_*$ is finite almost surely.

## Comparing prime pairs to the model in the rare tail

Write $P_X(u)=\Pr(u\mid p-1)$ for a uniform prime in the interval and $M=\pi(2X)-\pi(X)\asymp X/\log X$. For distinct pairs, let $P_X(u,v)=\Pr(u\mid p-1,v\mid q-1)$ and $w=[u,v]$ be their lcm. Exact counting gives
$$
P_X(u,v)=P_X(u)P_X(v)+
  \frac{P_X(u)P_X(v)-P_X(w)}{M-1}. \tag{4}
$$
In particular $P_X(u,v)\le(M/(M-1))P_X(u)P_X(v)$. Brun–Titchmarsh gives $P_X(u)\ll1/\varphi(u)$ for $u\le X^{3/4}$. Counting integers in the progression gives $P_X(u)\ll (\log X)/\varphi(u)$ throughout (when $u>2X$ it is zero).

For fixed $\ell^k$, set
$$
F_{\ell,k}(a,b)=\mathbf 1_{\max(a,b)\ge k}\,
                  \ell^{-t(k-|a-b|)_+}.
$$
Take first differences in both arguments, with zero values for negative arguments:
$$
c_{\ell,k}(i,j)=F_{\ell,k}(i,j)-F_{\ell,k}(i-1,j)
            -F_{\ell,k}(i,j-1)+F_{\ell,k}(i-1,j-1).
$$
These have modulus at most $4$ and vanish for $\max(i,j)<k$. Telescoping recovers $F_{\ell,k}(a,b)$ by summing $c_{\ell,k}(i,j)$ for $i\le a,j\le b$. Multiplying for all $\ell^k\Vert d$, define $c_d(u,v)$ by the products of the local coefficients, with zero values if $uv$ has a prime outside $d$. For nonzero $c_d(u,v)$ one has $d\mid[u,v]$ and $|c_d(u,v)|\le4^{\omega(d)}$. For $d=1$ take just $c_1(1,1)=1$. Independence of the sampled cyclic components gives
$$
\Pr(d\mid I_X)=d^{-t}\sum_{u,v\ge1}c_d(u,v)P_X(u,v),
\qquad
\Pr(d\mid I_*)=d^{-t}\sum_{u,v\ge1}\frac{c_d(u,v)}{\varphi(u)\varphi(v)}. \tag{5}
$$
The model summation is absolutely convergent. More quantitatively, for fixed $0\le\sigma<1$,
$$
\sum_{u,v\ge1}\frac{|c_d(u,v)|u^\sigma}{\varphi(u)\varphi(v)}
 \ll C_\sigma^{\omega(d)}d^{\sigma-1}. \tag{6}
$$
Each local sum only needs the bound $|c_{\ell,k}(i,j)|\le4$ and the support $\max(i,j)\ge k$. Since $\varphi(\ell^i)^{-1}\le2\ell^{-i}$ for $i\ge0$, geometric summation bounds it by $O_\sigma(\ell^{-(1-\sigma)k}+\ell^{-k})$. The same estimate holds with $v^\sigma$ in place of $u^\sigma$.

Möbius invert divisibility into masses and then use the triangle inequality. The left side of (1) is at most
$$
\sum_{d\ge L}\tau(d)d^{-t}
\sum_{u,v}|c_d(u,v)|
    \left|P_X(u,v)-\frac1{\varphi(u)\varphi(v)}\right|. \tag{7}
$$
Indeed the multiplicity with which a multiple $d$ occurs when summing over masses at least $L$ is at most $\tau(d)$. The model's interchange is justified by (6) at $\sigma=0$ and convergence of $\sum_d\tau(d)C_0^{\omega(d)}d^{-t-1}$ (here $C_0$ is the constant from (6)), and the finite law has finite support.

Let $Y_0=\sqrt X/(\log X)^b$, with $b$ chosen to apply Bombieri–Vinogradov. For the part with $u>Y_0$ or $v>Y_0$, use (6) with $\sigma=1/2$, (4), and the global upper bound for $P_X(u)$. The result is at most
$$
C_t(\log X)^2 Y_0^{-1/2}
 \sum_{d\ge L}\tau(d)C_{1/2}^{\omega(d)} d^{-t-1/2}
 \ll_t L^{-t}(L/Y_0)^{1/2}(\log X)^C . \tag{8}
$$
For the latter estimate, $\tau(d)C_{1/2}^{\omega(d)}$ is bounded by a fixed higher divisor function (choose its order larger than $2C_{1/2}$ and compare prime powers), and that function has summed order $\ll V(\log(2V))^{O(1)}$ for $d\le V$. This bound follows by counting ordered tuples of that many factors.

On $u,v\le Y_0$ take out $d^{-t}\le L^{-t}$. For each $w=[u,v]$,
$$
\sum_{d\mid w}\tau(d)4^{\omega(d)}\le\tau(w)^4\le\tau(u)^4\tau(v)^4.
$$
The correction term of (4) now contributes at most $L^{-t}(\log X)^{O(1)}/M$. For $P_X(u)P_X(v)$ this follows from the Brun–Titchmarsh upper bound and the divisor sums; for $P_X(w)$ group by $w\le Y_0^2$ with at most $\tau(w)^2$ choices of $u,v$ and use the global upper bound above. The required elementary divisor estimates, for any fixed $J$, are $\sum_{u\le V}\tau(u)^J/\varphi(u)\ll_J(\log(2V))^{O_J(1)}$. They follow by bounding truncated sums by Euler products with local factor $1+2^J/\ell+O_J(\ell^{-2})$ and applying Mertens.

It remains to compare $P_X(u)P_X(v)$ with $1/(\varphi(u)\varphi(v))$. Write $\delta_u=|P_X(u)-1/\varphi(u)|$. The difference is $O(\delta_u/\varphi(v)+\delta_v/\varphi(u))$ by Brun–Titchmarsh. With $b$ sufficiently large, Bombieri–Vinogradov centered at the actual prime count $M$ gives $\sum_{u\le Y_0}\delta_u\ll_D(\log X)^{-D}$ for any prescribed $D$. This applies to both endpoints; replacing their logarithmic-integral main terms by $M$ uses the ordinary prime number theorem with arbitrary logarithmic saving. Then
$$
\sum_{u\le Y_0}\tau(u)^4\delta_u
 \le \left(\sum_u\delta_u\right)^{1/2}
     \left(\sum_u\tau(u)^8\delta_u\right)^{1/2}
 \ll_D(\log X)^{-D/2+O(1)},
$$
since $\delta_u\ll 1/\varphi(u)$. Choose $D$ large enough and $B$ larger than $b$ by a sufficiently large constant so that (8) is also $O(L^{-t}(\log X)^{-A})$. This proves (1) and explicitly controls the diagonal removed in sampling the two primes without replacement.

## The logarithm in the model tail

Set $P_\ell=\Pr(K_\ell=0)=1-A_\ell r_\ell+B_\ell r_\ell^2$ and $\kappa_t=\prod_\ell P_\ell>0$. We have $P_\ell\ge1-\ell^{-t}\ge1/2$ since one top-size component alone can attain full order. Define a multiplicative function $w$ by $w(1)=1$ and
$$
w(\ell^k)=\frac{A_\ell(1-r_\ell)-B_\ell(1-r_\ell^2)r_\ell^k}{P_\ell}\quad(k\ge1).
$$
By differences of (3), $\Pr(I_*=n)=\kappa_t w(n)n^{-t-1}$. Since $A_\ell=2+O(\ell^{-2})$, $B_\ell=1+O(\ell^{-2})$ and $r_\ell\le\ell^{-2}$, we have $w(\ell^k)=2+O(\ell^{-2})$ uniformly for $k\ge1$. Let $h$ be defined by $w=\tau*h$ (Dirichlet convolution). Locally,
$$
h(\ell)=O(\ell^{-2}),\quad h(\ell^2)=O(1),\quad
h(\ell^k)=O(r_\ell^{k-2})\quad(k\ge3);
$$
the last two follow by taking second differences of the local sequence $w(\ell^k)$. Consequently $H(s)=\sum_n h(n)n^{-s}$ converges absolutely for $\Re s>1/2$. Also $H(1)>0$, because its absolutely convergent Euler factors are
$(1-1/\ell)^2(1+\sum_{k\ge1}w(\ell^k)\ell^{-k})>0$.

From $\sum_{n\le V}\tau(n)=V\log V+(2\gamma_{\rm E}-1)V+O(\sqrt V)$ and convolution,
$$
\sum_{n\le V}w(n)=H(1)V\log V+C_*V+O_{t,\epsilon}(V^{1/2+\epsilon}),
\qquad C_*=(2\gamma_{\rm E}-1)H(1)+H'(1).
$$
The error follows by absolute convergence at $1/2+\epsilon/2$, both for the convolution error and the omitted tails in the main terms. Partial summation yields (2) with
$$
C_t=\kappa_t H(1)/t,\qquad
D_t=\kappa_t\big(C_*/t+(t+1)H(1)/t^2\big).
$$
Using $\ge L$ instead of $>L$ changes only the allowed error (or evaluate the strict tail at $\lceil L\rceil-1$). In particular the model tail is bounded below by a constant times $L^{-t}\log(2L)$ on all $L\ge1$. Normalizing (1) proves the conditional claim. The source of the logarithm is the local coefficient $2$ at each positive prime-power exponent and the consequent $\tau$ factor, rather than an assumed independence of the actual prime progressions.

## Relation and checks

[Luca–Shparlinski, *Average multiplicative orders of elements modulo n*](https://doi.org/10.4064/aa109-4-7) and [Kurlberg–Pomerance, *On a problem of Arnold*](https://arxiv.org/abs/1108.5209) treat means of orders, the latter for a fixed element. [Sutherland's *Order computations in generic groups*](https://math.mit.edu/~drew/sutherland-phd.pdf) studies abstract group exponents and comparison probabilities; the statistic here is the full averaged deficit law, particularly its growing-threshold relative tail. The analytic inputs are [Bombieri](https://doi.org/10.1112/S0025579300005313) and [Montgomery–Vaughan](https://doi.org/10.1112/S0025579300004708). The smaller-tail model of [two common shifted-prime divisors](FactorLargeCommonDivisorLaw.md) is a different random variable: it involves a minimum, not the deficit of the maximum.

[Exact toy checks](verify_factor_abstract_order_deficit.js) test the local geometric identities, two-dimensional finite differences and finite joint-count identities on small data. They do not verify the analytic estimates or implement a factor, group-order, or exponent solver.
