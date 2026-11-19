# Two landmarks for the crossing of beta distribution functions, and a binomial consequence

Yongxian Zhang (张永贤). AI-assisted research note; internally checked, not externally peer reviewed, November 19, 2026.

Let $0<r<1$, $q=1-r$, and $F_a$ be the cdf of $X_a\sim\operatorname{Beta}(ar,aq)$, for every real $a>0$. The parameter $a$ is the total shape, and the mean $r$ does not vary.

**Theorem 1.** If $r>1/2$, then $a\mapsto F_a(1/2)$ is strictly decreasing and $a\mapsto F_a(r)$ is strictly increasing. For each $a_2>a_1>0$ the unique interior point where the two cdfs agree lies strictly between $1/2$ and $r$. If $r<1/2$, the monotonicities reverse and the crossing lies strictly between $r$ and $1/2$. If $r=1/2$ the crossing is $1/2$ and its cdf is constantly $1/2$.

See [SOURCES.md](SOURCES.md) for prior results and access limitations. The first comparison at $1/2$ answers the motivating question attributed to Subhash Kochar in [Portnoy, Torrado and Veerman, §6](https://arxiv.org/html/2406.02894v1). That paper proves the existence and uniqueness of the interior crossing in Theorem 4.3; we locate it, not claim that it exists for the first time. Their citation of Alam (1979) is discussed in the source notes.

**Theorem 2.** For each integer $b_0\ge2$, each $0\le p\le 1/b_0\le t\le1$, and each positive integer $k$,
$$
 \Pr\{\operatorname{Bin}(\lfloor k/t\rfloor,p)\ge k\}
 \le 1-(1-p)^{\lfloor1/t\rfloor}.
$$
The right side is attained by $k=1$. This is the precise unnumbered binomial question at the end of [Fokkink, Meester and Pelekis, §7](https://alea.impa.br/articles/v20/20-07.pdf). It does not compare arbitrary unequal stakes, establish Csóka's Conjecture 1.1, or assert that the floored sequence decreases at every successive $k$.

## 1. Folding at one half

Put $U=\log(X_a/(1-X_a))$. The Jacobian $dx=x(1-x)du$ gives a density in $u$ proportional to
$$
 \exp(a(r-1/2)u)[2\cosh(u/2)]^{-a}.
$$
Conditional on $V=a|U|=v>0$, the probability of the negative sign is $h(v)=(1+\exp((2r-1)v))^{-1}$, independently of $a$. The density $g_a$ of $V$ on $(0,\infty)$ is proportional to $\cosh((r-1/2)v)\cosh(v/(2a))^{-a}$. For $a_2>a_1$,
$$
 \frac{d}{dv}\log\frac{g_{a_2}(v)}{g_{a_1}(v)}
 =\tfrac12\big[\tanh(v/(2a_1))-\tanh(v/(2a_2))\big]>0.
$$
For $r>1/2$, $h$ is strictly decreasing. Thus $F_{a_2}(1/2)<F_{a_1}(1/2)$: integrating $h$ under $g_{a_2}$ amounts to reweighting $g_{a_1}$ by a strictly increasing normalized likelihood ratio, whose covariance with $h$ is negative. For clarity, the covariance is one half the expectation of the product of the differences at two independent draws. Strictness holds because the densities are positive and the functions are strictly monotone. Reflection $x\mapsto1-x$ gives the reverse for $r<1/2$.

## 2. Pairing levels at the mean

Inverse-branch integration already appears in [Kane (2001), proof of Theorem 2.1](https://doi.org/10.1090/S0002-9939-00-05776-2), for a shifted beta ray. Here we require the branch displacement ratio for the unshifted law. Assume $0<r<1/2$. Set
$$
 D(x)= r\log(r/x)+q\log(q/(1-x)).
$$
It is zero at $r$, tends to infinity at both endpoints, and has derivative $(x-r)/(x(1-x))$. For a given level $z>0$ write its two roots as $r-L(z)$ and $r+R(z)$. Then $0<L<r$, $0<R<q$, and $L,R$ increase strictly with $z$.

**Claim.** $R(z)/L(z)$ is strictly increasing. For $b>0$ and $0<l<\min(r,q/b)$ put $A_b(l)=D(r+bl)-D(r-l)$. Its derivative has the sign of
$$
 b^2(r-l)(q+l)-(r+bl)(q-bl)
 =(b^2-1)rq-(q-r)(b^2+b)l.                                      \tag{1}
$$
This follows by factoring out the positive $l$ and the two positive denominators. In particular $A_1(l)<0$ for $l>0$ since $A_1(0)=0$, so $R>L$. Take $b=R/L>1$. For this $b$, $A_b(0)=0$, and $A_b$ increases initially. Formula (1) shows that its derivative can change sign only from positive to negative; at its positive zero $l=L$ the derivative is strictly negative. Since $\partial_b A_b(l)=lD'(r+bl)>0$, implicit differentiation along $A_b(l)=0$ gives $db/dl>0$. This proves the claim.

The beta law has density proportional to $e^{-aD(x)}/[x(1-x)]$. Under $z=D(x)$ its two branch contributions are proportional to $e^{-az}/L(z)$ and $e^{-az}/R(z)$, respectively. Consequently, conditional on $z$, the left-branch probability is $R/(L+R)$, a strictly increasing function of $z$ by the claim. Increasing $a$ reweights the distribution of $z$ by a factor proportional to $e^{-(a_2-a_1)z}$, strictly decreasing. The covariance argument now yields $F_{a_2}(r)<F_{a_1}(r)$. The change of variables is performed separately in the interiors of the branches; the potential singularity at $z=0$ is integrable as this is the pushforward of a probability law and there is no atom at $x=r$. Reflection gives the comparison for $r>1/2$.

The density ratio $f_{a_2}(x)/f_{a_1}(x)$ is proportional to $[x^r(1-x)^q]^{a_2-a_1}$, rising strictly from zero to its maximum at $r$, then decreasing strictly to zero. Normalization forces that maximum above one. Thus the density difference has signs $-,+,-$ and the cdf difference has exactly one interior zero (strictly negative before it and strictly positive after). Together the two strict comparisons trap that zero at the stated locations. Symmetry settles $r=1/2$. This recovers the earlier uniqueness argument as well as locating the crossing.

## 3. The floored binomial inequality

For integers $b\ge2$, $k\ge1$, let
$$
 H_k^{(e)}(u)=\Pr\{\operatorname{Bin}(bk-1+e,u)\ge k\},\quad e\in\{0,1\}.
$$
These are beta cdfs with shapes $k,(b-1)k+e$. This follows by differentiating the binomial tail (intermediate terms telescope) and using its zero value at $u=0$. For $k>1$ the density ratio of $H_k^{(e)}$ to $H_1^{(e)}$ is proportional to $[u(1-u)^{b-1}]^{k-1}$, strictly increasing for $0<u<1/b$, in both cases. The corresponding cdf ratio is increasing up to $1/b$, because it is the average of this increasing density ratio on $[0,u]$ with respect to the positive $H_1^{(e)}$ density. In particular, comparison at $1/b$ suffices throughout $0\le u\le1/b$.

For $e=0$ the mean of the beta law is $r=1/b$. Section 2 and symmetry for $b=2$ give $H_k^{(0)}(1/b)\le H_1^{(0)}(1/b)$. For $e=1$ the endpoint inequality is the classical Chaundy–Bullard theorem, quoted in the question paper as Theorem 7.1. It also follows directly here: at $u=1/b$, adding the final Bernoulli gives
$$
 H_k^{(1)}(u)=H_k^{(0)}(u)+u\Pr\{\operatorname{Bin}(bk-1,u)=k-1\}
 =H_k^{(0)}(u)+u\Pr\{\operatorname{Bin}(bk,u)=k\}.
$$
The last identity follows from $k/(bku)=1$. This central point is the mode of $\operatorname{Bin}(bk,1/b)$ by the ratio of consecutive masses. Adding an independent block of $b$ trials cannot increase the maximum point mass, since convolution averages translates of the old pmf. The $e=0$ endpoint term is likewise nonincreasing in $k$ by Section 2. This proves the $e=1$ endpoint comparison without relying on the classical theorem.

If $1/t=b$ is integral, then $p\le t$, and $e=1$ proves the result for $b\ge2$; if $t=1$ the inequality is just $p^k\le p$. Otherwise let $b=\lceil1/t\rceil\ge2$. Since $1/t\le b_0$, we have $b\le b_0$, $p\le1/b$, $\lfloor k/t\rfloor\le bk-1$, and $\lfloor1/t\rfloor=b-1$. Adding independent Bernoulli trials increases the tail. Thus the left side is at most $H_k^{(0)}(p)\le H_1^{(0)}(p)=1-(1-p)^{b-1}$. This covers every endpoint and gives the stated maximum.

**Prior-tool alternative for the off-reciprocal integer comparison.** [Fokkink, Papavassiliou and Pelekis, Thm 1.1](https://www.math.uni.wroc.pl/~pms/files_doi/g00050/g00050.pdf) gives another route. At $u=1/b$ take $S\sim\mathrm{Bin}(bk-1,u)$ and independent $Y\sim\mathrm{Bin}(b,u)$. Choose $k$ as one of the two modes of $S$. In their definition $S$ is right-skewed: the ratio $v_i=\Pr(S=k-i)/\Pr(S=k+i-1)$ starts at $v_1=1$, and for $1\le i<k$,
$$
 \frac{v_{i+1}}{v_i}=\frac{(b-1)^2(k^2-i^2)}{(b-1)^2 k^2-i^2}\le1.
$$
Since $Y$ has mean one, it is left-loaded by their Lemma 2.1 and Definition 1.2(L2). Their Theorem 1.1 implies $H_{k+1}^{(0)}(1/b)\le H_k^{(0)}(1/b)$. Thus the discrete endpoint reduction also has a proof with pre-existing tools; it should not be marketed as an unrelated new beta theorem.
