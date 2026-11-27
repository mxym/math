# Two corollaries of the Erdős #462 short-window concentration theorem

This is an addendum to the [original note and its rectangle estimate (6)](https://github.com/mxym/math/blob/4948666ae3ddab71470045c0b4b99aba14a877c3/research/euclidean-tensor-geometry/theoretical-cryptography/FactorErdos462AlmostAll.md). Both results below are unconditional. Neither claims a lower bound at every starting point.

## 1. Factor balance: uniform weighted CDF and actual counts in fixed bands

For $0\le\lambda\le1$, define $W_\lambda(x,h)$ to count only semiprimes $n=pq$, $p\le q$, in $(x,x+h]$ with $p/\sqrt n\le\lambda$, giving each term weight $1/q$. Let $\mathcal M_\lambda(x,h)$ be the original integral with upper limit $\sqrt t$ in the inner integral replaced by $\lambda\sqrt t$; that inner integral is zero if $\lambda\sqrt t<2$. The full semiprime weight here is $W_1$, not the full composite sum.

For $Z=\sqrt X$, $L=\log X$ and any fixed $A,B>0$, the original concentration estimate extends to
$$
 \frac1X\sum_{X<m\le2X}
    \sup_{\substack{ZL^{-B}\le h\le ZL^B\\0\le\lambda\le1}}
       \left|\frac{ZL^2}{h}\bigl(W_\lambda(m,h)
                              -\mathcal M_\lambda(m,h)\bigr)\right|^2
      \ll_{A,B} L^{-A}.                                  \tag{1}
$$
It also holds with integration over real starting points. Here $h$ can be real.

**Proof of the two-parameter estimate.** Work first with $h=\delta x$, $\delta\le 2L^B/Z$, and fixed $\lambda>0$. The pointwise small-least-factor estimate (4) and its integral analogue (5) in the original note hold uniformly by positivity. Keep the remaining factors in $(ZL^{-K},4ZL^K]$ and the geometric bins of ratio at most $1+\kappa$, $\kappa=L^{-K'}$. The cutoff is $p\le\lambda^2q$. For rectangles straddling or touching this boundary, the continuous points have $u/v$ between $\lambda^2/(1+\kappa)^2$ and $\lambda^2(1+\kappa)^2$. After $t=uv$, they occupy an interval of width $O(\kappa\lambda\sqrt t)$ in $u$ around $\lambda\sqrt t$. Both factor logarithms are comparable to $L$ on the truncated range. Thus the total model over the crossing rectangles is $O(\kappa L^{B-2})$ uniformly on $[X,2X]$. Their union is disjoint except for endpoints and may be bounded by the entire indicated strip. The original rectangle estimate and the triangle inequality transfer the same bound to the discrete sum in normalized $L^2$, up to arbitrary log savings. The rectangles fully inside the cutoff directly use that estimate; all other rectangles are omitted. There are only $O((L^{K'}\log L)^2)$ rectangles. This gives the original fixed-$\delta$ estimate (11) with uniform constants for every fixed $\lambda$; $\lambda=0$ needs no estimate.

Mesh $\delta$ on $[0,2L^B/Z]$ at spacing $Z^{-1}L^{-E}$, and $\lambda$ on $[0,1]$ at spacing at most $L^{-E'}$. The model's variation between adjacent $\delta$'s is $O(L^{-E-2})$ because its density in $t$ is bounded by that of the unrestricted model. For a step $\Delta\lambda$ it is $O(h\Delta\lambda/(ZL))$: wherever the moving integration endpoint is at least $2$, $\log u\ge\log 2$ and $\log(t/u)\ge\tfrac12\log t$. The same bound holds through the endpoint $2$ by truncation. The two sums and models are each nondecreasing separately in the two mesh variables. Bracket the sum by the lower and upper corners for any mesh cell; its absolute error is at most the largest grid error plus the model variation. The grid contains only a fixed power of $L$ points. Bound the mean square of the maximum by the sum of their mean squares, choosing the original saving and $E,E'$ large enough also to absorb $ZL^2/h\le L^{B+2}$. The unit-cell transfer from real to integer starts still loses at most $O(1/Z)$ in the count: changing $x$ over a unit cell changes only a bounded number of endpoints and the ratio attached to each $n$ remains unchanged. This proves (1).

**Consequences.** Write $h_C(x)=C\sqrt x(\log x)^2$ and $L_x=\log x$. For $\lambda>0$ put $a_\lambda=-\log\lambda$. The substitution $u=\sqrt t\,e^{-s}$ in the original model formula, starting the $s$-integral at $a_\lambda$, gives uniformly in $\lambda$
$$
 \mathcal M_\lambda(x,h_C(x))
   =4C\lambda\left(1+
      \frac{4(a_\lambda^2+2a_\lambda+2)}{L_x^2}\right)
                   +O_C(L_x^{-4}).                        \tag{2}
$$
Split at $L_t/4$ as in the original expansion. For $a_\lambda\le L_t/4$, the first two moments are $\lambda$ and $\lambda(a_\lambda^2+2a_\lambda+2)$, and the integrated remainder is $O(L_t^{-4})$ uniformly after normalization. If $a_\lambda>L_t/4$, both the original integral (possibly zero) and those terms are exponentially small times a power of $L_t$. The coefficients are bounded uniformly, so replacing $t$ by $x$ across the short window costs an exponentially small error on the log scale. At $\lambda=0$ the displayed main term is interpreted by continuity.

For every fixed $D>0$, outside $O_{C,D}(XL^{-D})$ integer starts in $[X,2X]$, (1) and Markov's inequality give (2) for $W_\lambda$ itself with the same $O_C(L_x^{-4})$ error, simultaneously for all $\lambda$. Thus the weight-normalized CDF equals
$$
 \frac{W_\lambda(x,h_C(x))}{W_1(x,h_C(x))}
   =\lambda\left(1+\frac{4(a_\lambda^2+2a_\lambda)}{L_x^2}\right)
                         +O_C(L_x^{-4}).
$$
It converges uniformly to the CDF of $U[0,1]$; this law is for the **weights**, not for the uniform measure on semiprimes. For fixed $0<u<v\le1$, the actual, unweighted count on $u<p/\sqrt n\le v$ is
$$
 4C\sqrt x\log(v/u)
   +\frac{16C\sqrt x}{3L_x^2}\bigl((\log v)^3-(\log u)^3\bigr)
   +O_{C,u,v}(\sqrt x\,L_x^{-4}).                         \tag{3}
$$
Indeed at an atom with $\beta=p/\sqrt n$ one has $1/q=\beta/\sqrt n$. Divide the count by $\sqrt x$, replace each factor $\sqrt n/\sqrt x$ by $1+O_C(L_x^2/\sqrt x)$, and integrate $1/\beta$ against $d W_\beta$ on $(u,v]$. The replacement error is $O_{C,u}(L_x^2/\sqrt x)$ since $W_1$ is bounded on the good set. Stieltjes partial summation transfers a uniform CDF error $O_C(L_x^{-4})$ with a constant depending on $u,v$, even if an endpoint is an atom. The derivative of $\beta((-\log\beta)^2+2(-\log\beta)+2)$ is $(\log\beta)^2$, giving the second term in (3).

## 2. Centering at the actual mean: the exponential-minus-one law

Let $N_X$ be uniform on the integers $2\le m\le X$, and $\mu=\mu_C(N_X)$ be the full composite sum as in the original note. Then, with all fixed moments as well as in distribution,
$$
 \frac{L^3}{64C}\left(\mu-4C-\frac{32C}{L^2}\right)
                \longrightarrow \operatorname{Exp}(1).
 \tag{4}
$$
In particular
$$
 \mathbb E\mu=4C+\frac{32C}{L^2}+\frac{64C}{L^3}+O_C(L^{-4}),
 \qquad
 \operatorname{Var}\mu\sim\frac{(64C)^2}{L^6}.             \tag{5}
$$
Centering at $\mathbb E\mu$ gives the limiting law $\operatorname{Exp}(1)-1$, not the law about the fixed number $4C$.

**Proof.** For $R=\log(X/N_X)$, elementary counting gives $R\Rightarrow\operatorname{Exp}(1)$ with uniformly exponentially bounded tails and convergence of all fixed moments. Stirling's formula gives $\mathbb E R=1+O(L/X)$. On $N_X\ge\sqrt X$ the exact composite integral has, by the original expansion,
$$
 \mathcal M(N_X,h_C(N_X))
      =4C+\frac{32C}{L^2}+\frac{64C R}{L^3}
                     +O_C((1+R^2)L^{-4}).
$$
This follows by Taylor expanding $(L-R)^{-2}$ on $0\le R\le L/2$. The remainder after multiplication by $L^3$ is $O_{C,p}(L^{-1})$ in each fixed $L^p$. For $N_X<\sqrt X$ the crude bound $\mu_C(N_X)\ll_C(\log(2N_X))^2$, and the corresponding bound for the integral, make the contribution negligible at all fixed moment scales. On the rest, sum the original dyadic mean-square estimate to get an arbitrary log saving in the quadratic mean of $\mu-\mathcal M$. The same pointwise crude bound upgrades it, by $\mathbb E|D|^p\le\|D\|_\infty^{p-2}\mathbb E|D|^2$ when $p\ge2$, to arbitrary log savings for every fixed moment. Thus the quantity in (4) differs from $R$ by $O_{C,p}(L^{-1})$ in each fixed $L^p$; (4)–(5) follow.

### Version and quantifier distinction

Zhang's [August arXiv v1](https://arxiv.org/abs/2608.24930v1) states $O_C((\log X)^{-2})$ for the second moment about $4C$; the [October v2](https://arxiv.org/abs/2608.24930v2) states $O_C(1)$. These are the bounds stated in each version, without an inference as to why they differ. The original note's $(32C)^2/(\log X)^4$ is the asymptotic for that fixed center, whereas (5) concerns variance about the actual mean. [Henriksson](https://hexagonmath.org/2611.00808v1) treats the lower bound for every starting point under RH; the present results concern unconditional statistics of almost all starts and do not settle that quantifier.

The companion finite verifier checks the crossing-strip envelope, corner bracketing, the atom-weight conversion, and the two exact second-order coefficient identities. It does not test the analytic asymptotics.
