# Local pairwise dominance is global for every positive power of completion time

**Yongxian Zhang.** We consider the nonpreemptive single-machine problem with all jobs available at zero, positive processing times and weights, and objective $\sum_h w_h C_h^\beta$. Local dominance of $i$ over $j$ means that placing $ij$ instead of $ji$ strictly reduces cost at **every** possible start time; global dominance means that putting $j$ before $i$ cannot occur in an optimal schedule, irrespective of the intervening jobs and prefix. This is the pair-universal relation of [Bansal, Dürr, Thang and Vásquez](https://arxiv.org/pdf/1304.6188), not an equivalence between adjacent-swap local optima and globally optimal schedules for whole instances.

**Theorem.** For $0<\beta<1$, $p=p_i>q=p_j>0$, put $f(x)=x^\beta$ and
\[
h_0=\frac{f(p+q)-f(q)}{f(p+q)-f(p)}.
\]
If $w_i/w_j>h_0$, then $i$ globally precedes $j$. More precisely, for an arbitrary prefix and suffix, and any nonempty intervening block $B$, at least one of $iBj$ and $Bij$ strictly improves $jBi$, even when $w_i/w_j=h_0$. For an empty block the ordinary adjacent comparison applies.

The original paper's Eq. (2) and Lemma 5 characterize strict local dominance in this case by $w_i/w_j>h_0$ (the critical endpoint is attained at $t=0$). Its Theorems 1 and 2 settle $p_i\le p_j$ and $\beta\ge1$; Theorem 3 gives a sufficient condition $(p_i/p_j)^{2-\beta}$ in the remaining regime. The theorem therefore completes the strict local-to-global implication for all positive powers, as in its Conjecture 1. The converse is the universal adjacent case: a counter-comparison at any prescribed start time is a two-job instance after that prefix (a sufficiently high-priority initial job can force a positive start time). In case of equality at zero the adjacent jobs tie there; neither order is uniquely forced. No claim about the computational complexity of general exact scheduling follows.

## 1. Eliminating the intervening weights

Write $D_l(x)=f(x+l)-f(x)$, $g=f'$, and $\gamma=1-\beta\in(0,1)$, so $g(x)=\beta x^{-\gamma}$. Let the prefix duration be $a\ge0$, let $b=a+\sum_{h\in B}p_h>a$, and write $x_h=a+\sum_{u\in B:\,u\text{ up to }h}p_u$. Divide all weights by $w_j$ so $w_j=1$, and put $h_*=w_i/w_j$. In the comparisons that follow the prefix and suffix do not change. Set $E=f(b+p+q)-f(a+q)$ and $A=f(b+p+q)-f(a+p)$.

Suppose $jBi$ costs no more than either alternative. From $Bij$ and $iBj$, respectively, direct subtraction gives
\[
 \sum_{h\in B} w_h D_q(x_h)\le E-h_*D_q(b+p),\qquad
 h_* A-E\le\sum_{h\in B} w_h [D_p(x_h)-D_q(x_h)].
\]
Here $w_h$ are the rescaled weights. The ratio $D_p(x)/D_q(x)$ increases with $x$: after subtracting one, it is the ratio of integrals of $g(x+u)$ on $[q,p]$ and $[0,q]$. Their logarithmic derivatives average $-\gamma/(x+u)$ under the respective tilted weights, and every point of the former interval is to the right of every point of the latter. We only need $x>0$. Thus, with $z=D_q(b)/D_p(b)\in(0,1)$, the second sum is at most $(1/z-1)$ times the first. Rearrangement yields
\[
 h_*\,\big[D_q(b+p)+z(f(b+p)-f(a+p))\big]\le f(b+p+q)-f(a+q). \tag{1}
\]
We prove the **strict reverse** of (1) at $h_*=h_0$.

## 2. The two endpoints of the prefix

Hold $b>0$ fixed and let $V(a)$ be the left side minus the right side of (1) with $h_*=h_0$. On $0\le a\le b$,
\[
 V'(a)=g(a+p)\left[\left(\frac{a+p}{a+q}\right)^\gamma-h_0 z\right].
\]
The bracket decreases; hence the minimum is at $a=0$ or $a=b$. At $b$ the desired inequality is the strict adjacent comparison $D_p(b+q)/D_q(b+p)<h_0$, by the original Lemma 5. Directly, this ratio is the ratio of integrals on $[q,p+q]$ and $[p,p+q]$, translated by $b$; subtracting one leaves the ratio on the two disjoint intervals $[q,p]$ and $[p,p+q]$, which decreases strictly by the same logarithmic-derivative argument as above.

At $a=0$, use $h_0 D_q(p)=D_p(q)$ to cancel constants. Expanding $V(0)$ gives
\[
 (h_0-1)D_b(p+q)-h_0(1-z)D_b(p).
\]
Since $1-1/h_0=D_{p-q}(q)/D_p(q)$, positivity is precisely the inequality
\[
 \frac{D_{p-q}(b+q)}{D_p(b)}\frac{D_b(p)}{D_b(p+q)}
 <
 \frac{D_{p-q}(q)}{D_p(q)}. \tag{2}
\]

## 3. Separating the two sides

For $p>0$, $b>0$ and $0<q<p$, the following common separator lies strictly between the two sides of (2):
\[
 T=\frac{p-q}{p}\left(\frac{p+q}{p}\right)^{\gamma/2}.
\]

**Upper estimate for the left side.** Denote the left side of (2) by $U(q)$, treating $p,b$ as fixed. The derivative of $\log(U(q)/(p-q))$ is
\[
 \frac{1}{p-q}-\frac{g(b+q)}{D_{p-q}(b+q)}
 +\frac{g(p+q)-g(b+p+q)}{D_b(p+q)}. \tag{3}
\]
For any $l,c>0$, integrate $-g'(c+u)=\gamma g(c+u)/(c+u)$ to get
\[
 \frac{g(c)}{D_l(c)}-\frac{1}{l}
 =\frac{\gamma}{D_l(c)}\int_0^l(1-u/l)\frac{g(c+u)}{c+u}\,du
 \ \ge\ \frac{\gamma}{2(c+l)}.
\]
Indeed $1/(c+u)\ge1/(c+l)$ and the decreasing density $g(c+u)$ gives the decreasing linear function $1-u/l$ expectation at least its uniform mean $1/2$ (or pair $u$ and $l-u$).

A second estimate is
\[
 \frac{g(c)-g(c+l)}{D_l(c)}
 \le\frac{\gamma}{2}\left(\frac1c+\frac1{c+l}\right).
\]
The left side divided by $\gamma$ is the expectation of $1/x$ with weight $x^{-\gamma}$ on $[c,c+l]$. Reweighting by the decreasing function $x^{\gamma-1}$ increases this expectation, by nonnegative covariance of two decreasing functions. Under the resulting $dx/x$ weight, $y=\log x$ is uniform; convexity of $e^{-y}$ bounds its average by the arithmetic mean of its endpoint values.

Applying these two estimates to (3) with $(c,l)=(b+q,p-q)$ and $(p+q,b)$, respectively, bounds (3) by
\[
 \frac{\gamma}{2}\left(-\frac1{b+p}+\frac1{p+q}+\frac1{p+q+b}\right)
 <\frac{\gamma}{2(p+q)}.
\]
Now $U(0)=1$. Integrate from $0$ to $q$ to obtain $U(q)<T$.

**Lower estimate for the right side.** For $0<u<v$,
\[
 \frac{v^\beta-u^\beta}{v-u}
 =\beta(uv)^{-\gamma/2} S_\beta\!\left(\tfrac12\log(v/u)\right),
 \qquad S_\beta(y)=\frac{\sinh(\beta y)}{\beta\sinh y}.
\]
This identity follows by taking $u=\sqrt{uv}\,e^{-y}$ and $v=\sqrt{uv}\,e^y$. The function $S_\beta$ decreases strictly for $y>0$: $y\coth y$ increases, since $\sinh y\cosh y>y$. Apply the identity on $[q,p]$ and $[q,p+q]$. The former logarithmic half-width is smaller, so
\[
 \frac{D_{p-q}(q)}{D_p(q)}
 =T\,
 \frac{S_\beta(\tfrac12\log(p/q))}
      {S_\beta(\tfrac12\log((p+q)/q))}
 > T.
\]
This proves (2) and contradicts (1) for $h_*\ge h_0$. When $B$ is empty, the cost test is precisely the original adjacent one, including the stated distinction at $t=0$. This proves the theorem.
