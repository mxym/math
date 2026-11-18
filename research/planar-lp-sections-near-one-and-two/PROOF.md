# The left-hand neighborhood of two

**Claim.** For each fixed $n\ge4$, for every $p<2$ sufficiently close to two, the minimum-area central two-plane section of $B_p^n=\{x\in\mathbb R^n:\sum_j|x_j|^p\le1\}$ is on the [regular plane](README.md) and on no other plane except its signed coordinate permutations.

## 1. Frame, area, and first two variations

Choose an orthonormal basis of the plane as the columns of an $n\times2$ matrix. Its rows are $\sqrt{w_j}(\cos\alpha_j,\sin\alpha_j)$; a zero row can be assigned any angle. Write $\phi_j=2\alpha_j$ and $z_j=e^{i\phi_j}$. By the double-angle identities, the frame equations are precisely

$$
\sum_j w_j=2,\qquad \sum_j w_j z_j=0,\qquad w_j\ge0.
$$

Conversely these equations construct an orthonormal frame; in particular $w_j\le1$. A common rotation or reflection of its row vectors changes the column basis, not the plane. Passing to doubled angles has factored out row signs. Let $s_j(\theta)=w_j\cos^2(\theta-\alpha_j)$, so $\sum_js_j=1$ pointwise. Write angular averages on the circle as $\langle\,\cdot\,\rangle$. By polar integration, for $\delta=1-p/2$ the area divided by $\pi$ is

$$
V_\delta=\left\langle\left(\sum_j s_j^{1-\delta}\right)^{-1/(1-\delta)}\right\rangle.
$$

Set $L=\sum_j s_j\log s_j$ and $M=\sum_j s_j\log^2s_j$, giving zero terms their continuous values. Uniformly on the compact frame space, for $0\le\delta\le1/8$,

$$
V_\delta=1+\delta A+\delta^2 B+O_n(\delta^3),\qquad
A=\langle L\rangle,\qquad B=\langle L-M/2+L^2\rangle.
$$

Indeed the inner sum is $1-\delta L+\delta^2M/2+O_n(\delta^3)$. Take its logarithm, multiply by $-1/(1-\delta)$, and exponentiate. Uniformity follows because $x^{1-\delta}|\log x|^j$ is bounded on $[0,1]$ for $j\le3$ and the inner sum is at least one. In particular $A,B$ are continuous even at zero rows. For $c=\cos^2\theta$,

$$
A=\tfrac12\sum_j w_j\log w_j+2\langle c\log c\rangle .
$$

Strict convexity selects exactly the equal weights $w_j=w_*=2/n$ at first order. At those weights $\langle L\rangle$ and $\langle M\rangle$ are independent of the row directions. We must therefore minimize $\langle L^2\rangle$ at second order.

## 2. Global angular selection at equal weights

Write $K(x)=u\log u$ where $u=(1+\cos x)/2$. For $k\ge2$ its complex Fourier coefficient is $(-1)^k/[2k(k^2-1)]$: the coefficients of $\log u$ for $k\ge1$ are $(-1)^{k-1}/k$ by the logarithm series (take its Abel limit in $L^1$); multiplication by $u$ combines neighbors with weights $1/4,1/2,1/4$. In $L$ the $\log w_*$ term is constant, and the first nonconstant frequency of $K$ cancels by $\sum_jz_j=0$. Parseval, including both conjugate frequencies, gives

$$
B=B_0+\tfrac12w_*^2\mathcal E,\qquad
\mathcal E=\sum_{k=2}^{\infty}a_k|P_k|^2,\quad
a_k=\frac1{k^2(k^2-1)^2},\quad P_k=\sum_j z_j^k ,
$$

where $B_0$ depends only on $n$.

The sequence $a_{s+2}$ is a moment sequence on $(0,1)$. Map six variables in $(0,1)$ to their product $r$, using the product of the measures $x^{d-1}dx$ for $d=1,1,2,2,3,3$. The resulting finite measure $\mu$ charges every nonempty open subinterval and has $\int r^s\,d\mu=1/[(s+1)^2(s+2)^2(s+3)^2]$ for $s\ge0$.

For fixed $0<r<1$, the circle Poisson kernel

$$
K_r(\varphi)=\frac{1-r^2}{(1-r)^2+r|1-e^{i\varphi}|^2}
$$

is a completely monotone function of squared chordal distance. By [Cohn–Kumar, Theorem 1.2](https://arxiv.org/abs/math/0607446v2), the regular $n$-gon minimizes its sum over pairs: it has $m=\lfloor n/2\rfloor$ distinct interpoint distances and is an $(n-1)$-design (its nonconstant Fourier moments through $n-1$ vanish), hence a $(2m-1)$-design. The comparison extends to repeated sites by continuity, **before** imposing the centroid constraint. Including the diagonal and counting ordered pairs sends every pair energy to

$$
n^2+2\sum_{k\ge1}r^k |P_k|^2 .
$$

For tight equal-weight frames $P_1=0$, so the regular configuration minimizes $\sum_{k\ge2}r^{k-2}|P_k|^2$ for each $r$. Integrating these nonnegative series against $\mu$ identifies $\mathcal E$. If a configuration attains the same energy, the nonnegative continuous difference at fixed $r$ must vanish for every $r\in(0,1)$. Equality of the power series gives $P_1=\cdots=P_{n-1}=0$ as for the regular polygon. Newton's identities then give $\prod_j(t-z_j)=t^n+c$ with $|c|=1$, so the doubled angles form a rotated regular $n$-gon. [The internal review](REVIEW.md) also proves the needed Poisson comparison directly.

Now take any sequence of minimizers with $\delta\downarrow0$ and extract a convergent subsequence. Compare Section 1's uniform expansion against a regular frame. First $A\to A_{\min}$, so all limiting weights are equal. Next divide the comparison by $\delta^2$ after canceling $1+\delta A_{\min}$: dropping $(A-A_{\min})/\delta\ge0$ gives $\limsup B\le B_{\rm reg}$. The limiting angles are therefore regular by the equality case just proved. Hence every minimizer approaches the regular-frame orbit. This is a localization statement, not yet exact minimization.

## 3. A chart and the angular Hessian

Write $z_j^0=e^{2\pi i j/n}$, $w_j=w_*+u_j$ with $\sum u_j=0$. Choose the common rotation so that the small increments $\eta_j=\phi_j-2\pi j/n$ have zero mean. Define

$$
Y=\{y\in\mathbb R^n:\sum_j y_j=0,\ \sum_j z_j^0 y_j=0\}.
$$

In the tightness equation $\sum_j(w_*+u_j)z_j^0 e^{i\eta_j}=0$, the two real directions $\cos(2\pi j/n),\sin(2\pi j/n)$ in $\eta$ give an invertible differential onto $\mathbb C$: their images are $iw_*n/2,-w_*n/2$. Thus the implicit function theorem gives smooth coordinates $(u,y)$, with $y$ the orthogonal projection of $\eta$ to $Y$. The $y$-derivative of $\eta$ at the origin is the identity on $Y$.

The regular point is stationary for every exponent considered: cycling rows and undoing a common rotation acts by cyclic permutation on both $u$ and $y$, fixes the origin, and preserves area. The spaces have zero mean, so averaging the orbit of any tangent vector gives zero. There is no nonzero invariant linear functional. The separate regularity statement used for differentiation is given in Section 4.

Consider $\mathcal E$ as a function of the unrestricted angles. Its gradient at regular is zero because cyclic symmetry makes the components equal and common rotation invariance makes their sum vanish. Thus the second derivative along an angle path in the chart is the straight-line Hessian on its tangent, with no chart-acceleration term. For $y\in Y$, put $S_s=\sum_j(z_j^0)^s y_j$ and $b_k=k^2a_k=(k^2-1)^{-2}$. Along $\phi_j=2\pi j/n+ty_j$,

$$
\tfrac12\mathcal E''(0)=\sum_{k\ge2}b_k|S_{k\bmod n}|^2
  -n\sum_{\ell\ge1}b_{\ell n}\sum_j y_j^2 .
$$

The negative term comes only from $k$ divisible by $n$, for which $P_k(0)=n$. For the other $k$, $P_k(0)=0$. Termwise differentiation is justified by $\sum k^2a_k<\infty$. We have $S_0=S_1=S_{n-1}=0$, $n\sum_j y_j^2=\sum_s|S_s|^2$ (one complete residue system), and $|S_s|^2=|S_{n-s}|^2$. Symmetrizing the residue coefficients gives the coefficient of $|S_s|^2$ for $2\le s\le n-2$ as

$$
\lambda_s=\tfrac12 b_s+\tfrac12\sum_{\ell\ge1}
  (b_{\ell n-s}+b_{\ell n+s}-2b_{\ell n}).
$$

Indeed the positive sum of $b_k$ in the two residue classes, averaged, is $\tfrac12[b_s+\sum_{\ell\ge1}(b_{\ell n-s}+b_{\ell n+s})]$. This includes $s=n/2$ when $n$ is even: that class appears twice before taking the average. Since $b(x)=(x^2-1)^{-2}$ is strictly convex for $x>1$ and the arguments are at least two, $\lambda_s\ge b_s/2>0$. Thus the $yy$-block of $D^2B$ is positive definite at the origin. No dimension-uniform spectral gap is needed.

## 4. Mixed regularity and exact minimization

Locally the expansion of Section 1 has an $O_n(\delta^3)$ remainder **in the frame $C^2$ norm**. Here is a common regularity argument which will also apply in the companion near-one proof. Take a small closed chart ball where all weights are positive and the $2n$ circle points $\alpha_j\pm\pi/2$ are separated uniformly. Around each point use a smooth angular cutoff, equal to one near the point, translated with it, with the supports disjoint. Decompose the angular integral into these pieces and the remainder. In each piece substitute $\theta=\alpha_j\pm\pi/2+s$. The only cosine that can vanish now occurs as $|\sin s|^p$, independent of all frame parameters. Every other row stays away from its zero on this support. The integrand's outer denominator stays bounded away from zero. Differentiating up to twice in frame parameters and three times in $p$ gives uniformly dominated terms: for $p$ in a positive compact interval, $|\sin s|^p|\log|\sin s||^a$ is bounded, with its continuous zero convention, for $a\le3$. On the remainder the cutoff and its derivatives vanish near all moving zeros. Thus integration gives continuous mixed derivatives through these orders, with no spatial differentiation across a cusp. Taylor's theorem in $\delta$ proves the asserted uniform local $C^2$ control. No global derivative bound at degenerate frames is asserted.

In these coordinates $A$ depends only on $u$ and has uniformly positive Hessian in $u$. The $yy$-Hessian of $B$ is positive by Section 3, hence remains positive on a smaller fixed ball, where the other blocks are bounded. For constants $c,C>0$ depending on $n$, the area Hessian on tangent increments $(U,H)$ satisfies, for all sufficiently small $\delta>0$,

$$
D^2V_\delta[(U,H),(U,H)]\ge
 c\delta|U|^2+c\delta^2|H|^2-C\delta^2|U|\,|H|.
$$

The last term is at most $c\delta|U|^2/2+C'\delta^3|H|^2$ in magnitude. Shrinking $\delta$ makes the Hessian positive definite on this fixed convex ball. The origin is stationary by Section 3 and is its unique minimum. All global minimizers eventually belong to this ball after row signs, permutations and a choice of column basis, by Section 2. This proves the claim. ∎
