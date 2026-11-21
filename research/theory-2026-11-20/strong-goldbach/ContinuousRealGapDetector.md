# A uniform signed asymptotic in a single shrinking real zero-gap window

**Correction to the original interpretation.** This particular filter also suppresses the active arithmetic scales. Its negative signed zero-pair asymptotic holds for every large even target under Dirichlet GRH, whether or not the target has a prime-pair representation. It does not give a viable one-sided criterion for binary Goldbach.

Under Dirichlet GRH we evaluate a parity-signed two-zero statistic in one shrinking interval of genuine real gaps at **each even modulus**. The negative main term holds whether or not the target is represented. The filtered statistic loses the arithmetic signal; it cannot prove binary Goldbach. The parity projection and support isolation go back at least to [Gou–Wang–Xu, §3, (3.1), November 2026](https://arxiv.org/html/2611.18825v1#S3); their full asymptotic assumes a separate ratios conjecture in addition to GRH. This note uses a continuous-scale **same-target detector**, with an explicit entire (Chebyshev-type) multiplier and a matching width obstruction for this uniform leakage method. Unlike a dyadic filter, it has no periodic aliases. Unlike an exact reproducer of one prescribed arithmetic weight, this continuum detector assigns a vanishing norm to every live scale, as quantified below.

Let $N>2$ be even, $L=\log N$, $\Phi=\varphi(N)$. Fix nonnegative $f\in C_c^\infty((b_0,b))$ positive near $1/2$, where $0<b_0<1/2<b<1$. Write $m(s)=\int f(u)u^{s-1}\,du$ and $m=m(1)>0$. For $Y>0$ let
$$
 T_N(Y)=(Y\Phi)^{-1}\sum_{\chi\bmod N}\chi(-1)
      \left|\sum_{n}\Lambda(n)\chi(n) f(n/Y)\right|^2.
$$
On $Y\le N$ the orthogonality condition $(nn',N)=1$, $n+n'\equiv0\pmod N$ forces $n+n'=N$. Indeed $0<n+n'<2bY<2N$. For $Y\le N/(2b)$ even this is impossible, so $T_N(Y)=0$. If $N$ has no representation by two primes, $T_N(Y)\ll_f N^{-1/2}L^2$ **uniformly in $Y\le N$**: only $Y\asymp N$ is nonzero; there are $O(\sqrt N)$ possible proper powers up to $N$, and each has at most one complement.

Assume Dirichlet GRH for the primitive conductors dividing $N$, including conductor 1. List the nontrivial zero ordinates $\gamma_j$ of each inducing primitive $L(s,\chi^*)$ with multiplicity; both indices below belong to the same $\chi^*$. Write $M_j=m(1/2+i\gamma_j)$, $t_{ij}=\gamma_i-\gamma_j$. For a bounded multiplier $K$ and a real interval or union $B$ define
$$
 Z_N(K;B)=\Phi^{-1}\sum_{\chi\bmod N}\chi(-1)
   \sum_{t_{ij}\in B}e^{iL t_{ij}}M_i\overline{M_j}K(t_{ij}).
$$
No evenness, reality, independence, or simplicity of individual character zero sets is assumed.

## Continuous pole-preserving detector

For any finite complex measure $\lambda$ supported on $[0,S]$, $0<S\le(1-\eta)L$ with fixed $\eta>0$, let $K(t)=\int e^{-ist}\,d\lambda(s)$. The primitive smooth explicit formula gives
$$
 \int T_N(Ne^{-s})\,d\lambda(s)=\frac{N}{\Phi}m^2 K(-i)
       +Z_N(K;\mathbb R)+O_{f,\eta}\big(\|\lambda\|_{\rm TV}N^{-\eta/2}L^C\big).       \tag{1}
$$
For clarity, the smoothed prime sum divided by $\sqrt Y$ is $\mathbf1_{\chi_0}\sqrt Y m-\sum_j e^{i\gamma_j\log Y}M_j+O_f(Y^{-1/2}\log^2(3N))$ for $N^\eta\le Y\le N$. This follows by Mellin inversion of $-L'/L$ shifted to $-1/2$, collecting the bounded residue from a possible trivial zero at 0, then discarding powers of primes dividing $N$ (total $O_f(\log^2(3N))$ before normalization). The contour on $-1/2$ is $O_f(Y^{-1/2}\log(3N))$ before normalization by the functional equation. The unit-height zero-count bound and smooth transform decay give $\sum_j |M_j|\ll_f L$ uniformly. On squaring, the unique pole-zero cross term is $O_f(\sqrt N L/\Phi)$; $N/\Phi\ll\log\log(3N)$. The remaining errors are $O_f(Y^{-1/2}\log^C(3N))$ after averaging. Termwise integration proves (1); the pole scales by $e^{-s}$, and the pair by $e^{-ist_{ij}}$. In general the resulting gap measure is Hermitian, not a real even measure: values of its Fourier transform at positive and negative scales cannot simply be identified.

Fix any real $t_0\ne0$ and fix $0<c<1/2$. Set $a=cL$, $S=2a$, and
$$
 w=D\sqrt{\frac{\log L}{L}},\qquad I_N=[t_0-w,t_0+w].
$$
Take $D$ sufficiently large in terms of $t_0,c$. Define
$$
 U(t)=e^{-iat}\cos\left(a\sqrt{(t-t_0)^2-w^2}\right),\qquad K_N(t)=U(t)/U(-i).             \tag{2}
$$
The cosine is entire and branch-independent by its power series. Write $v=|\Im\sqrt{(-i-t_0)^2-w^2}|$. Uniformly as $w\to0$ for this fixed $t_0$,
$$
 v=1+\frac{w^2}{2(1+t_0^2)}+O_{t_0}(w^4).
$$
Indeed choose the branch near $-i-t_0$ and expand $z\sqrt{1-w^2/z^2}=z-w^2/(2z)+O_{t_0}(w^4)$. Since $|\cos(x+iy)|\ge\sinh|y|$, $|U(-i)|\ge e^{-a}\sinh(av)\ge \tfrac13 e^{a(v-1)}$ for large $N$. Hence, increasing $D$ if needed, $|U(-i)|\ge L^5$. For all real $t\notin I_N$ the square root is real and $|U(t)|\le1$, so $\sup_{\mathbb R\setminus I_N}|K_N|\le L^{-5}$ along the **entire** real complement, independent of height.

To bound the inverse-transform cost, $C_a(z)=\cos(a\sqrt{z^2-w^2})$ is the Fourier transform of a positive finite measure $\sigma_a$ supported on $[-a,a]$ and of mass $C_a(0)=\cosh(aw)$. One direct proof uses the following Volterra equation, obtained from $C_a''+z^2 C_a=w^2 C_a$ with $C_0=1$, $C'_0=0$:
$$
 C_a(z)=\cos(az)+w^2\int_0^a\frac{\sin((a-b)z)}{z}\,C_b(z)\,db.
$$
The free term represents atoms of mass $1/2$ at $\pm a$, and $\sin(uz)/z$ is the transform of half Lebesgue measure on $[-u,u]$. Successive convolution-integral terms are positive and supported as claimed. Their masses are explicitly $(aw)^{2n}/(2n)!$ at step $n$, so the series converges absolutely in total variation and gives the solution. Modulating by $t_0$ and translating by $a$ gives a complex measure on $[0,2a]$ for $U$. Dividing by $U(-i)$ gives $\lambda_N$ with
$$
 \|\lambda_N\|_{\rm TV}\le\cosh(aw)/|U(-i)|\le\exp(O_{c,D}(\sqrt{L\log L}))=N^{o(1)}.        \tag{3}
$$
Thus $K_N(-i)=1$, the error in (1) is $o(1)$, and the absolute total contribution of all pairs outside $I_N$ is $O_f(L^{-3})$. The same-index and different-index but equal-ordinate terms are outside $I_N$ and discarded with this very bound for all sufficiently large $N$. 
## The negative sign is provable, but independent of representation

For every sufficiently large even $N$ under the same GRH hypothesis,
$$
 \boxed{\displaystyle Z_N(K_N;I_N)=-\frac N\Phi m^2+o_{f,t_0,c,D}(1).}                 \tag{4}
$$
Equality here is complex, with an absolute vanishing error. No hypothesis on prime pairs is needed. The conclusion gives a signed asymptotic for a deliberately amplified two-level weight on one *nonperiodic*, shrinking, off-diagonal interval. It also shows why (4) cannot serve as a Goldbach criterion that is sometimes violated.

Indeed take $h=\log(2b)>0$. All arithmetic scales outside $0\le s<h$ are exactly zero, and throughout the live interval $T_N(Ne^{-s})\ll_f L^2$, even from the trivial bound of $O_f(N)$ candidate pairs. We sharpen the estimate (3) on this short one-sided endpoint of the inverse measure. For $r\ge0$ the defining positive measure $\sigma_a$ gives
$$
 |U(-ir)|_{t_0=0}=e^{-ar}\cosh(a\sqrt{r^2+w^2})
               \le \exp\!\left(\frac{aw^2}{2r}\right)\qquad (r>0).
$$
The unnormalized inverse at any real $t_0$ is the same positive shifted measure with a unit-modulus modulation. The norm of that measure on $[0,h]$ is at most $e^{rh}$ times its Laplace transform at $r$, hence bounded by $\exp(rh+aw^2/(2r))$. Taking $r=\sqrt{aw^2/(2h)}$ gives $\exp(\sqrt{2haw^2})=\exp(O(\sqrt{\log L}))=L^{o(1)}$. The normalization $|U(-i)|\ge L^5$ then gives $\|\lambda_N\|_{[0,h]}\le L^{-5+o(1)}$. It follows that the left side of (1) is $O_f(L^{-3+o(1)})$ for **all** targets; combining with (1) and the absolute complementary leakage proves (4).

The pole normalization is therefore borrowed from scales where the full arithmetic correlation is exactly zero, and the negative signed zero-pair statistic compensates it. This resolves the sign for *this specific* filter; it does not resolve the sign for a filter retaining a live arithmetic signal. In particular a uniform lower bound by $-(1-\delta)(N/\Phi)m^2$ is impossible even on represented targets. Constraints like an exact unit atom at zero delay and no remaining delays in $[0,h]$ instead preserve $T_N(N)$; then the full complement of a bounded real interval **cannot** have uniformly small multiplier. Indeed for any such measure, its Fourier transform averaged on $[T,2T]$ tends to its unit atom by dominated convergence, so the limiting tail supremum is at least one. Using actual zero weights to damp nonuniform tail leakage is a distinct, open strategy.

## Why the width scale is sharp for uniform leakage with bounded causal delay

Let $K(z)=\int_0^{2a}e^{-isz}\,d\lambda(s)$ for any finite complex measure, with $K(-i)=1$. If $|K(t)|\le\epsilon$ everywhere on the real complement of $[t_0-w,t_0+w]$, then
$$
 \boxed{\displaystyle \log(1/\epsilon)\le a\left(|\Im\sqrt{(-i-t_0)^2-w^2}|-1\right).}     \tag{5}
$$
For a direct proof, center the type by $B(z)=e^{iaz}K(z)$, so $|B(z)|\le\|\lambda\|_{\rm TV} e^{a|\Im z|}$. On the simply connected slit plane $\Omega=\mathbb C\setminus(( -\infty,t_0-w]\cup[t_0+w,\infty))$ let $M(z)=\Re\sqrt{w^2-(z-t_0)^2}$, using the branch with positive real part (equivalently $M=|\Im\sqrt{(z-t_0)^2-w^2}|$). This positive harmonic function extends by zero to both slits. We have $M(z)\ge|\Im z|$: the square of $M$ at $z=t_0+x+iy$ is the larger nonnegative root of $X^2+(x^2-y^2-w^2)X-x^2y^2=0$, whose value at $X=y^2$ is $-w^2y^2\le0$. Consequently the analytic function $H(z)=B(z)\exp(-a\sqrt{w^2-(z-t_0)^2})$ is bounded on $\Omega$, with boundary modulus $\le\epsilon$ on the slits. It follows that $|H|\le\epsilon$ throughout: under $z=t_0+w\sin\zeta$ the slit plane is the strip $|\Re\zeta|<\pi/2$, and a bounded analytic function there obeys the maximum modulus bound of its two boundary lines (three-lines theorem, or disk mapping; its two infinite ends have harmonic measure zero). Evaluating at $z=-i$, where $|B(-i)|=e^{a}$, proves (5). The explicit (2) misses this bound by at most a factor 3 in $\epsilon$ for large $a$.

In particular any method demanding a uniform complementary bound $\epsilon\le (\log N)^{-A}$ for some fixed $A>0$, with delays at most $O(\log N)$ and $K(-i)=1$, cannot shrink this genuine real interval to $o(\sqrt{\log\log N/\log N})$. This is a restriction on the specified **uniform-multiplier** method, not on cancellations among the actual L-function zeros, on unbounded delays, or on Goldbach itself.

Relevant scope: [Languasco–Perelli (1996)](https://www.research.unipd.it/retrieve/e14fb267-6015-3de1-e053-1705fe0ac030/%5B3%5D.pdf) concern pair correlation with further averages; [Althöfer–Chen–Perelli–Pintz (November 2026)](https://arxiv.org/html/2611.09386v1#S4) bound exceptional sets rather than this one prescribed target; [Bhowmik–Grimmelt (July 2026)](https://arxiv.org/html/2607.27282v2#S7) use smooth zero formulas on major arcs. Neither pair-correlation heuristic, exceptional-set bound, nor ratios conjecture is used to infer (4). The complex-analytic Chebyshev/slit principle is a classical type of entire-function argument, not a priority claim for approximation theory.
