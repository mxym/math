# Explicit all-rank transmission constant

For the one-end probability of PREFACTOR.md one has the finite product
$$\gamma_d(\beta)=\prod_{1\le i<j\le d}(1-e^{-\beta(j-i)/d})=\prod_{h=1}^{d-1}(1-e^{-\beta h/d})^{d-h}.$$
Thus the leading constant in (1) is elementary for every fixed rank.

Take independent homogeneous Poisson coordinate streams of rates $a_i=\alpha_i$ in the first coordinate and $\lambda_i=\bar\alpha_i$ in the second, independently for each colour. The merged orders are the independent iid colour words in the definition of $\gamma$. At first-coordinate time $x$, let $Y_i(x)$ be the ordinate of the point of colour $i$ most recently seen in that coordinate (zero initially). The independent coordinate processes $Y_i$ jump at rates $a_i$ by positive independent exponential increments of parameter $\lambda_i$, by ordinal matching. At a jump of colour $s>1$, the required northwest witness of colour $s-1$ exists exactly when the new ordinate is less than the last ordinate of $s-1$. Positive jump endpoints almost surely never tie another ordinate; and a tie at zero from two unseen colours causes no failure. Therefore passing all ordinal tests is precisely nonexit of $Y$ from the weak Weyl chamber $y_1\ge\cdots\ge y_d$ starting at the origin. The merged jump chain picks component $i$ with probability $a_i$, since their sum is 1. The identity $a_i\lambda_i=c$ is independent of $i$, and $\lambda_1<\cdots<\lambda_d$ if $d>1$.

Write $g_i=y_{i-1}-y_i$ for $i>1$ and $g_1=\infty$. For each permutation $\pi$ of $[d]$ put
$$A_\pi=\operatorname{sgn}(\pi)\prod_{i=1}^d\left(\frac{\lambda_{\pi(i)}}{\lambda_i}\right)^i,\qquad
E_\pi(y)=\exp\left(\sum_i(\lambda_i-\lambda_{\pi(i)})y_i\right),\qquad h(y)=\sum_\pi A_\pi E_\pi(y).$$
With zero value after killing, the transition operator of this jump chain acts on $E_\pi$ by
$$K E_\pi(y)=E_\pi(y)\sum_i\frac{c}{\lambda_{\pi(i)}}\big(1-e^{-\lambda_{\pi(i)}g_i}\big).$$
Indeed the $i$ jump density is $c e^{-\lambda_i z}dz$ on $0<z<g_i$. The terms with 1 reproduce $E_\pi$, for $\sum c/\lambda_{\pi(i)}=1$. At a finite gap $g_i$, swap the images $\pi(i-1),\pi(i)$ to obtain $\pi'$. Then
$$\frac{A_{\pi'}}{\lambda_{\pi'(i)}}=-\frac{A_\pi}{\lambda_{\pi(i)}},\qquad
E_\pi(y)e^{-\lambda_{\pi(i)}g_i}=E_{\pi'}(y)e^{-\lambda_{\pi'(i)}g_i}.$$
The latter identity follows by evaluating the permutation-dependent exponents at equal coordinates $y_i+g_i=y_{i-1}$. All the lost terms cancel pairwise, so $Kh=h$.

On the entire chamber, $|h|\le\sum|A_\pi|$ because $\sum\lambda_i y_i\le\sum\lambda_{\pi(i)} y_i$ by rearrangement. More explicitly the difference in the latter order is
$$\sum_{k<d}(y_k-y_{k+1})\sum_{i\le k}(\lambda_{\pi(i)}-\lambda_i),$$
with nonnegative partial sums, at least one strictly positive for every nonidentity permutation. For the *unconstrained* process the strong law gives $Y_i(x)/x\to a_i/\lambda_i=c/\lambda_i^2$, strictly decreasing in $i$. Therefore on survival each consecutive gap tends to infinity also along jump times; all nonidentity terms disappear and $h\to1$. After killing it stays zero. Bounded convergence in $h(y)=K^N h(y)$ yields exactly the forever-survival probability, without assuming $h$ positive beforehand. Finally $h(0)=\det[\lambda_j^i]_{i,j=1}^d/\prod_i\lambda_i^i=\prod_{i<j}(1-\lambda_i/\lambda_j)$ by the Vandermonde identity. Substituting $\lambda_i/\lambda_j=e^{-\beta(j-i)/d}$ proves the claim.
