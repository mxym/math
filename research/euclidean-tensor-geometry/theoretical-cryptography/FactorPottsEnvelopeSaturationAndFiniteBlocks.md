# Equality and finite-block rounding for the q-ary entropy envelopes

Fix \(q\ge3\), \(L=\log q\), uniform distribution \(u\), and the symmetric channel
\(T_\lambda p=\lambda p+(1-\lambda)u\), with
\(-1/(q-1)\le\lambda<1,\ \lambda\ne0\). Logarithms are natural.
For \(d=L-H(X|U)\), this note gives exact fixed-marginal saturation of **both** one-letter conditional-entropy envelopes. For \(n\) memoryless channel uses it gives exact equality in the tensorized lower bound, including the loss from the integer allocation of coordinates inside its affine segment.

We use as inputs [Gu–Polyanskiy, Theorem 4, Proposition 18 and Corollary 25](https://people.lids.mit.edu/yp/homepage/data/nlsi_potts.pdf) for the lower scalar optimizer and tensorized envelope, and the [preceding envelope calculation](FactorPottsEntropyEnvelopes.md) for the exact chord, strictness, and reverse polygon. The lower profile, tensorized inequality, and asymptotic tightness are not new here. The endpoint \(\lambda=-1/(q-1)\) is the zero-diagonal coloring channel. The completely random and identity channels, omitted from the nondegenerate statements, respectively give constant and unchanged output entropy.

## 1. Profiles and equalities for fixed input marginal

Let \(p_t^{(j)}=(1-t)u+t e_j\), \(0\le t\le1\), and
\(D_q(t)=D(p_t^{(j)}\Vert u)\) (independent of \(j\)). In the lower conditional-entropy profile, use the entropy deficit \(d\) and write
\[
s(D_q(t))=D_q(\lambda t),\qquad
        H(Y|U)\ge L-\widehat s(d).
\]
For negative arguments of \(D_q\) the same probability formula defines it. The concave envelope is \(\widehat s(d)=\eta d\) on \([0,d_*]\), and equals \(s(d)\) thereafter; \(d_*=D_q(t_*)\). Unless \(\lambda=-1/(q-1)\), \(d_*\in(0,L)\) is a unique positive tangency, and \(s\) is strictly concave on \([d_*,L]\). At the coloring endpoint set \(d_*=L,\ t_*=1\), and the entire envelope is the chord. In either case the profile lies strictly below that chord at each interior point of the chord segment.

**Lower equality at a prescribed marginal \(\pi=P_X\).** If \(d=0\), equality requires \(\pi=u\) and one posterior suffices. If \(d>0\), define
\[
(\beta,t)=
\begin{cases}
(d/d_*,\,t_*) & 0<d<d_*,\\
(1,\,D_q^{-1}(d)) & d_*\le d\le L.
\end{cases}
\]
Then the lower envelope is attained at \((d,\pi)\) if and only if
\[
             \min_i\pi_i\ \ge\ \frac{1-\beta t}{q}.        \tag{1}
\]
When attainable, the smallest support of an auxiliary \(U\) has size
\[
 \#\{i:\pi_i>(1-\beta t)/q\}+\mathbf 1_{\{\beta<1\}}.       \tag{2}
\]
In particular for the uniform marginal this is \(q+1\) in the open linear segment and \(q\) at and beyond its right endpoint.

To see this, every positive-probability posterior must attain the one-letter minimum and be at a contact point of \(\widehat s\) and \(s\). Equality in concavity requires all its deficits to lie on the same supporting face. On the linear segment this leaves only deficits \(0,d_*\); the latter have total mass \(\beta\). At the right endpoint their average forces deficit exactly \(d_*\), and beyond it strict concavity forces every deficit to be \(d\). Gu–Polyanskiy's uniqueness says that a nonuniform posterior in either regime must be \(p_t^{(j)}\) for one symbol \(j\). Thus \(\pi=(1-\beta t)u+\beta t w\) for a probability vector \(w\). This gives (1) and fixes the required total probability \(\beta w_i\) of the \(i\)-th heavy-symbol posterior; one state for each positive weight, plus a uniform state if needed, proves (2). Conversely these posteriors attain equality.

**Upper equality at a prescribed marginal.** Write \(h=H(X|U)\). On any upper polygon interval \([\log k,\log(k+1)]\), \(1\le k<q\), set
\[
\alpha=\frac{h-\log k}{\log(k+1)-\log k},\qquad
b=\frac{1-\alpha}{k}+\frac{\alpha}{k+1}.
\]
Except for the coloring channel on \(0<h<\log 2\), the upper envelope is attained if and only if
\[
                         \max_i\pi_i\le b.                 \tag{3}
\]
In the exception, let \(p_{\max}=\max_i\pi_i\) and let \(H_b\) be the binary entropy. The sharp condition becomes
\[
              h\le H_b\!\left(\max(\tfrac12,p_{\max})\right). \tag{4}
\]
The criteria agree at \(h=0,\log2\), and (3) covers all polygon vertices including \(h=L\).

For (3), strict chord slopes and the strict pointwise arc below the chord force uniform posterior laws on \(k\)- and \((k+1)\)-subsets with total weights \(1-\alpha,\alpha\) respectively. At an interval endpoint only that vertex type is needed. These mixtures cannot exceed \(b\) in any coordinate. Conversely choose a \(k\)-subset inside a \((k+1)\)-subset and mix the two uniform laws with the fixed weights. The resulting vector is \(b\) on \(k\) coordinates, \(\alpha/(k+1)\) on one more, and zero elsewhere. The convex hull of its permutations is exactly the capped simplex \(\{\pi_i\le b,\ \sum\pi_i=1,\ \pi_i\ge0\}\). Indeed, at a vertex at most one coordinate can be between 0 and \(b\), since otherwise a two-coordinate transfer is feasible both ways, and the resulting vertices are precisely these permutations (with the evident degeneracies at \(\alpha=0,1\)). This constructs attaining mixtures for every eligible \(\pi\).

For (4), the first arc is affine for the coloring channel and its pointwise maximizers are exactly the laws of support at most two there. This follows also from the explicit binary-face output: if the two masses are \(p,1-p\), its entropy is \(\log(q-1)+H_b(p)/(q-1)\). For any support-at-most-two posterior, its entropy is at most \(F(p_j)\) for any fixed index \(j\), where \(F(t)=\log2\) for \(t\le1/2\), and \(F(t)=H_b(t)\) for \(t\ge1/2\). This function is concave, so taking \(j\) at a largest marginal coordinate gives \(h\le F(p_{\max})\). If \(p_{\max}\le1/2\), decompose \(\pi\) into uniform pairs using the preceding capped-simplex argument. If \(1/2<p_{\max}<1\), mix the laws \(p_{\max}e_j+(1-p_{\max})e_i\) over \(i\ne j\), with weights \(\pi_i/(1-p_{\max})\). The case \(p_{\max}=1\) admits only \(h=0\). These realize \(F(p_{\max})\); mixing with a point-mass decomposition of the same \(\pi\) realizes every smaller \(h\). The exception is genuine: \(\pi=(3/4,1/4,0,\ldots,0)\) at \(h=H_b(3/4)\) attains the coloring upper line with one posterior, while the cap in (3) would be less than \(3/4\) because \(H_b(3/4)>\frac12\log2\).

## 2. Exact equality at finite block length

For arbitrary \(X^n\), let
\[
c=\frac{D(P_{X^n}\Vert u^{\otimes n})}{n}=L-\frac{H(X^n)}n,
\qquad
D(P_{Y^n}\Vert u^{\otimes n})\le n\widehat s(c).             \tag{5}
\]
**For \(0\le c\le d_*\), equality holds only at \(c=j d_*/n\) for an integer \(0\le j\le n\).** The equality inputs are exactly the product laws with \(j\) coordinates independently of the form \(p_{t_*}^{(i)}\), and the other coordinates uniform. For \(d_*<c\le L\), exactly the independent products of single-site extremizers \(p_{D_q^{-1}(c)}^{(i)}\) attain equality. Coordinates and heavy symbols may be chosen separately. Off the grid in the affine segment the best finite-block value is strictly below (5), even allowing arbitrary correlations; compactness makes this a strict gap at each fixed \(n,c\).

For the proof, use the chain rule and the fact that \(Y_i\) and \(Y_{<i}\) are conditionally independent given \(X_{<i}\):
\[
\begin{aligned}
D(P_{Y^n}\Vert u^{\otimes n})
 &\le \sum_i \mathbb E_{X_{<i}}
        D(P_{Y_i|X_{<i}}\Vert u)\\
 &\le \sum_i \mathbb E_{X_{<i}}
        \widehat s(D(P_{X_i|X_{<i}}\Vert u))
 \le n\widehat s(c).
\end{aligned}                                              \tag{6}
\]
The difference in the first inequality is \(\sum_i I(Y_i;X_{<i}\mid Y_{<i})\). If it vanishes, the law \(P_{Y_i|X_{<i}=x}\) equals the law given any \(Y_{<i}=y\) that is reachable from \(x\) of positive probability. Any two input prefixes have a common reachable output prefix: for the coloring channel choose each output symbol different from the two corresponding inputs, which is possible since \(q\ge3\); in other nondegenerate cases all output symbols have positive probability. Hence \(P_{Y_i|X_{<i}=x}\) is the same for every such \(x\). Invertibility of \(T_\lambda\) on distributions when \(\lambda\ne0\) makes \(P_{X_i|X_{<i}=x}\) constant too. This proves independence. The pointwise equality and Jensen contact arguments of §1, now applied to \(n\) equally weighted coordinate deficits, give exactly the asserted grid and equality inputs. The inputs displayed there attain (5) by direct product additivity.

There is a quantitative form of independence rigidity. Let
\[
\mu=\min_{a,b}\sum_y T_\lambda(y|a)T_\lambda(y|b)>0 .
\]
In fact \(\mu=(1-\lambda^2)/q\) since \(T_\lambda(\cdot\mid a)=u+\lambda(e_a-u)\). For \(n\ge2\), the slack in (5) is at least
\[
\frac{\lambda^2\mu^{n-1}}{8(n-1)}
 \left\|P_{X^n}-\bigotimes_{i=1}^n P_{X_i}\right\|_1^2.      \tag{7}
\]
To prove it, fix \(i\) and write \(r_x=P_{Y_i|X_{<i}=x}\). At fixed noisy prefix \(z\), Pinsker gives \(\frac12\sum_x P(x|z)\|r_x-r_z\|_1^2\) as a lower bound for the conditional mutual-information contribution. This bounds below one eighth of the conditional mean over two independent posterior prefixes of \(\|r_x-r_{x'}\|_1^2\), by the triangle inequality squared. When averaged in \(z\), the weight of a pair is at least \(P(x)P(x')\sum_z P(z|x)P(z|x')\), since the exact weight additionally divides by \(P(z)\le1\). Zero-mass \(z\) contributes nothing. The sum is at least \(\mu^{i-1}\). Finally, output law differences are \(\lambda\) times input law differences, and Jensen replaces the second prefix by the marginal of \(X_i\). Thus the \(i\)-th slack is at least \(\lambda^2\mu^{i-1}/8\) times the mean squared \(L^1\) distance of \(P_{X_i|X_{<i}}\) to \(P_{X_i}\). Telescoping joint prefixes against products bounds the joint distance by the sum of mean coordinate distances; Cauchy–Schwarz yields (7).

## 3. The finite loss among product inputs

At non-endpoint noise, fix \(c\) in any compact subinterval of \((0,d_*)\). For all sufficiently large \(n\), the exact largest output deficit over independent (not necessarily identically distributed) inputs at average input deficit \(c\) is
\[
 \max_{k\in\{\lfloor nc/d_*\rfloor,\lceil nc/d_*\rceil\}}
                       k\,s(nc/k).                         \tag{8}
\]
The \(k\) chosen coordinates all have common deficit \(nc/k\) and are single-site optima. Relative to the envelope, the product loss **per coordinate** is
\[
 \frac{[-s''(d_*)]d_*^3}{2c}\,
 \frac{\operatorname{dist}(nc/d_*,\mathbb Z)^2}{n^2}
 \left(1+O(n^{-1})\right),                                 \tag{9}
\]
uniformly on the stated compact subinterval. At an exact grid point this is zero. The remainder is relative away from exact zero, not an error hiding the oscillation. Since these are actual product inputs, (9) is also an upper bound on the finite-block gap when arbitrary correlations are allowed, but not a matching lower bound for that larger class.

Here is the argument. For product inputs maximization reduces to \(\sum s(d_i)\) with \(\sum d_i=nc\). Set \(g(x)=\eta x-s(x)\); its only zeros are \(0,d_*\); \(g'(0)=\eta-\lambda^2>0\), \(g'(d_*)=0\) and \(g''(d_*)=-s''(d_*)>0\). Choosing \(k\) nearest \(nc/d_*\) and \(d_i=nc/k\) on \(k\) coordinates gives total gap \(O(1/n)\) by Taylor's formula. An optimum therefore has every coordinate in arbitrarily small neighborhoods of \(0\) or \(d_*\), uniformly in \(c\), because the loss is nonnegative and bounded away from zero outside them. There is at least one coordinate near \(d_*\). Choose the neighborhoods so that \(g'\) at small coordinates is strictly greater than its supremum in the neighborhood of \(d_*\). Transferring a small positive amount from any positive small coordinate to a near-\(d_*\) one would reduce the loss; hence all small coordinates are zero. Strict convexity of \(g\) near \(d_*\) makes all remaining coordinates equal. The ratio \(s(x)/x\) strictly increases up to \(d_*\) and strictly decreases afterwards, so only the two enclosing integers \(k\) need be considered. This proves (8). Taylor expansion around \(d_*\), with \(nc/k-d_*=d_*(nc/d_*-k)/k\), proves (9). For either enclosing integer the coefficient of its squared distance has the same uniform relative error; taking their minimum gives (9) also arbitrarily near the grid.

For the coloring endpoint, let \(j=\lfloor nc/L\rfloor\), \(R=nc-jL\). The exact largest product output deficit is instead \(j\,s(L)+s(R)\), for every \(n\): strict convexity of \(s\) on \([0,L]\) moves all but at most one coordinate to the endpoints of that box at any maximum. This gives the exact product loss per coordinate \((\eta R-s(R))/n\). No off-grid exact correlated optimum is asserted.

The [exact rational companion](verify_factor_potts_envelope_saturation.py) checks the capped-simplex vertices, fixed-prior constructions and prefix-overlap identities; these computations illustrate the formulas, while the proofs above establish their full ranges.
