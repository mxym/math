# Expected rank loss and two uniform-square statistics

## Guarantees

Fix a prime power $q$, integers $1\le r\le k$, and a uniform index $i$ in a finite list of $n$ linear maps $E_i:\mathbb F_q^k\to\mathbb F_q^r$. Labels may repeat matrices. For each $r$-dimensional $U$ let $D_i(U)=\dim\ker(E_i|_U)$. A strong lossless rank extractor with budget $L$ has $\sum_i D_i(U)\le L$ for every $U$; a weak one counts nonzero deficiencies only.

**A.** The labelled maps and parameter choices in the pinned weak construction already give $\mathbb E_iD_i(U)<1145/1344<7/8$ for $q=2$, and $<25/[24(q-1)]\le25/48$ for $q\ge3$. One can take $L$ to be the floor of the indicated constant times $n$. Their sizes are respectively at most $k2^{6r+o(r)}$ and $kq^{2r+o(r)}$, for fixed $q$ with the little-oh independent of $k$.

**B.** Let $A$ be a uniform $r\times r$ matrix over the same field, $\mu=\mathbb E\dim\ker A$ and $p=\Pr[A\text{ injective}]=\prod_{j=1}^r(1-q^{-j})$ (expose its columns in order). For each rational $0<\delta<1$ there is an explicit family for which, simultaneously for every $r$-space $U$,
$$
|\mathbb E_iD_i(U)-\mu|\le\delta,\qquad |\Pr_i[D_i(U)=0]-p|\le\delta.
$$
For fixed $q,\delta$ the size is at most $kq^{2mr+o_{q,\delta}(r)}$ with $m=\min(r,t)$, $t=O(1+\sqrt{\log_q(1/\delta)})$ given explicitly below. This controls two statistics, not total variation of the entire nullity distribution. No claim of optimal seed length, all-distinct matrices, strongly local evaluation, or polynomial size in unrestricted $k,r$.

## 1. Linear evaluation and its moments

Write $G_s(d)={d\brack s}_q$ for the number of $s$-spaces in a $d$-space, including $G_0(d)=1$ and $G_s(d)=0$ when $s>d$. Counting ordered bases gives
$$
G_s(d)=\prod_{j=0}^{s-1}(q^d-q^j)/|\mathrm{GL}_s(q)|,\qquad
|\mathrm{GL}_s(q)|=q^{\binom{s}{2}}\prod_{j=1}^s(q^j-1).
$$
Take $1\le m\le r$. Identify the input with $K=\mathbb F_{q^k}$ via a basis, fix a surjective coordinate projection $\pi:K\to\mathbb F_q^r$, and put $E_a(x)=\pi(\sum_{j=0}^{m-1}a_jx^{q^j})$ for $a\in K^m$. Frobenius makes this linear. At an independent set of $s\le m$ points the coefficient-to-evaluations map is surjective onto $K^s$ before projection. Otherwise its first $s$ Moore columns are dependent, giving a nonzero linearized polynomial of degree at most $q^{s-1}$ that vanishes on a space of size $q^s$. Composing with $\pi$ in every coordinate remains surjective.

An $\varepsilon$-biased indexed sample in $K^m$ means that every nontrivial additive character has mean of modulus at most $\varepsilon$. For an $s$-space $W$, its annihilation indicator is the average of all $q^{rs}$ characters of the joint evaluation at its basis. Every nontrivial character has a nontrivial pullback by surjectivity. Thus $|\Pr[E_iW=0]-q^{-rs}|\le(1-q^{-rs})\varepsilon$. Counting $s$-spaces inside each kernel gives, for every fixed $U$ and $1\le s\le m$,
$$
|\mathbb E_iG_s(D_i(U))-G_s(r)q^{-rs}|\le G_s(r)\varepsilon. \tag{1}
$$
For a uniform square matrix these moments are exactly $G_s(r)q^{-rs}$. There is no union bound over $U$ and no independence assumption on the killed subspaces.

For the linear-in-$k$ enumeration bound we use two standard constructive inputs: Shoup's deterministic irreducible-polynomial algorithm at fixed characteristic constructs the polynomial basis of $K$; the Jalan–Moshkovitz small-bias theorem for the additive group of $mk$ field coordinates gives $O_q(mk\,\varepsilon^{-(2+o(1))})$ labelled samples in time polynomial in $mk,1/\varepsilon$. Evaluate on each of $k$ basis vectors to obtain an $r\times k$ matrix. Uniformly repeat the entire list until $n\ge1/\varepsilon$ if necessary; this increases its size by fewer than $\lceil1/\varepsilon\rceil$ labels if repetition was needed, without changing its law. Fixed-field enumeration time is polynomial in $k,n$ and the bit length of any rational accuracy input.

**Elementary alternative at larger size.** Fill the $rk$ entries directly with the prime-field version of the Alon–Goldreich–Håstad–Peralta power sampler (see SOURCES). For $q=p_0^e$, put $b=erk$, let $J=\mathbb F_{p_0^h}$ with minimal $h\ge1$ such that $|J|\ge b/\varepsilon$. Sample $x,y\in J$ independently uniformly, and take the $b$ prime-field coordinates $\ell(yx^j)$, $0\le j<b$, for any nonzero $\mathbb F_{p_0}$-linear functional $\ell$; group them in $e$-tuples. Each nontrivial additive character has exponent $\ell(yP(x))$ for a nonzero polynomial of degree at most $b-1$. Averaging over $y$ vanishes except at its roots, so bias is at most $(b-1)/|J|$. For unrestricted matrix entries evaluation at any independent vectors is onto by basis extension; hence (1) holds. One may find an irreducible of degree $h$ by enumeration and trial division in time polynomial in $|J|$. This recovers the statistical guarantees without either advanced construction, at size $O_q((rk/\varepsilon)^2)$, not the linear-in-$k$ bound.

## 2. Interpolation of dimension and injectivity

Put $c_s=\prod_{j=1}^{s-1}(1-q^j)$ for $s\ge1$, $b_s=(-1)^s q^{s(s-1)/2}$ for $s\ge0$, and
$$
P_u(d)=\sum_{s=1}^u c_sG_s(d),\qquad H_u(d)=\sum_{s=0}^u b_sG_s(d).
$$
For $u\ge d$ these equal $d$ and $1_{\{d=0\}}$. To see why, use the polynomial identity
$$
z^d=\sum_{s=0}^dG_s(d)\prod_{j=0}^{s-1}(z-q^j).
$$
For its induction, multiplication of the product by $z$ gives the next product plus $q^s$ times the old, while $G_s(d+1)=q^sG_s(d)+G_{s-1}(d)$ (by the counting formula, with out-of-range terms zero). Differentiate at $z=1$ for the dimension identity, or evaluate at $z=0$ for injectivity, taking the constant monomial to be 1.

As a polynomial in $x=q^d$, $P_u$ has degree at most $u$ and interpolates $\log_q{x}$ at $1,q,\ldots,q^u$. For integer $d>u$ the nodal product at $q^d$ is positive; the derivative of order $u+1$ throughout is $(-1)^u u!/(x^{u+1}\ln q)$. The interpolation remainder has that sign, by Rolle's theorem applied $u+1$ times after adding the extra evaluation node. Thus even $P_u$ bounds $d$ below, odd $P_u$ above. Also by interpolation uniqueness,
$$H_u(d)=\prod_{j=1}^u(q^j-q^d)/(q^j-1).$$
At $d>u$ its sign is $(-1)^u$: even $H_u$ bounds the injectivity indicator above, odd $H_u$ below. These statements include $u=0$ and are pointwise on all integer dimensions.

## 3. Accuracy and degree

Let $t$ be the smallest positive odd integer with both
$$w_D(t)=\frac1{q^{\binom t2}(q^t-1)},\qquad
w_0(t)=\frac1{\prod_{j=1}^t(q^j-1)}$$
at most $\delta/2$. Each denominator is at least $q^{t(t-1)/2}$ since $q^j-1\ge q^{j-1}$, giving the claimed square-root cutoff. Set
$$m=\min(r,t),\quad B=\sum_{s=1}^m q^{\binom{s}{2}}G_s(r),\quad \varepsilon=\delta/(2B).$$
Because $|c_s|\le|b_s|=q^{\binom s2}$, each polynomial expectation through degree $m$ differs from its own uniform-square expectation by at most $B\varepsilon=\delta/2$, via (1). If $r\le t$, both degree-$r$ polynomials are exact on all deficiencies. Otherwise use the lower/upper sandwiches $[P_{t-1},P_t]$ and $[H_t,H_{t-1}]$. For a uniform matrix their expected widths are at most $w_D(t)$ and $w_0(t)$, respectively: their one-term differences in expectation have magnitudes $|c_t|G_t(r)q^{-rt}$ and $|b_t|G_t(r)q^{-rt}$, and $G_t(r)q^{-rt}\le 1/|\mathrm{GL}_t(q)|$. Comparing either sampled endpoint with the matching uniform endpoint, and then the latter with the uniform statistic, costs at most $\delta/2+\delta/2$. This proves B.

Moreover $q^{\binom s2}G_s(r)\le q^{rs}/\prod_{j=1}^s(q^j-1)\le q^{rs}$, so $1/\varepsilon\le2m q^{rm}/\delta$. For varying $\delta$ the unambiguous size bound is $O_q(mk(2B/\delta)^{2+o(1)})$ as $2B/\delta\to\infty$; for fixed accuracy and field it yields the stated asymptotic.

## 4. Baseline constants with no retuning

For $q\ge3$ use $m=1$, $v=q^r$, $\varepsilon=1/(24v)$. Since an independent basis supplies $d$ distinct lines, $d\le G_1(d)$. Thus the mean loss is at most $(v-1)(v^{-1}+\varepsilon)/(q-1)<25/[24(q-1)]$.

For $q=2$, let $v=2^r$, $m=\min(3,r)$ and $\varepsilon=1/(24v^3)$. The majorant $P_3=G_1-G_2+3G_3$ applies even when $r<3$, because the absent subspace terms then vanish. For $s=1,2,3$, respectively, $G_s(r)$ is $(v-1)$, $(v-1)(v-2)/6$, and $(v-1)(v-2)(v-4)/168$. Therefore
$$
\mathbb E_{\rm unif}P_3=143/168-5/(8v)-1/(12v^2)-1/(7v^3).
$$
The error is at most $(G_1(r)+G_2(r)+3G_3(r))/(24v^3)$. The factor before $1/24$ is
$$1/56+1/(24v)+3/(4v^2)-17/(21v^3).$$
On adding, all three nonconstant coefficients are negative; the constant term is $143/168+1/1344=1145/1344$. §1 gives A's two size bounds. Taking zero bias shows $\mu<143/168$ in the binary case and $\mu<1/(q-1)$ otherwise.

## 5. Filtering, and what optimality does not mean

Suppose the unfiltered upper bound on each mean loss is $a<1$. Every globally rank-deficient map contributes at least 1 for every $U$. If $b$ such labels are removed, at least $(1-a)n$ remain, and for any $U$ the remaining sum is at most $an-b\le a(n-b)$. The strong upper bound therefore survives, as does any lower bound on success (no successful seeds are removed). The rank-deficient-label deletion itself is already noted by Guo–Raj–Shangguan–Zhang, §2; this shows what survives for the normalized bounds. For B one may use internal accuracy $\min(\delta,1/16)$ so that $\mu+1/16<1$. The opposite sides of the two-sided approximations are **not** asserted after filtering: at $k=r$ every surjective seed has zero loss. Another one-sided option is to extend each deficient row space to dimension $r$ and use a basis of that space as rows of its replacement matrix. Its kernel only shrinks and the label count is unchanged.

For context, let $g=k-r$ and $\nu$ be the mean dimension of intersection of a fixed $U$ with a uniformly random $g$-subspace of the $k$-space. This is the exact smallest possible worst-$U$ mean loss when family size is unrestricted: any kernel contains a $g$-subspace and hence averaging over uniform $U$ gives at least $\nu$, by invariance under basis changes; a uniform $g$-space as kernel attains equality for each $U$. A uniform unrestricted $r\times k$ matrix restricts to a uniform square matrix on $U$, while conditioned on full row rank its kernel is uniform of dimension $g$. Consequently
$$
0\le\mu-\nu\le r\Big(1-\prod_{j=0}^{r-1}(1-q^{j-k})\Big)\le r q^{r-k}/(q-1).
$$
For the last inequality sum $q^{-k}$ over the $(q^r-1)/(q-1)$ possible left-kernel lines. This explains closeness to the true minimax benchmark when the displayed error is small; not an all-parameter near-minimax claim or a size lower bound.
