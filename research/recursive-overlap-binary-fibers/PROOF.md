# Concavity of homogeneous Bernoulli entropy for fibers of size at most two

Let X=(X₁,…,Xₙ) have independent Bernoulli(p) coordinates. Let F be any map from the binary cube to a finite set, all of whose nonempty fibers have size at most two. Suppose that the all-zero and all-one inputs have singleton fibers (separate output values). Then H(F(X)) is strictly concave on [0,1]. Natural logarithms are used. No additivity is needed for this theorem.

In particular, Neunhäuserer’s recursive-overlap entropy Conjecture 3.1 holds for every step and positive integer weight sequence for which each attained subset sum has at most two representations. Indeed the index of the original recursion equals, up to translation and replacing p by 1−p, the weighted sum of the independent bits with positive weights 1,a₂−a₁,…,aₙ−aₙ₋₁. The two extreme sums have unique representations. Reflection p↦1−p takes the law to a reflection of its output, so in this weighted application the unique maximum is at 1/2. This leaves the general weighted-sum conjecture open. An example with arbitrarily many distinct collisions is the list 1,1,2,4,…,2^{n−2}: the last n−1 entries encode an ordinary binary integer, and adding the first bit results in at most two representations at every output.

**Entropy curvature.** Work on 0<p<1 with q=1−p. It suffices to prove negativity of the curvature for p≤1/2: although an arbitrary F need not itself be reflection-invariant, precomposing it with bitwise complementation preserves the hypotheses. Denote the word probabilities by w=w_x=p^k q^{n−k}, where k is its Hamming weight. Their log score s and negative log second derivative v are
$$s_k=k/p-(n-k)/q,\qquad v_k=k/p^2+(n-k)/q^2.$$
Thus w′=ws, w″=w(s²−v), E s²=E v=n/(pq). Given the output put t_x=w_x/∑_{y:F(y)=F(x)} w_y and ℓ_x=−log t_x. The entropy loss D=H(X)−H(F(X))=∑wℓ has second derivative
$$D''= E[(s^2-v)\ell]-E[\operatorname{Var}(s\mid F)].$$
To see this, differentiate the difference of entropies; the derivatives of the logarithms produce −∑w′²/w+∑_c W_c′²/W_c, with W_c the output masses. These are exactly the negative mean conditional variance. In particular −H(F(X))″=n/(pq)+D″.

Write L=log 2. Decompose this last expression among fibers by **allocating** (1−L)E s²+L E v=n/(pq). Each singleton contributes its mass times (1−L)s²+Lv. On a two-point fiber the contribution per unit mass is
$$G=E_t[(1-L+\ell)s^2]-\operatorname{Var}_t(s)+E_t[v(L-\ell)].$$
The first two terms together are nonnegative: they equal E_t[−log(2t)s²]+(E_t s)². Use −log(2t)≥1−2t; the resulting quadratic is t₁t₂(s₁+s₂)²≥0. It remains to bound E_t[v log(2t)].

**The tilt estimate (n≥5).** A nonsingleton's Hamming weights k≤l are between 1 and n−1. If k=l or p=1/2 its posterior is uniform and the last term is zero. Otherwise set x=q/p≥1 and z=(l−k)log(x)/2. The two posterior masses have odds exp(2z) in favor of k. For each interior k≥1,
$$\frac{v_{k+1}}{v_k}=1+\frac{x^2-1}{k(x^2-1)+n}\le\frac{2x^2+n-2}{x^2+n-1}\le \sqrt{x}.$$
For the last inequality put y=√x. Its rearranged numerator factors as (y−1)(y⁴−y³−y²−y+n−2). At n=5, y=1+b the second factor is (1−b)²+b²+3b³+b⁴; larger n only helps. It follows that v_l/v_k≤exp(z). After reweighting the posterior by v, the odds in favor of k are therefore at least exp(z). The weighted mean of log(2t), whose two values are ±z−log cosh z, is at least z tanh(z/2)−log cosh z, which is nonnegative: tanh is concave on [0,∞), so ∫₀ᶻ tanh s ds≤z tanh(z/2) by Jensen. Thus every two-point G≥0. Both positive-mass singletons give strict negativity of the entropy’s second derivative.

**Small n.** For n=2,3,4 apply the very same tilt estimate to the artificial v′_k=v_k+(5−n)/q²=k/p²+(5−k)/q² on each two-point fiber (the posterior odds are unchanged). Hence E_t[v log(2t)]≥−(5−n)L/q², since 0≤E_t log(2t)≤L. Two-point fibers together have probability at most 1−pⁿ−qⁿ≤1−2^{1−n}. The two forced singletons together contribute exactly
$$(p^{n-2}+q^{n-2})n[(1-L)n+L].$$
Multiplying this by q² gives lower bounds 2−L, 3(3−2L)/4, and (4−3L)/2 for n=2,3,4 respectively (use q≥1/2 and p²+q²≥1/2). These strictly exceed (5−n)L(1−2^{1−n}) in the three cases, as follows just from L<7/10. Other singletons contribute nonnegatively. This proves strict negativity also for n=2,3,4; n=1 gives the binary entropy. Continuity at the endpoints extends strict concavity to the closed interval.

**Independent blocks (direct consequence).** If a weighted sum uniquely determines the tuple of its block sums, then its entropy equals the sum of their entropies. Each block may satisfy the theorem above, may be an injective independent encoding, or may be a binomial sum covered by prior work. Thus global representation multiplicity can exceed two for such direct products, without implying the unrestricted case.
