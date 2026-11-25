# The limiting constant for equal pairwise gcds (Erdős 535)

Fix an integer \(r\ge3\). Let \(g_r(X)\) be the maximum size of an \(A\subseteq[1,X]\cap\mathbb N\) not containing \(r\) distinct numbers with identical pairwise greatest common divisors. Let \(M_r(k)\) be the maximum size of an \(r\)-sunflower-free family of \(k\)-element sets with arbitrary finite ground set, and write \(b_r=\sup_{k\ge1}M_r(k)^{1/k}\). Then, using natural logarithms,
\[
 \lim_{X\to\infty}\frac{\log g_r(X)\log\log X}{\log X}=\log b_r .
\]
The same limit holds when \(A\) consists only of squarefree numbers. The identity is valid in the extended reals without any additional result. It is finite by OpenAI's [fixed-petal sunflower theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/An-exponential-bound-for-sunflowers-November-24-2026/paper.pdf); see their [scope note for the Lean formalization](https://github.com/openai/math/blob/main/lean/docs/379.md#sunflowers).

This is the limit proposed by Erdős in [his 1964 paper, equation (8), p. 646](https://users.renyi.hu/~p_erdos/1964-10.pdf). His forcing threshold is one larger than our extremal size, with no effect on the limit. The order-of-growth implication from a fixed-petal exponential theorem is already Erdős's; the result here identifies the coefficient as the optimal uniform sunflower base. It does not compute \(b_r\) or improve the available quantitative sunflower theorem.

The prime-power layer encoding also appears in Sunder, Kumrawat and Cheri, *Equal pairwise greatest common divisors and sunflowers* (April 2026; [discussion and source announcement](https://www.erdosproblems.com/forum/thread/535)). The uniform block-product lemma used below is stated for both sunflowers and cosunflowers in [Luo, Yang and Zhu, arXiv:2609.07268v1, Lemma 2.1](https://arxiv.org/html/2609.07268v1#S2). Their limiting exponent concerns harmonic LCM avoidance, a different problem.

## Upper bound

It suffices to prove the upper bound when \(b_r<\infty\). Let \(L=\log X\), \(y=L/(\log L)^2\), and \(\sigma=(\log y)^{-2}\). The number of \(y\)-smooth positive integers up to \(X\) is at most
\[
 X^\sigma\prod_{p\le y}(1-p^{-\sigma})^{-1}
       =\exp(o(L/\log L)).
\]
For this estimate, take logarithms. The first summand is \(L\sigma=o(L/\log L)\); each logarithmic local factor is \(O(\log\log y)\) using \(p\ge2\), and \(\pi(y)=O(y/\log y)\).

Group \(A\) by its exact \(y\)-smooth part \(s\). For a member \(a\) of a class, encode \(a/s\) as the set of pairs \((p,i)\) for \(p>y\) and \(1\le i\le v_p(a/s)\). This is injective inside the class, and intersection of two sets gives exactly the encoding of the gcd of their rough parts. Thus an \(r\)-sunflower within this class would give \(r\) original integers with identical pairwise gcds. Each set has size at most \(K=\lfloor L/\log y\rfloor\). Pad each to size \(K\) with elements private to that set, which preserves intersections between distinct sets. The class has at most \(M_r(K)\le b_r^K\) elements. Multiplying by the number of classes, and using \(\log y\sim\log L\), gives the upper limit.

## Lower bound, with squarefree integers

Take any \(r\)-sunflower-free \(k\)-uniform family \(\mathcal F\) on \(m\) points. Take \(t\) disjoint copies of its ground set, and all unions obtained by choosing a member in every copy. If \(r\) distinct unions had the same pairwise intersections, then inside any block their projections would be either all equal or all distinct. Indeed if two projections agree, their intersection is a full \(k\)-set, so every other projection must be that same set. The all-distinct alternative would be an \(r\)-sunflower in that block, excluded by construction. Hence all projections would be equal in every block, contradicting distinct unions.

Assign the first \(mt\) primes to the ground-set points and encode a union by the product of its primes. These numbers are distinct and squarefree and gcd again encodes intersection. There are \(|\mathcal F|^t\) of them, each at most \((C mt\log(2mt))^{kt}\), by the usual upper bound for the \(j\)-th prime. For fixed \(\varepsilon\in(0,1)\), take \(t=\lfloor (1-\varepsilon)L/(k\log L)\rfloor\). For fixed \(k,m\), the logarithm of the displayed maximum is \(((1-\varepsilon)+o(1))L<L\). Thus the lower limit is at least \((1-\varepsilon)\log|\mathcal F|/k\). First let \(\varepsilon\) go to zero, then take the supremum over \(\mathcal F,k\). This also gives divergence to \(+\infty\) if \(b_r=+\infty\).
