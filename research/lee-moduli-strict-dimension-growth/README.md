# The sharp Schatten constant for a sum of right moduli grows with dimension

Fix $m\ge2$ complex matrices and a Schatten exponent $1<p<2$. Write $c_p(m,n)$ for the best constant in

$$
\left\|\sum_{i=1}^{m} A_i\right\|_p \le c_p(m,n)\left\|\sum_{i=1}^{m}|A_i|\right\|_p,\qquad A_i\in M_n(\mathbb C),\quad |A|=(A^*A)^{1/2}.
$$

The [proof](PROOF.md) shows **strict growth at every step**: $c_p(m,n+1)>c_p(m,n)$ for all $n\ge1$. Every fixed-dimension maximum exists, but no finite dimension realizes the supremum over all dimensions. In particular, for each fixed $p$, some pair of $3\times3$ matrices beats every rank-at-most-one pair, in any dimension. The pair can depend on $p$. For $m$ matrices the corresponding size is $m+1$.

**What was known.** [Qiu, Question 5.1](https://arxiv.org/html/2608.17565v2#S5), asks for the exact dimension-free coefficient; the paragraph after it reports numerical evidence at $p=6/5$ and suggests possible nonattainment. The [15 November 2026 candidate preprint](https://github.com/ipitchford/schatten-sum-of-moduli-constants/blob/v0.1.0-candidate/manuscript.tex) already implies strict growth when $n+1\le m$ and certifies rank gaps for pairs at nine exponents. Its [open-problems section](https://github.com/ipitchford/schatten-sum-of-moduli-constants/blob/v0.1.0-candidate/manuscript.tex#L1083-L1103) asks whether the constants stabilize, and whether a rank gap holds for every $n>m$ throughout $1<p<2$. The additional adjacent steps established here are **$n\ge m$**; they answer those two structural questions.

**What remains open.** The proof computes neither the dimension-free constant nor the fixed-size values for $n>m$, gives no quantitative rate of growth, and makes no assertion about extremizers on an infinite-dimensional space. It does not claim the first counterexample to the Tang–Zhang formula or the first higher-rank example. At $p=1$ the constant equals one; at $p=2$ it stabilizes once $n\ge m$, so those endpoints are excluded.

**How the proof works.** At a fixed-size maximizer the sum must be injective on the joint input support: separating a small part of each output would otherwise improve it, even after compressing the outputs back to their original dimension. With one extra input coordinate, a rank-one perturbation at a singular summand gives a numerator gain linear in the tilt but only quadratic cost in the first derivative of the denominator. A fixed-sum decomposition of the moduli ensures that some maximizing tuple has such a singular summand.

- [Self-contained analytic argument](PROOF.md)
- [Prior work and search scope](PRIOR.md)
- [Independent internal review, including a direct perturbation argument](REVIEW.md)

AI-assisted research draft. The proof received a separate internal AI-assisted mathematical audit, not external peer review or proof-assistant verification. No worldwide priority claim is made.
