# When random measurements have a narrower entropy range than mutually unbiased measurements

Research draft. See the [overview](README.md) for the finite comparison and the [review](REVIEW.md) for checks and limitations.

## Question, answer, and proof map

Imagine choosing one of several measuring devices at random to measure a pure quantum state. Each device has a probability distribution for its outcomes. Average the *entropies* of these distributions, and ask: how much can this average change as we vary the input state? The order of these operations matters. We do not average the probabilities before computing entropy.

A natural design uses mutually unbiased bases (MUBs). In that design, a state perfectly predictable by one device has completely uniform outcomes on every other device. Puchała, Rudnicki, Chabuda, Paraniak and Życzkowski conjectured in 2015 that a complete family of such bases has the smallest possible upper endpoint of the average entropy. They also suggested that it has the narrowest interval of attainable entropies. We compare the *sharp* endpoints, the actual maximum and minimum over inputs, not any separately derived formula bounding them.

The same predictability property that motivates the proposed design supplies a counterexample mechanism: a basis vector gives a complete MUB an average entropy within a vanishing distance of the largest conceivable entropy. In contrast, sufficiently many randomly chosen bases keep the average entropy close to the same, distinctly smaller, value for **every** input. We make this comparison in a specified finite dimension and asymptotically. The dimension is explicit; the competing matrices are proved to exist, not exhibited entry by entry.

The proof has three steps. First compute the center shared by every design and test a complete MUB on a single basis vector. Next upgrade a known tail estimate for one random measurement of one fixed state to a uniform estimate for many independent measurements of all states. Finally compare the resulting intervals, keeping explicit constants for one finite example.

## 1. Two deterministic facts

A pure state is a unit vector x in complex d-dimensional space, with vectors differing by a common scalar phase identified. For an ordered orthonormal basis B with basis matrix U (columns are the measured vectors), put p_i(x,B)=|(U* x)_i|². For a tuple of L such bases write

    H(p) = −Σᵢ pᵢ ln pᵢ,         F(x) = L⁻¹ Σⱼ H(p(x,Bⱼ)),
    m(B) = minₓ F(x),            M(B) = maxₓ F(x),       W(B) = M(B)−m(B).

Use 0 ln 0=0. All logarithms are natural, and all bases have equal weight. Other log bases rescale both sides by the same positive factor. Continuity and compactness give true extrema. We work only with pure states: the maximally mixed state would have measurement entropy ln d in every basis.

Write h_d=Σ_{k=1}^d 1/k and μ_d=h_d−1. For each deterministic tuple the mean of F over Haar-uniform pure states is μ_d. Indeed the squared coordinates of a complex Haar unit vector are Dirichlet(1,…,1), as follows by normalizing independent standard complex Gaussians, whose squared moduli are independent mean-one exponentials. In particular one coordinate has Beta(1,d−1) density. Hence E[p₁^s]=Γ(d)Γ(1+s)/Γ(d+s) for s>−1. Differentiating at 1, or differentiating (d−1)!/[(s+1)⋯(s+d−1)], gives −d E[p₁ ln p₁]=Σ_{k=2}^d 1/k. This calculation applies to each basis by unitary invariance. In particular

    m(B) ≤ μ_d ≤ M(B).                                                (1)

For any complete MUB tuple U, L=d+1, and any pair of vectors in different bases has squared overlap 1/d. A vector of its first basis therefore has entropy 0 in that basis and ln d in each of the other d. Thus

    M(U)−μ_d ≥ a_d := ln d − h_d + 1 − (ln d)/(d+1),
    W(U) ≥ a_d.                                                      (2)

Here a_d→1−γ>0, where γ is Euler's constant. No classification of complete MUBs or determination of their actual optimizing states is used. Complete families exist in every prime-power dimension including powers of two by [Wootters–Fields](https://doi.org/10.1016/0003-4916(89)90322-9); we assume no existence elsewhere.

## 2. Independent bases uniformly approximate the common center

Fix d≥3 and L≥1. Choose L independent Haar unitary matrices; for each fixed unit vector x the random vectors Uⱼ* x are independent and each has the law of a Haar unit vector. Write Xⱼ=H(p(x,Bⱼ))−μ_d. The one-basis input is [Singh–Zhang–Pati, Theorem 1, Eq. (10)](https://arxiv.org/pdf/1509.08939#page=3). Their relative entropy of coherence *on a pure state* is exactly the Shannon entropy of its squared coordinates. Their formula uses natural logs, centers at h_d−1, and gives for u>0

    P(|Xⱼ|>u) ≤ 2 exp[−d u²/{36π³ ln(2) (ln d)²}]
              ≤ 2 exp(−u²/K),   K=1000(ln d)²/d.                     (3)

The numerical weakening follows from π<22/7 and ln 2<7/10. The argument below also admits a purely elementary qualitative substitute for (3), in the [elementary asymptotic proof](ELEMENTARY.md); a [separate elementary proof](FINITE.md) treats the very same finite dimension.

For one real Xⱼ, write exp(Xⱼ²/(2K)) as 1 plus the integral of the derivative of exp(s/(2K)) from 0 to Xⱼ². By (3) and Tonelli its expectation is at most

    1 + ∫₀^∞ (1/(2K)) exp(s/(2K)) 2exp(−s/K) ds = 3.

By Cauchy–Schwarz, |Σ Xⱼ/L|>t implies Σ Xⱼ²>L t². Markov's inequality and independence *between the L bases*, not between coordinates, now give

    P(|F(x)−μ_d|>t) ≤ 3^L exp[−L t²/(2K)].                           (4)

For uniformity over x, use only a coarse Lipschitz estimate. The function f(r)=−r² ln(r²), set to zero at zero, has |f′(r)|≤2 on [0,1]: on its positive-slope portion the maximum is 4e^(−3/2)<2 and on its negative-slope portion the maximum magnitude is 2. The componentwise reverse triangle inequality followed by Cauchy–Schwarz gives

    |H(p(x,B))−H(p(y,B))| ≤ 2 Σᵢ ||(U* x)ᵢ|−|(U* y)ᵢ|| ≤ 2√d ||x−y||₂.

The same constant works for F by averaging. Choose δ=t/(2√d). A maximal δ-separated subset of the unit sphere is a δ-net: any uncovered point could be added. The ambient space is real dimension 2d. Disjoint open balls of radius δ/2 around the net points are contained in the ball of radius 1+δ/2, so their number is at most (1+2/δ)^(2d). If every net point is within t of the target value, the Lipschitz estimate puts every state within 2t. A union bound in (4) therefore proves

    P(supₓ |F(x)−μ_d|>2t)
    ≤ (1+4√d/t)^(2d) 3^L exp[−dL t²/{2000(ln d)²}].                 (5)

No independence between different test states is needed. No net over the space of bases is taken.

For L=d+1 and t=(ln d)²/√d, the positive terms in the logarithm of (5) are O(d ln d); its subtracted term is (d+1)(ln d)²/2000. Thus the right side vanishes and 2t→0. In particular with probability tending to one the entire interval [m(B),M(B)] lies within 2t of μ_d. The common-center bound (1) now sandwiches inf_B M(B) and sup_B m(B) between μ_d and μ_d+o(1), or μ_d−o(1) and μ_d, respectively. Also inf_B W(B)→0. These are additive estimates in nats; no rate optimality or characterization of finite-dimensional optimizing tuples is claimed.

## 3. A specified finite prime-power dimension

Take d=2⁴⁰, L=d+1, t=1/16. Then ln d<28, the factor 1+4√d/t=1+2²⁶<2²⁷, and

    d t²/{2000(ln d)²} > 2⁴⁰/(256·2000·28²) > 2000.

Consequently the logarithm of the right side of (5) is less than 54d ln 2+(d+1)ln 3−2000(d+1)<0. A tuple B therefore exists with M(B)≤μ_d+1/8 and W(B)≤1/4.

For the opposite comparison, g_d=ln d−h_d+1 increases with d because ln(k/(k−1))>1/k for k≥2, by integrating 1/x from k−1 to k. For d≥4, g_d≥ln 4−13/12. The expansion ln 2=2[1/3+(1/3)³/3+⋯] gives ln 2>56/81; ln 2<7/10 follows from the first four terms of exp(7/10)>2. For the stated d,

    a_d ≥ ln 4−13/12 − (ln d)/(d+1)
        > 97/324 − 28/(d+1) > 1/4.                                   (6)

Equations (2) and (6) give M(U)>μ_d+1/4 and W(U)>1/4 for **every** complete MUB family U, so the same choice B strictly beats every such U in both comparisons. The gap between upper endpoints is greater than 1/8 nat. As d→∞ along prime powers, (2) and (5) likewise show that all sufficiently large such d admit strict counterexamples on both comparisons. This is a probabilistic existence result in the ordinary finite-dimensional model, not an experimentally specified measurement protocol.

The source conjecture pertains to endpoints; a smaller width need not imply a larger lower endpoint than a complete MUB in this same dimension, and we make no such assertion here. Width is not Haar variance either. Nothing here contradicts a variance minimization statement, nor refutes an inequality providing a nonsharp analytic upper bound.

## Attribution and boundaries

The [published original](https://chaos.if.uj.edu.pl/~karol/pdf/PRCPZ15.pdf), p. 032109-1 and p. 032109-10 (Conjecture 1), proposes the range and extremal-endpoint statements. In the numerical comparison it distinguishes sharp extrema from the paper's analytic inequalities; our statements concern the former. The original abstract emphasizes properties of its upper bound, which is not what is disproved here.

Random bases, state nets, entropy concentration, and the mean μ_d are established tools. [Hayden–Leung–Shor–Winter, Eq. (66) and Appendix B](https://arxiv.org/pdf/quant-ph/0307104#page=15) already obtain uniform one-sided average-entropy bounds for random measurements using this strategy, with a two-sided concentration input for a single measurement. [Adamczak–Latała–Puchała–Życzkowski, §V](https://arxiv.org/pdf/1412.7065#page=10) establish further one-sided uncertainty results for random bases. [Ballester–Wehner](https://arxiv.org/abs/quant-ph/0606244) already compare unbiased and random choices for uncertainty and locking; we do not present that general idea as new. The finite comparison above requires *upper* control around the exact center, and the width uses two-sided control. A finite public literature search including current indexed material did not identify a paper making this precise complete-MUB extremal comparison from those inputs. This is not a certification of novelty. The result is a short consequence of the known concentration machinery, not a new concentration principle. The argument received separate AI-assisted internal review, not external peer review.
