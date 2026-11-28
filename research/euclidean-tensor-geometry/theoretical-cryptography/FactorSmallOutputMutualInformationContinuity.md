# Fixed-prior mutual-information continuity with a small output alphabet

Let a finite positive input prior \(p\) be prescribed on \(s\) symbols and let the output alphabet have size \(b\ge2\). No output marginal is prescribed unless explicitly stated. For joint distributions \(P_{XY},Q_{XZ}\) with this common \(X\)-marginal and \(Y,Z\) valued on the same \(b\) labels, define
\[
M_{p,b}(\delta)=\max_{T(P_{XY},Q_{XZ})\le\delta}
              |I(X;Y)_P-I(X;Z)_Q|,
\qquad T(P,Q)=\tfrac12\|P-Q\|_1 .
\]
The [earlier prescribed-input result](FactorPrescribedBlockMarginalContinuity.md) reaches the full input-prior Fano curve when the output alphabet is large enough. Here the output alphabet is the bottleneck; the thresholds below are exact even when \(b<s\). Ordinary discrete conditional-entropy continuity and fixed-prior Fano bounds are prior results ([Alhejji and Smith](https://arxiv.org/abs/1909.00787), [Sakai](https://arxiv.org/abs/1801.02876)). The contribution is the small-output fixed-prior modulus and its equality thresholds, not a new Fano inequality.

For a deterministic map \(f\) from input symbols to output labels, let \(p_f\) denote its vector of group masses, allowing zero masses. Put
\[
\begin{aligned}
C&=\max_f H(p_f),\\
\delta_{\rm F}&=(b-1)\max_f \min_j (p_f)_j,\\
\delta_{\rm C}&=1-\max_{f:\ H(p_f)=C}\max_j(p_f)_j,\\
F_b(\delta)&=h\big(\min(\delta,1-1/b)\big)
                         +\min(\delta,1-1/b)\log(b-1),
\end{aligned}                                                  \tag{1}
\]
where \(h\) is binary entropy and all logarithms are natural.

**Theorem.** We have \(0\le\delta_{\rm F}\le\delta_{\rm C}\le1-1/b\) and
\[
\begin{array}{rcll}
M_{p,b}(\delta)&=&F_b(\delta)&0\le\delta\le\delta_{\rm F},\\
M_{p,b}(\delta)&<&\min\{F_b(\delta),C\}
                      &\delta_{\rm F}<\delta<\delta_{\rm C},\\
M_{p,b}(\delta)&=&C&\delta\ge\delta_{\rm C}.
\end{array}                                                  \tag{2}
\]
In particular, for **binary output**, set
\[
         \beta=\max_{A\subseteq[s]}\min(p(A),1-p(A)).
\]
Then \(\delta_{\rm F}=\delta_{\rm C}=\beta\), so the entire modulus is
\[
                M_{p,2}(\delta)=h(\min(\delta,\beta)).       \tag{3}
\]
This may be strictly smaller than the dimension-only binary bound even though the prior has at least three positive symbols. In a ternary example \(p=(.7,.1,.1,.1)\), the thresholds are \(1/5\) and \(3/10\): the gap region is real, and (2) does not claim the full modulus there.

## 1. Fano equality forces the more informative channel to be deterministic

Orient the pair so \(I(X;Y)\ge I(X;Z)\). Under the common prior, couple \(Y,Z\) maximally conditional on each \(X\), giving
\[
                   e=\mathbb P(Y\ne Z)=T(P_{XY},Q_{XZ}).
\]
The chain rule gives
\[
 I(X;Y)-I(X;Z)=I(X;Y|Z)-I(X;Z|Y)
                  \le H(Y|Z)\le h(e)+e\log(b-1).
\]
Together with \(H(Y|Z)\le\log b\) this yields \(M_{p,b}\le F_b\).
If \(0<\delta<1-1/b\) and the upper bound is attained, the capped Fano function is strictly increasing up to \(\delta\), so \(e=\delta\). Equality in the steps forces
\[
 I(X;Z|Y)=0,\quad H(Y|X,Z)=0,\quad
 P(Y=i\mid Z=j)=
    \begin{cases}
    1-\delta&i=j,\\
    \delta/(b-1)&i\ne j
    \end{cases}                                               \tag{4}
\]
for every \(j\) of positive probability. To obtain the last equality, split off the error indicator; it must be independent of \(Z\), and conditional on error the remaining \(b-1\) labels must be uniform.

Choose any \(j\) of positive \(Z\)-probability. By (4) each \(i\) has positive joint probability with \(Z=j\). Since \(X-Y-Z\) is a Markov chain, for each \(x\) a possible output \(i\) under \(P(Y|X=x)\) remains possible after also conditioning on \(Z=j\). The condition \(H(Y|X,Z)=0\) therefore allows only one output per \(x\). So \(Y=f(X)\) and its masses satisfy
\((p_f)_i\ge\delta/(b-1)\) by (4).

Conversely, when all the masses of some deterministic partition exceed or equal \(a=\delta/(b-1)\), take \(P(Z=i)=((p_f)_i-a)/(1-\delta-a)\) and use (4) to generate \(Y\) from \(Z\). Given \(Y=i\), choose \(X\) with the prescribed prior conditioned on its \(i\)-th cell. This fixes the given prior and \(Y=f(X)\), and the pair's actual total variation equals the error probability because its first channel is deterministic. Moreover \(X-Y-Z\) and \(H(Y|X,Z)=0\) hold. The sharp value is therefore exactly \(F_b(\delta)\) for \(\delta\le\delta_{\rm F}\) in this range, and is strictly below it otherwise by compactness. At \(\delta=1-1/b\), equality means \(\log b\) is attained, which requires an exactly balanced deterministic partition by the next section; it is then attained by the balanced partition and an independent output.

## 2. Exact first saturation of the information cap

Every stochastic channel is a finite mixture of deterministic channels, indexed by a random variable \(S\) independent of \(X\). Thus
\[
 I(X;Y)\le I(X;Y,S)=\mathbb E_S H(p_{f_S})\le C.
\]
When \(b\le s\), every maximizing deterministic map must use all \(b\) labels, since splitting off a positive input of a group of size greater than one strictly increases entropy if an unused label is available. If a stochastic channel attains \(C\), all its deterministic mixture components must attain \(C\) and the equality \(I(X;S|Y)=0\) holds. At each output label \(i\), all the component posteriors on \(X\) must agree. Their supports are the nonempty \(i\)-th cells of the deterministic partitions; since the input prior is strictly positive, equal posteriors force these cells to be identical. Thus a \(C\)-maximizing channel is itself deterministic.

If the difference equals \(C\), the weaker channel must be independent: \(Q_{XZ}=p\otimes r\). For deterministic \(Y=f(X)\), the distance to this channel is \(1-\sum_i (p_f)_i r_i\). Its minimum over \(r\) is \(1-\max_i(p_f)_i\), attained by taking a constant \(Z\) at a largest cell. This proves (1)'s saturation threshold for \(b\le s\).

When \(b>s\), \(C=H(p)\), and any maximizing channel must have disjoint output supports \(A_x\) for distinct \(x\), since \(H(X|Y)=0\). Its distance to any independent \(r\) is at least \(\sum_x p_x(1-r(A_x))\ge1-\max_x p_x\). A one-to-one deterministic map attains that threshold. This again equals \(\delta_{\rm C}\) in (1). This argument includes a prior concentrated on one input, for which \(C=\delta_{\rm C}=0\).

Together with the strict increase of \(F_b\) below \(1-1/b\), the two attainment statements force \(\delta_{\rm F}\le\delta_{\rm C}\): otherwise any interior interval where both caps attain would make a strictly increasing function constant. The bound \(\delta_{\rm C}\le1-1/b\) follows from the largest cell mass being at least \(1/b\). Compactness gives the strict pair of bounds in the intervening range. For \(b=2\), entropy of a deterministic partition is \(h(p(A))\), uniquely ranked by the smaller cell mass, giving (3).

An exact lower bound in the remaining range is the maximal fixed-prior Hamming-equivocation value of a deterministic partition \(p_f\). For a deterministic first channel the distance to any second channel is its Hamming error, and \(I(X;Z)\ge I(f(X);Z)\), with equality by making \(Z\) depend only on \(f(X)\). Therefore Sakai's fixed-prior formula supplies the exact value for a prescribed deterministic anchor. As an example, when \(s=b+1\), this deterministic-anchor lower bound is maximized by merging the two smallest input masses and leaving the other inputs separate. Among partitions using \(b\) labels it is the least majorized mass vector: replacing one member of a merged pair by an unused smaller mass is a two-coordinate balancing step. Indeed the transformation \(x+y,z\mapsto z+y,x\) for \(x\ge z\), \(y\ge0\) preserves their sum and does not increase their maximum. A partition using fewer labels can only decrease its Hamming equivocation compared with a refinement padded with zeros: its mass vector majorizes the refined one. The fixed-prior conditional-entropy maximum at a given error budget is a symmetric concave function of the prior, since the entropy objective is concave in the joint law and the distorting error constraint is linear. Hence it is Schur-concave, proving the assertion among deterministic anchors. We do **not** infer that a deterministic anchor is globally optimal inside the gap for arbitrary \(b>2\).

## 3. Binary output with both marginals shared

One can also require \(P_Y=Q_Z\), without prescribing what that common marginal must be. For \(\beta>0\), the exact binary modulus in this smaller class is
\[
 \beta h\left(\frac{d}{2\beta}\right)
 +(1-\beta)h\left(\frac{d}{2(1-\beta)}\right),\qquad
                   d=\min\{\delta,2\beta(1-\beta)\}.          \tag{5}
\]
For \(\beta=0\) it is identically zero.

Write the row probabilities of output one as \(a_x,b_x\), and orient to make \(I(P)-I(Q)\ge0\). Equality of the output means cancels the output entropy terms. For a change of fixed absolute size \(e=|b_x-a_x|\), the row entropy gain is at most \(h(e)\). This follows because \(h(a+e)-h(a)\) is decreasing in \(a\), with its largest value at \(a=0\); if the change is downward, reflect the bits. The total amounts of upward and downward changes are equal, so each has mass \(D/2\), where \(D=T(P,Q)\). Assign any unchanged rows to either change group and let their masses be \(u,1-u\). Jensen bounds the sum by \(u h(D/(2u))+(1-u)h(D/(2(1-u)))\); for \(D>0\) both groups are nonempty. This is attained at each feasible \(D\) by starting at the deterministic partition and taking constant flip probabilities within each group.

For each \(u\), this quantity as a function of \(D\) is maximized under the budget at \(D=\min(\delta,2u(1-u))\): its derivative has the sign of \(2u(1-u)-D\). For fixed feasible \(D\), the expression is concave and symmetric in \(u\) (since \(u h(c/u)\) is concave for \(u\ge c\)), and therefore increases as \(u\) moves toward \(1/2\). The feasible \(D\)-range only expands when the smaller group mass grows. The closest available partition to \(1/2\) has smaller mass \(\beta\), proving (5) including the saturated range. If \(0<\beta<1/2\), the two-marginal modulus is strictly below (3) for \(0<\delta<2\beta(1-\beta)\): below \(\beta\) strictness is Jensen for the two unequal flip probabilities, and from \(\beta\) up to saturation it is strict increase toward \(h(\beta)\). At \(\beta=1/2\) the two formulas coincide. This last theorem does not prescribe either numerical output mean.

The [exact rational companion](verify_factor_small_output_mi_continuity.py) sanity-checks partition thresholds, the reversing and two-marginal couplings, and the majorization assertion; the proofs above, not the sampled inputs, establish the formulas.
