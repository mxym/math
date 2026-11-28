# A quadratic memory lower bound beyond the small Fourier-mass regime

The previous fixed-order many-pass reduction used a positive mixture of single Fourier terms. Its small-total-mass condition required the wrapped first-harmonic parameter to be at most a small constant times \(1/d\). A different binary representation removes this condition on the memory lower bound. It uses clipping and orbit-wise repair of a density, followed by a balanced random subset whose inclusion probabilities are prescribed. The representation is a proof device about restricted classical computations, not a transformation of externally supplied data.

## 1. Model and bound

Fix odd \(q\ge3\), dyadic \(d\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and fixed number of scans \(P\ge1\). Draw \(S\) uniformly on \(R\). Conditional on \(S\), draw \(T\) independent rows
\[
 A\sim U_R,\quad Y=AS/q+E\pmod{\mathbb Z^d},
 \qquad E\sim \bigotimes_{j=1}^d f_b,\quad
 f_b(x)=\sum_h b^{h^2}e^{2\pi i h x}.
\]
The original learner scans exactly the same continuous observation list in exactly the same order at most \(P\) times; it keeps at most \(m\) bits between rows or scans. A row transition may be any measurable function of the state and the whole current row, with arbitrary transient computation and fresh independent randomness. There is no outside storage or free transcript. The final output is a label or a list.

There exist positive constants \(\delta,c,C\) at fixed \(q,P\) such that if \(d b^2\le\delta\) and
\[
       D=\min\{d,(d b^2)^{-1}\},\qquad
       m\le c d^2,\quad T\le e^{cD},
\]
then the probability of exact success (or of containing \(S\) in a list of size at most \(e^{cD}\)) is at most \(C e^{-cD}\). For \(P=1\) use a dummy second pass. In particular if \(b=d^{-\alpha}\) with any fixed \(1/2<\alpha<1\), the lower bound remains quadratic in persistent bits, for a stream of up to \(\exp(c d^{2\alpha-1})\) observations. This is not a bound on unrestricted computation, and for the wider noise range it does not claim the same \(\exp(cd)\) length scale as the earlier narrower-band result. When \(D\) remains bounded the displayed error bound may be uninformative.

The same numerical lower bound also holds in a local-access version, if \(m+C_q(B+1)d(D+\log(d+1))\le c d^2\): in each of the fixed number of scans allow either arbitrary forward skips and adaptive backward requests up to \(B\) positions behind the furthest requested index in the original observation list, or adaptive read-once reordering with at most \(B\) outstanding earlier accepted rows as in [the windowed-access model](https://github.com/mxym/math/blob/ff3a6657c9dbff3e85c6f6140cdb6e6a89bf62a8/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-windowed-access-memory.md). In particular when \(D=d^{2\alpha-1}\) with \(1/2<\alpha<1\), this includes growing buffers of a sufficiently small constant times \(d^{2-2\alpha}\) rows. It is still not arbitrary random access.

By contrast, for the foregoing polynomial \(b\) range, \(T\asymp b^{-2}\) with sufficiently large constant is statistically sufficient with unrestricted access and decision. Thus the result is a lower bound on the specified classical memory and pass model and does not follow just from the number of observations. It does not address actual schemes or supply any recovery algorithm.

A single balanced sign generally cannot give an exact representation without some change of distribution. For any public latent variable independent of the label, if each of its sign probabilities under the uniform label is at least \(1/2-\epsilon\), then the postprocessed law at every fixed label is dominated by \(1/(1/2-\epsilon)\) times the uniform-label mixture. This holds even after acceptance with equal acceptance probability at all labels: condition on the latent row, compare its two possible output sublaws, and divide by the same acceptance probability. On the event that the ring coefficient is a unit, the true continuous row likelihood relative to that mixture attains \(\left(f_b(0)/f_{b^{q^2}}(0)\right)^d\), and values arbitrarily close to it occur on a positive-measure neighborhood. For \(b=\beta/d\) this tends to \(e^{2\beta}\), so exact simulation by such a sign with \(\epsilon=o(1)\) is impossible when \(\beta>\frac12\log 2\). The finite-TV repair below is therefore an essential change in this representation, not just a different way to arrange the original Fourier modes.

## 2. Clip the high-density tail and preserve every grid average

Write \(F(y)=\prod_j f_b(y_j)\), and define the grid-averaged reference density
\[
        g(y)=q^{-d}\sum_{u\in R} F(y-u/q)
             =\prod_j f_{b^{q^2}}(q y_j).
\]
It is invariant under every \(u/q\) shift. The positive ratio \(L=F/g\) has grid average exactly 1 at each \(y\). Define
\[
  C_0(y)=\min(L(y),2),\quad
  a(y)=q^{-d}\sum_{u\in R} C_0(y-u/q),\quad
  \widehat L(y)=C_0(y)+(1-a(y))\frac{2-C_0(y)}{\,2-a(y)\,}.       \tag{1}
\]
Here \(0\le a\le1\), so \(0\le\widehat L\le2\), and \(a\) is grid invariant. The mean of \(\widehat L\) over each grid orbit is
\(a+(1-a)(2-a)/(2-a)=1\). In particular \(g\widehat L\) is a normalized density. The total mass removed by clipping and that added in repair are equal, which gives
\[
 \operatorname{TV}(g\widehat L\,dy, F\,dy)
   \le \int g(y)(L(y)-2)_+\,dy
   \le \Pr_{Y\sim F}(\log L(Y)>\log 2).                         \tag{2}
\]
The bound holds for every shifted row law by translating the observation and using grid invariance.

Under \(Y\sim F\), \(\log L(Y)\) is a sum of \(d\) independent terms
\(\log(f_b(Y_j)/f_{b^{q^2}}(qY_j))\). For small \(b\) these are bounded in absolute value by \(C_q b\) and have mean \(O_q(b^2)\): the scalar ratio is \(1+O(b)\) uniformly, its first-order deviation integrates to zero against the reference, and the mean is a KL divergence. Thus the mean of the sum is at most \((\log 2)/2\) for \(d b^2\le\delta\) with small enough \(\delta\). Hoeffding shows the last probability in (2) is at most \(\exp(-c_q/(d b^2))\). This uses the likelihood tail under the true row, not an absolutely summed Fourier series of a \(d\)-coordinate product.

For the finite approximation below, \(\widehat L\) is uniformly \(O(b)\)-Lipschitz in each coordinate separately. Indeed \(\partial_j\log L=O(b)\) by the scalar Fourier derivatives. Where \(L\le2\), \(|\partial_j L|=O(b)\), so the clipped \(C_0\) has that Lipschitz bound (by absolute continuity along lines). Averaging shifts gives it for \(a\), and the repair function is uniformly Lipschitz on \(0\le C_0\le2,0\le a\le1\), its denominator bounded below by 1.

## 3. Balanced binary labels with a fixed acceptance probability

Here is the representation of the repaired model. For a finite grid-equivariant partition, use \(M\) bins per scalar coordinate with \(q\mid M\); the product boxes are denoted \(B\). For each box and each \(t\in R\) put
\[
       p_t(B)=\frac{1}{2g(B)}
                 \int_B g(y)\widehat L(y-t/q)\,dy .
\]
Thus \(p_t(B)\in[0,1]\) and \(\sum_t p_t(B)=|R|/2\). There is a finite lottery of signs \(F_B:R\to\{-1,+1\}\) such that every sign function in its support has magnitude of mean at most \(1/|R|\) under a uniform argument, and \(\Pr[F_B(t)=+1]=p_t(B)\). For a direct proof lay out half-open intervals of lengths \(p_t(B)\) in a fixed order on \([0,|R|/2)\). For one uniform \(u\in[0,1)\), select precisely those intervals meeting \(u+\mathbb Z\). Each interval has length at most 1, hence is selected with its length as probability, and the number selected is either \(\lfloor|R|/2\rfloor\) or \(\lceil|R|/2\rceil\). The sign is \(+1\) on selected elements. The selection changes only at the endpoints modulo 1, so at most \(|R|+2\) sign functions are needed for a box. This is the elementary random-start construction used in [systematic sampling with unequal probabilities](https://doi.org/10.1080/01621459.1966.10480902).

A binary extractor row consists of independent choices \(a,\tau\) uniform \(R\), box \(B\) of probabilities \(g(B)\), and a sign function \(F_B\) from the above finite lottery for that box. Its binary label at the hidden parameter \(s\) is
\[
                        M(a,\tau,B,F_B;s)=F_B(as+\tau).
\]
**Accept the row precisely for sign \(+1\).** On acceptance emit design \(a\), and a response drawn from \(g\) conditioned on the box \(B-\tau/q\). This continuous draw can be performed using an independent position-specific seed, not included in the label calculation.

The emitted row law after conditioning on acceptance is exactly the boxwise reference interpolation of the shifted \(g\widehat L\). In fact, at fixed \(a,\tau,s\), the mass of being accepted and emitting box \(B'\) is the mass of \(B=B'+\tau/q\) times \(p_{as+\tau}(B)\); by grid-shift invariance it is
\[
                 \frac12\int_{B'} g(z)\widehat L(z-as/q)\,dz .
\]
This expression is independent of \(\tau\). Its sum over \(B'\) is \(1/2\) for every \(a,s\). Thus acceptance probability is exactly \(1/2\) conditional on \(s,a\), and accepted designs are uniform. Independent latent rows produce independent accepted rows conditional on \(s\) when read in order. Dequantizing a box by \(g\) makes the likelihood ratio there its \(g\)-average; its error relative to \(\widehat L\) is \(O(d b/M)\) by the separate Lipschitz bound in §2. Choose \(M\) as the smallest multiple of \(q\) at least \(d^5 e^{10D}\). Since \(d b^2\le\delta\), this error is \(O(e^{-5D})\) and \(\log M=O(D+\log(d+1))\). The law of each accepted row therefore differs in TV from the original physical row by at most
\[
                     e^{-c_q/(d b^2)}+O(e^{-5D}).              \tag{3}
\]
This approximation is uniform in every label and is done before subsequent scans, not independently at each reread.

## 4. Why the binary representation is a good extractor

For a fixed sign \(F_B\), translation orthogonality gives, for a nonnegative density \(h\) on \(R\) relative to uniform,
\[
 \mathbb E_{a,\tau}
   \big|\mathbb E_s h(s) F_B(as+\tau)\big|^2
   =
   |\widehat F_B(0)|^2+
         \sum_{v\ne0}|\widehat F_B(v)|^2
                      \mathbb E_a|\widehat h(\overline a v)|^2.
\]
Here \(X\mapsto X^{-1}\) is the coefficient-dot adjoint for multiplication. For every \(v\ne0\), \(\overline a v\) is uniform on a nonzero ideal whose cardinality is at least \(e^{\alpha_q d}\) at fixed odd \(q\). This holds also when \(q\) is composite, because a nonzero ideal has a simple quotient, and in each odd residue characteristic the common irreducible factor degree of \(X^d+1\) grows proportionally to \(d\). See the algebra in [the fixed-order proof, §4](https://github.com/mxym/math/blob/09dead42499780e321e58b7b995a547af89d2dec/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-constant-pass-memory-lower-bound.md#4-fixed-odd-modulus-a-balanced-sign-with-a-random-translation). Parseval and \(|\widehat F_B(0)|\le1/|R|\) give
\[
              q^{-2d}+ e^{-\alpha_q d}\|h\|_2^2 .
\]
This bound does not depend on the box or which balanced sign the lottery returns, so averaging those public choices preserves it. In particular, Markov gives a binary \(L^2\)-extractor with all three parameters \(r_0=\lfloor c_q d\rfloor\) for sufficiently small \(c_q>0\), with strict exponential slack.

The catalogue of public binary rows has log cardinality \(O_q(d(D+\log(d+1)))\): there are \(M^d\) boxes, \(q^{2d}\) pairs \(a,\tau\), and at most \(q^d+2\) signs at any box. Approximate this finite distribution by duplicating entries under a uniform alphabet of size \(2^n\), \(n=O_q(d(D+\log(d+1)))\), moving at most \(e^{-4d}\) mass by taking the constant sufficiently large. Likewise use a uniform concept set of size \(2^n\) mapped to \(R\) with fibers differing by at most one, so its projected law is \(1+O(e^{-4d})\) pointwise relative to uniform. Under projection the relative \(L^2\) norm increases by at most this relative upper bound's square root, by conditional Jensen. The strict extractor slack thus survives approximation. Any use of finite alphabet padding in the cited proof costs \(O(\log d)\) bits, since \(\log|\mathcal X|=O(d^2)\). We need only existence of these finite encodings for a nonuniform lower-bound argument, not an efficient sampling procedure for the balanced functions.

## 5. Transfer the fixed-pass theorem through rejection

Let the simulated binary learner read a fixed-length list of \(N'=8(T+d)\) latent labeled rows. From independent ideal latent rows the probability that fewer than \(T\) are accepted is \(\exp[-\Omega(T+d)]\) by the binomial Chernoff bound (conditional on any secret, the signs on distinct rows are independent and each accepts with probability \(1/2\)). Couple their retained sequence to the first \(T\) accepted rows of an infinite ideal stream. On every scan, feed the original learner only those first \(T\) accepted rows, skipping rejected positions, and pad with no-op updates at the remaining latent layers. If fewer were available, give any result. This is a genuine program reading exactly the same latent list in the same order at each pass. Besides the original state, it needs only a counter for the accepted prefix, i.e. \(O(\log(T+d))\) bits. At a particular position the output dequantization draw is fixed once, so a repeated pass reproduces the identical accepted continuous row. Average over independent seeds after bounding each nonuniform deterministic program. Fresh private coins can be incorporated in the same way. The simulation is mathematical and arbitrary measurable row transitions cause no discretization-of-the-transition issue.

Apply [Lyu–Tal–Wu–Yang, Theorem 6](https://arxiv.org/pdf/2310.08070v1) to this fixed-order program: with all extractor parameters \(r_0=\Theta(d)\) and fixed number \(P\) of passes, the allowed width is \(2^{\Theta_{q,P}(d^2)}\) and length is \(\exp(\Theta_{q,P}(d))\). The exceptional event is \(\exp(-\Theta_{q,P}(d))\), and in each reached final state on the good event the pointwise concept posterior is at most \(2^{r_0/2}\) times its uniform prior, by selecting the auxiliary \(\ell\) a sufficiently small multiple of \(r_0\). A guessed projected label then has posterior at most \((1+O(e^{-4d}))q^{-d}2^{r_0/2}\), also exponentially small, multiplied by the list size for a list. These consequences apply to the finite uniform dyadic model in §4. Its total discrepancy from the ideal finite binary experiment is \(O((N'+1)e^{-4d})\) by coupling the prior and initial latent rows only once. There is no independence assumption across repeated passes.

Since \(\log T\le cD\le cd\), both the width and length hypotheses hold with small \(c\). The total error to the original experiment from (3) is at most \(T(e^{-c_q/(d b^2)}+O(e^{-5D}))\); because \(D\le(d b^2)^{-1}\) this is \(O(e^{-cD})\) after reducing \(c\) again. Add the accepted-count error and the finite theorem error to get the claimed result. For a single pass, add an idle scan.

For the local-access version only accepted rows enter the logical index sequence. The sequential binary simulator moves through latent positions, skipping rejects, until it reaches the next needed unread **accepted** index. Store the requisite last \(B+1\) or outstanding accepted symbols and their latent positions, to reconstruct each accepted response using its invariant positional seed. Rejected rows need no storage after their test. The fixed-order simulation proof of [the windowed-access theorem, §3](https://github.com/mxym/math/blob/ff3a6657c9dbff3e85c6f6140cdb6e6a89bf62a8/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-windowed-access-memory.md#3-one-sequential-sweep-simulates-one-local-access-scan) applies verbatim to the accepted indices while the binary reader takes no-op steps through rejections. It costs \(O_q((B+1)d(D+\log(d+1)))\) bits because that is the symbol length and \(\log(N'+1)=O(D+\log(d+1))\). With the stated stricter width budget, the same extractor proof therefore applies. This buffering variant does not supersede the sharper linear-bit symbols of the old \(b\le1/(100d)\) regime.

## 6. Statistical comparison and prior

For \(b=d^{-\alpha}\), \(1/2<\alpha<1\), take \(k b^2\to t>\log q\). The true log likelihood across \(k\) rows has mean \(t d+o(d)\) and variance \(O(d)\) from the scalar first-harmonic expansion. A false-pair overlap after averaging the design is \(\exp(O(kd b^4))=1+o(1)\): its scalar first term is \(2b^2\cos\) of the phase difference, and for each row the sum of these cosines has mean zero and variance \(O(d)\), by the nonzero ideal and the absence of signed two-term units from its annihilator. To control the exponential remainder uniformly, use the fixed-base independent bounded-block property of that ideal, which gives log moment \(O(d b^4)\) for the row's \(b^2\)-scaled cosine sum. The grid mean is zero and the log scalar remainder is \(O(b^4)\), as in [the posterior overlap proof](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md). Thus the total wrong weight normalized by \(q^d\) has bounded expected value under the true law, whereas the true weight exceeds \(e^{c d}\) with probability tending to one. This gives the unrestricted statistical comparison without a computational procedure.

The [prior one-pass bound](https://github.com/mxym/math/blob/50efe594/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-one-pass-memory-lower-bound.md) maintains horizon \(\exp(\Theta(d))\) but gives the memory scale \(d^2/(1+db)\) in its wider range. The present bound gives quadratic memory for a shorter but stretched-exponential horizon when \(b=d^{-\alpha}\) and also for any fixed number of same-order passes. The earlier positive single-Fourier-mixture proof covers quadratic memory with a horizon exponential in \(d\) when \(b\le1/(100d)\). The new contribution is the bounded likelihood repair and balanced binary-label representation, not an extension of the cited branching-program theorem itself. No range here yields a general classical polynomial-time lower bound or concerns a deployed system.
