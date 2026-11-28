# Constant-pass memory lower bounds for broad wrapped-Gaussian ring learning

## 1. Models and statement

Fix an integer modulus \(q\), and let \(d\) tend to infinity through powers of two. Set \(R=(\mathbb Z/q)[X]/(X^d+1)\); elements are identified with their \(d\) coefficients. Choose \(S\) uniformly in \(R\). Conditional on \(S\), observe independent rows
\[
 (A,Y),\qquad A\sim U_R,\qquad Y=AS/q+E\pmod{\mathbb Z^d},
 \qquad E\sim \prod_{j=1}^d f_b,\quad
 f_b(z)=\sum_{n\in\mathbb Z} b^{n^2}e^{2\pi i n z}.
\tag{1}
\]
Here \(0<b\le 1/(100d)\), so \(f_b\) is a circle heat density (wrapped Gaussian). The coefficientwise map \(AS/q\) is independent of the integer representatives. Haar is the reference measure on the real torus. All \(T\) rows are generated once: on each of \(P\) passes the learner reads precisely the same list in the same order. Between rows or passes it retains at most \(m\) bits. Row transitions can be arbitrary measurable nonuniform maps of the current full row, current state and independent coins, with no restriction on ephemeral time or numerical precision. There is no other persistent storage or output channel. The final state produces a guess for \(S\).

**Theorem.** For any fixed \(P\ge2\), uniformly in the stated range of \(b\), there are positive constants \(c,C\), independent of \(d,b\), such that for all sufficiently large \(d\):
* For every fixed **odd** \(q\ge3\), if \(m\le c d^2\) and \(T\le \exp(c d)\), then the probability of a correct guess is at most \(C\exp(-c d)\).
* For \(q=2\), put \(D=\min\{d,\sqrt{d\log(1/b)}\}\). If \(m\le c D^2\) and \(T\le\exp(cD)\), the probability is at most \(C\exp(-cD)\). In particular, at \(b=\beta/d\) for a fixed \(0<\beta\le1/100\), this is a \(d\log d\)-bit lower bound for streams up to length \(\exp(c\sqrt{d\log d})\).

The same assertions hold for a one-pass learner by ignoring a second pass. The constants can depend on \(P\) and, in the first assertion, on \(q\). The proof gives exponentially small success even when the final state supplies a list of size \(\exp(c d)\), with a possibly smaller \(c\). This is a computational restriction on retained state, separate from the number of rows statistically sufficient without a state or running-time bound: Section 6 bounds the latter by \(O_q(b^{-2})\) for vanishing error, and this is \(O_q(d^2)\) at \(b=\beta/d\). The theorem is not an unrestricted time lower bound, nor does it cover random-access or arbitrary-order reads.

## 2. Binary learning theorem and simulation conventions

We use the extractor theorem of [Lyu, Tal, Wu and Yang, FOCS 2023, arXiv:2310.08070v1, Definition 1 and Theorem 6](https://arxiv.org/pdf/2310.08070v1), for deterministic binary labels. Its fixed-pass consequence used here is the following. If a finite row space \(\mathcal A\) and concept space \(\mathcal X\) are uniform, and every probability density \(h\) relative to \(U_{\mathcal X}\) with \(\|h\|_2\le 2^r\) has
\[
 \Pr_{\mathcal A}\bigl(\bigl|\mathbb E_{\mathcal X}[h(x)M(a,x)]\bigr|\ge2^{-r}\bigr)\le2^{-r},
 \qquad M:\mathcal A\times\mathcal X\longrightarrow\{-1,1\},
\tag{2}
\]
then for fixed \(P\) there is a \(c_P>0\) with this property: for \(r\) large, a \(P\)-pass learner of width at most \(2^{c_P r^2}\) reading \(T\le2^{c_P r}\) iid rows and their deterministic labels has an exceptional event of probability at most \(2^{-c_P r}\), outside which the conditional density at any reached final state is at most \(2^{r/2}\) relative to \(U_{\mathcal X}\). To get this formulation, take \(k_{\rm ext}=\ell_{\rm ext}=r_{\rm ext}=r\) in Theorem 6 and take its \(\ell\) to be a sufficiently small positive multiple of \(r\) depending only on \(P\); its final \(L^\infty\) bound has relative factor \(2^{C'_P\ell+1}\) for a constant \(C'_P\) depending only on \(P\). All width and length requirements can then hold with \(c_P\) decreased. Norms in (2) are under the uniform probability measure.

Here is a precise convention for invoking that theorem on our simulations, including the equal-power-of-two alphabet sizes used in its display notation. Let \(\mathcal S\) be the actual uniform secret set of size \(N\), and suppose we have a finite rational distribution of row modes independent of \(S\), and other *finite* uniform public row randomness. Approximate all row probabilities by counts out of \(2^n\), with \(2^n\ge N\), using arbitrarily large \(n\). Each of the \(2^n\) rows is an individual label, and repeated rows present no problem. If \(N\) is a power of two, one can project a binary concept space of size \(2^n\) exactly uniformly onto \(\mathcal S\). Otherwise choose the fibers as equal as possible. In the second case their induced secret law \(\mu\) can be made arbitrarily close to uniform in relative density and total variation. Relative density of the projected \(h\) with respect to uniform on \(\mathcal S\) has \(L^2\) norm at most \((1+\varepsilon)^{1/2}\|h\|_2\) if \(\mu/U_{\mathcal S}\le1+\varepsilon\): this follows by conditional Jensen and one factor of the change of measure. Thus an extractor proved with small strict exponential slack under uniform S continues to hold. Under the flatness conclusion the probability of guessing a single projected value at a final state is at most \(2^{r/2}(1+\varepsilon)/N\), and a list of size \(L\) has at most \(L\) times this probability. We may choose \(n\) after the parameters are fixed, and take \(n\to\infty\); there is no hidden bound on row-alphabet size in the claimed state model. In particular, cardinalities \(q^d\) for odd \(q\) do not need to be powers of two.

Countably many modes may first be reduced to finite many, moving arbitrarily small total probability to a dummy mode. The errors for finite approximation of a row law add over the \(T\) independent rows (and the one prior), not across repeated passes of already generated rows. To postprocess a row into a continuous observation, fix in advance an independent uniform draw for each *position* in the original list; use the exact same draw on every return to that position. Conditional on the full table of these independent draws (and the original learner's independent coins), the simulation is a deterministic nonuniform branching program on the finite binary rows. The width is unchanged; it substitutes a fixed transition for each input row and sign at a given layer. The tables are used only to prove a bound for that class of deterministic programs and are not extra data retained by the original learner. On averaging over the tables the generated stream has the desired independent rows conditional on \(S\). Standard Borel torus distributions admit such a uniform-draw realization, or one can use an independent finite table of torus samples for each possible row/sign at each position. This avoids an assumption of independence of a later pass from the first.

## 3. The positive Fourier representation

Let \(p_b(y)=\prod_{j=1}^d f_b(y_j)\) and
\[
 g(y)=\prod_{j=1}^d f_{b^{q^2}}(q y_j).
\]
Averaging \(p_b(y-t/q)\) over the full grid \(t\in R\) retains exactly the Fourier terms with frequencies divisible by \(q\), giving \(g\). For every \(a,s\),
\[
 p_b(y-as/q)=g(y)+
 \sum_{\substack{u\in\mathbb Z^d\\w=u\bmod q\ne0}}
 b^{\|u\|^2}\cos\bigl(2\pi u\cdot y-2\pi w\cdot as/q\bigr).
\tag{3}
\]
All signed frequencies are included: taking real parts does not introduce a factor of two. The elementary bounds \(\sum_{k\in\mathbb Z} b^{k^2}\le1+3b\) and \(f_{b^{q^2}}\ge1-3 b^{q^2}\) give
\[
 \sum_{u\not\equiv0(q)}b^{\|u\|^2}\le e^{3db}-1 <1/16,\qquad
 \inf_y g(y)\ge1-3db^{q^2}>1/2
\tag{4}
\]
in the stated band, for every \(q\ge2\). Thus a mode can be sampled independently of the secret, and its conditional output density can be \(g\) plus one cosine of amplitude \(1/2\) multiplied by a deterministic sign. Such densities are nonnegative and have integral one (all the modes have \(u\ne0\)). Remaining probability goes to the dummy mode of density \(g\). The sign and its row space are built next.

For both constructions, for coefficient characters \(\chi_w(t)=e^{2\pi i w\cdot t/q}\), the adjoint identity \(\langle w,a t\rangle=\langle\bar a\,w,t\rangle\) holds, with \(\bar a(X)=a(X^{-1})\). This follows first for the signed cyclic shift \(a=X\), then by linearity. Thus \(\bar a\,w\), for uniform \(a\), is uniformly distributed on the ideal \(wR\). Fourier coefficients and Parseval below are for normalized uniform probability.

## 4. Fixed odd modulus: a balanced sign with a random translation

For each \(w\ne0\) in \(R\), let \(r_w\) be the order of \(\chi_w\), so \(3\le r_w\le q\) and \(r_w\) is odd. Each character-value fiber, indexed by \(j\in\mathbb Z/r_w\), has \(N/r_w\) elements, \(N=q^d\). Choose a sign \(F_w:R\to\{-1,1\}\) so that its sum on this fiber is the closest admissible sum of \(N/r_w\) signs to \((N/r_w)\cos(2\pi j/r_w)\). The approximation in the sum is at most one, including the endpoints. It follows that
\[
 |\widehat F_w(0)|\le q/N,\qquad
 \bigl|\widehat F_w(w)-1/2\bigr|\le q/N.
\tag{5}
\]
The second reference coefficient is \(1/2\) because \(r_w\ge3\) and the \(-1\) and \(+1\) Fourier modes are distinct. In particular \(H_w=|\widehat F_w(w)|\ge1/4\) for all \(w\ne0\) once \(d\) is large.

For mode \(u\) use independent uniform \(a,\tau\in R\) and binary label \(M=F_w(as+\tau)\). Define \(\phi_w=\arg \widehat F_w(w)\). The continuous density conditional on this binary row is
\[
 g(y)+\tfrac12 M\cos(2\pi u\cdot y+2\pi w\cdot\tau/q+\phi_w).
\]
After averaging \(\tau\), the contribution beyond \(g\) is exactly \(\frac12 H_w\cos(2\pi u\cdot y-2\pi w\cdot as/q)\): changing variables \(t=as+\tau\) gives the conjugate Fourier coefficient times \(e^{-2\pi i w\cdot as/q}\). Therefore mode \(u\) has mass \(2 b^{\|u\|^2}/H_w\); (4) guarantees total mass less than \(1/2\). Use any fixed \(F_{w_0}\) and an independent uniform translate for the dummy label, ignoring that label during output generation. This construction **exactly** gives (1) before the optional finite approximations of Section 2. It is a proof device about constraints on finite states, and provides no method for recovering the label from actual observations.

For the extractor bound, let \(h\ge0\) with \(\mathbb E h=1\). Orthogonality in the auxiliary translation \(\tau\) gives the identity
\[
 \mathbb E_{a,\tau}\left|\mathbb E_s h(s)F_w(as+\tau)\right|^2
 =|\widehat F_w(0)|^2+\sum_{v\ne0}|\widehat F_w(v)|^2\,\mathbb E_a |\widehat h(\bar a\,v)|^2.
\tag{6}
\]
For a nonzero ideal \(I\subset R\), some simple module quotient of \(I\) is \(R/\mathfrak m\) for a maximal ideal \(\mathfrak m\): take a maximal proper submodule and use the cyclicity of a nonzero element of the simple quotient. For each odd prime \(p\mid q\), the reduction of \(X^d+1\) over \(\mathbb F_p\) has simple roots of exact order \(2d\), hence each residue field above \(p\) has size \(p^{\operatorname{ord}_{2d}(p)}\). For fixed \(p\), \(\operatorname{ord}_{2d}(p)\) is at least a positive constant times \(d\). For example take \(v_2(p^2-1)=c_p\); for powers \(2^j\), \(j\ge1\), successive squaring gives \(v_2(p^{2^j}-1)=c_p+j-1\). The unit group modulo \(2d\) has power-of-two order, so the claim follows. Consequently \(\min_{v\ne0}|vR|\ge\exp(\alpha_q d)\) for some \(\alpha_q>0\).

The summands in (6) have \(\mathbb E_a|\widehat h(\bar a v)|^2\le\exp(-\alpha_qd)\|h\|_2^2\), and \(\sum_v|\widehat F_w(v)|^2=1\). In particular the extractor bound is uniform over the mode, with mean square at most
\[
 (q/N)^2+e^{-\alpha_qd}\|h\|_2^2.
\tag{7}
\]
Use (7) and Markov with \(r=\lfloor c_q d\rfloor\) for a sufficiently small positive \(c_q\), with slack for the finite row and secret-law approximations of Section 2. This gives (2), including on the dummy mode. Applying the binary theorem and its projected-secret bound proves the odd-modulus case. It was essential to average the square over the **public** \(\tau\); merely rounding a function of an odd-order one-dimensional character into a sign need not make its zero mode exponentially small.

## 5. Binary ramified case: frequency rank versus repetition

For \(q=2\) there is no need to balance a sign. For \(w=u\bmod2\ne0\), use \(M=(-1)^{\langle w,as\rangle}\) and conditional density \(g(y)+\frac12 M\cos(2\pi u\cdot y)\). Take weight \(2b^{\|u\|^2}\) for mode \(u\), and let the dummy density use a fixed full-rank sign, ignored in generation. This gives (3) exactly before discarding rare modes. In the binary ring write \(\varpi=1+X\); \(R=\mathbb F_2[\varpi]/(\varpi^d)\). For \(k\in[0,d]\) the unique ideal of dimension \(k\) is \(I_k=\varpi^{d-k}R\). For a power of two \(p\mid d\), \(I_p\) consists exactly of all repetitions of a block of length \(p\), because
\[
 (1+X)^{d-p}=\frac{1+X^d}{1+X^p}=1+X^p+\cdots+X^{d-p}
\quad\text{in }\mathbb F_2[X].
\tag{8}
\]
Multiplying this polynomial by the arbitrary degree-\(<p\) block gives an injective \(p\)-dimensional space in the ideal.

Let \(D\) be as in the theorem, \(K=\lfloor D/8\rfloor\), and take the smallest power of two \(p\ge K\), so \(p\le d/4\) and \(p<2K\) unless \(p=K\). All modes with \(0<\dim(wR)<K\) have parity in \(I_p\setminus\{0\}\). Put \(u_0=\sum_{j\ {\rm even}}b^{j^2}\), \(u_1=\sum_{j\ {\rm odd}}b^{j^2}\). The total Fourier weight with parity in this latter set equals
\[
 u_0^d\left[(1+(u_1/u_0)^{d/p})^p-1\right].
\tag{9}
\]
Indeed a parity pattern of block weight \(j\) has full weight \(jd/p\), and each integer coordinate is summed independently inside its parity class. Since \(u_0^d\le e^{3db^4}\), \(u_1/u_0\le3b\), and \(p\le D/4\), the expression in (9) is at most \(e^{-c_0D}\) for an absolute \(c_0>0\) and all sufficiently large \(d\), uniformly in \(b\). To see the exponent, write \(B=\log(1/b)\ge\log(100d)\); then \((d/p)(B-\log3)\ge2d B/D\ge2D\). Thus \(p(3b)^{d/p}\le p e^{-2D}\), and for small \(z\ge0\), \((1+z)^p-1\le 2pz\) when \(pz\le1\). The omitted mixture weight is at most twice (9). Move it to the dummy mode. By the section 2 coupling bound whole-list error is \(O(T e^{-c_0D})\).

All retained modes and the dummy have \(\dim(wR)\ge K\). The extractor mean square in this case is at most \(2^{-K}\|h\|_2^2\), again by the adjoint and Parseval, so take \(r=\lfloor K/10\rfloor\) with slack for finite approximations. The binary theorem now gives the asserted rate with \(r\asymp D\); increasing the slack in the length condition pays the discarded mass. In this case the construction's tradeoff in \(D\) is not just the bound of a single low-rank frequency. In the **untruncated** mode law the repetition word in (8) has weight \(d/p\) and ideal dimension exactly \(p\); its mode alone has probability \(2 b^{d/p}\). The uniform density on the annihilator \(I_p^\perp\) has \(L^2\) norm \(2^{p/2}\) and gives bias one for every row in that mode. If \(r\le d/2\) and \(r\ge C_0\sqrt{d\log(1/b)}\) for sufficiently large \(C_0\), choose a power of two \(p\in[r/2,r]\). The probability of that single mode then exceeds \(2^{-r}\). Thus (2) for this particular exact untruncated binary representation cannot have the three equal extractor scales much beyond the square-root scale. This does not give an upper bound on the resources of a learner; a different proof may improve the lower bound.

## 6. Statistical comparison, attribution and limitations

For completeness an unbounded statistical comparison holds for each fixed \(q\ge2\). For two distinct shifts on the scalar \(q\)-grid, their laws have first Fourier coefficient gap at least \(2b\sin(\pi/q)\); hence TV is at least \(b\sin(\pi/q)\). If \(\mathcal H\) is their square-root density overlap, Cauchy--Schwarz gives TV \(\le\sqrt{2(1-\mathcal H)}\); thus \(\mathcal H\le1-c_q b^2\) for a fixed positive \(c_q\le 1\). For a nonzero \(v=s-s'\), \(av\) is uniform on the nonzero ideal \(vR\) and every coordinate projection of that ideal is a nontrivial additive subgroup: one nonzero coordinate implies all by the signed cyclic shift. Thus \(\mathbb E_a\operatorname{wt}(av)\ge d/2\), where weight counts nonzero coordinates. By product structure, conditional overlap is at most \((1-c_q b^2)^{\operatorname{wt}(av)}\). Using \(d b^2\le1\) yields one-row overlap at most \(1-c'_q d b^2\). The wrong-label pair probability under an unrestricted maximum-likelihood rule is at most the \(T\)-th power of the one-row overlap, by bounding the likelihood-ratio threshold with its square root. Taking the union over fewer than \(q^d\) labels proves a vanishing statistical error for \(T\ge C_q b^{-2}\) with large enough fixed \(C_q\). No procedure to carry out that unrestricted rule efficiently is provided.

The binary constant-pass theorem is Lyu--Tal--Wu--Yang's result, not proved here. [Garg--Raz--Tal, CCC 2019](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2019.22) initiated the two-pass extractor approach, and [Garg--Kothari--Liu--Raz, arXiv:2107.02320](https://arxiv.org/abs/2107.02320) give one-pass results for noisy binary labels rather than (1). [Castagnoli--Massey--Schoeller--von Seemann](https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI433.pdf) develop the repeated-root cyclic-code setting; we use only the elementary repetition identity (8). The contribution here is the distribution-preserving bridge via a balanced sign and an independent translation for odd fixed modulus, and the separate frequency-mass versus ideal-rank bridge for \(q=2\). The [same-repository one-pass result](ring-lwe-one-pass-memory-lower-bound.md) covers a wider noise envelope for fixed odd modulus using a continuous overlap argument, not rereads. Search did not locate either bridge in the cited work. We make no claim about other noise scales, growing moduli, mixed even moduli beyond \(2\), many growing passes, cryptographic implementations or deployed parameters.

The companion verifier is an exact/rational check of the finite ring identities, fiber rounding, character extraction and representative arithmetic, not a substitute for the proofs or the external binary learning theorem.
