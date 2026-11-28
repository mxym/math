# Entropy-scale local-batch communication lower bound for wrapped ring learning

## 1. Model and result

Fix an odd integer \(q\ge3\), a fixed \(\beta>0\), and a positive \(t\). Let \(d\) grow through powers of two; \(R=(\mathbb Z/q)[X]/(X^d+1)\), \(N=q^d\), and \(S\) is uniform in \(R\). Write
\[
 b=\beta/d,\quad k=\lfloor t/b^2\rfloor,\quad
 f_b(y)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i j y},\quad
 p(y)=\prod_{j=1}^d f_b(y_j).
\]
A row is \((A,Y)\), where \(A\) is uniform on \(R\) and \(Y=AS/q+E\) on the coefficient torus with independent \(E\) of density \(p\); rows, including the public-design values \(A\), are independent conditional on \(S\).

A coordinator can engage \(B\) fresh parties sequentially. Each party privately receives \(k\) whole rows, including its own coefficients, and encodes them into one message with at most \(2^m\) possibilities. Its encoder can depend arbitrarily on the earlier transcript and shared randomness, and it can perform arbitrary measurable local computations. The coordinator has unbounded memory and time. It sees **none** of the private batch, including the coefficient values, except through the returned message. No party is revisited, and no private batch is shared between parties. A bounded-length variable message may instead be used with the evident bound on the number of transcripts. The term “public design” refers to design being revealed together with its row, not to a free broadcast to the coordinator.

Let
\[
 \alpha_q=\lim_{d\to\infty}\frac1d\log\min_{0\ne J\lhd R}|J|
 =\min_{p\ {\rm prime},\,p\mid q}\lim_{d\to\infty}
 \frac{\operatorname{ord}_{2d}(p)}d\log p>0.
\tag{1}
\]
Logs are natural unless marked bits. The limits in (1) are in fact eventually constant after taking the ratios.

**Theorem.** Suppose \(0<t<\log q\) and
\[
 \limsup_{d\to\infty}\frac{m\log2}{d}<
 \min\{\alpha_q,\log q-t\}.
\tag{2}
\]
There are constants \(c,c'>0\) such that for \(B\le e^{cd}\) the joint law of \(S\) and the complete coordinator view has total variation distance at most \(e^{-c'd}\) from a law where \(S\) is uniform independent of that view. In particular the exact-label success probability is at most \(q^{-d}+e^{-c'd}\), and advantage in predicting any balanced binary property of \(S\) is at most \(e^{-c'd}\). The statement holds with data-independent randomized decisions, arbitrary real observations, and an unbounded coordinator. It uses a worst-case bound on message alphabet size, not an average entropy budget.

The per-party sample threshold in this positive communication range reaches the actual local statistical threshold: if \(t>\log q\), unrestricted local inference from one batch already has probability \(1-e^{-\Omega(d)}\) of the right label. With at least one bit per message, a prescribed single bit of the label can then be sent with exponentially small error; for exact identification using small messages, disjoint fresh batches may report prescribed different bit positions of an injective label encoding. This is only an information-theoretic comparison, not a running-time assertion about the parties. At \(t=\log q\) no assertion is made. The lower bound also does not assert sharpness of the linear message rate in (2).

## 2. Exact Fourier diagonalization of a whole batch

Use the full-grid marginal
\[
 g_1(y)=f_{b^{q^2}}(qy),\qquad g(y)=\prod_j g_1(y_j);
 \qquad \nu=U_R\times (g(y)\,dy)
\]
as a convenient single-row reference. For \(k\) rows use \(\nu^{\otimes k}\). Let \(G\) be the product density of its \(k\) responses. A residual likelihood \(L(\mathbf y)\) on the \(k\)-row response torus defines likelihood for the batch at \(s\) by \(L(\mathbf y-\mathbf a s/q)\). Assume \(L\in L^2(G\,d\mathbf y)\); in the two uses below it is a nonnegative density of integral one relative to \(G\). For a \(k\)-tuple of residue frequencies \(\mathbf w=(w_1,\ldots,w_k)\in R^k\), let \(L_{\mathbf w}\) denote the projection onto the Fourier sector \(\mathbf w\) modulo \(q\), and put \(\Gamma_{\mathbf w}=\|L_{\mathbf w}\|^2_{L^2(G)}\). These sectors are orthogonal since \(G\) is invariant under all grid translations; their projections are the character averages of the finite grid action. Define the operator on hidden-label functions
\[
 (\mathcal T h)(\mathbf a,\mathbf y)=\mathbb E_s h(s)L(\mathbf y-\mathbf a s/q).
\]
Using the coefficient pairing and adjoint \(\langle u,av\rangle=\langle\bar a u,v\rangle\), \(\bar a=a(X^{-1})\), each shifted sector multiplies by the character \(\exp(-2\pi i\langle\sum_i\bar a_i w_i,s\rangle/q)\). For fixed \(\mathbf w\), the sum \(\sum_i\bar a_i w_i\) is uniform on the ideal \(J(\mathbf w)=\sum_i w_iR\): each summand is uniform on its image ideal, and addition of independent uniform subgroup elements is uniform on their sum. Hence exactly
\[
 \|\mathcal T h\|_2^2=\sum_{z\in R}|\widehat h(z)|^2\,\lambda_L(z),
 \qquad
 \lambda_L(z)=
 \sum_{\mathbf w}\Gamma_{\mathbf w}
    \frac{\mathbf1_{\{z\in J(\mathbf w)\}}}{|J(\mathbf w)|}.
\tag{3}
\]
This also proves diagonalization for complex \(h\); all norms on labels use uniform probability. The relevant squared operator norm on mean-zero functions is \(\lambda_*=\max_{z\ne0}\lambda_L(z)\). No independence of the response-coordinate sectors after truncation is needed in (3).

## 3. Before truncation: proper ideals are weak

For one original residual row set \(\ell(y)=p(y)/g(y)\). If \(j\) is a scalar residue, let
\[
 \gamma_j=\int_{\mathbb T}
 \frac{\left|\sum_{n\equiv j\bmod q} b^{n^2}e^{2\pi i n y}\right|^2}{g_1(y)}\,dy,
 \qquad w=(w_1,\ldots,w_d),\quad \gamma_w=\prod_{j=1}^d\gamma_{w_j}.
\]
Thus for the original \(k\)-row residual \(L=\prod_i\ell(y_i)\), \(\Gamma_{\mathbf w}=\prod_i\gamma_{w_i}\). Write \(W(J)=\sum_{w\in J}\gamma_w\). This is the squared norm of the projection of \(\ell\) onto sectors in \(J\); the analogous \(k\)-row norm is \(W(J)^k\). In particular \(\gamma_0=1\) at both scalar and vector levels.

All maximal residue fields of \(R\) have odd characteristic \(p\mid q\), and the image of \(X\) has exact order \(2d\). Thus a signed monomial, or a sum of two signed monomials with distinct exponents \(0,\ldots,d-1\), is a unit: if the binomial vanished in a maximal residue field, a nonzero exponent difference of absolute value less than \(d\) would have power \(+1\) or \(-1\). Every proper ideal therefore excludes these words. Scalar Parseval and \(g_1=1+O(b^{q^2})\) give \(\gamma_j=O_q(b^2)\) for \(j\ne0\), and \(O_q(b^8)\) if \(j\notin\{0,1,-1\}\). Summing either words of weight at least three or words with at least one nonzero residue other than \(\pm1\) gives, uniformly over all proper ideals,
\[
 1\le W(J)\le1+O_q(d^3b^6+d b^8),
 \qquad
 W(J)^k=1+O_{q,t,\beta}(d^{-1}).
\tag{4}
\]
For the sum, the other coordinates cost at most \((1+C_q b^2)^d\), uniformly bounded here; the support-at-least-three term follows by marking any three occupied coordinates. The full norm instead satisfies
\[
 W(R)^k=\left(\int_{\mathbb T} f_b(y)^2/g_1(y)\,dy\right)^{dk}
       =\exp(2td+o(d)).
\tag{5}
\]
This follows from \(f_b=1+2b\cos(2\pi y)+O(b^4)\), uniform on the circle. Applying an untruncated quadratic-moment argument to the full ideal would therefore restrict \(t\) to below \(\log q/2\), rather than the threshold proved here.

We record the elementary ideal-count facts. Over each \(\mathbb F_p\) with \(p\mid q\), every irreducible factor of \(X^d+1\) has degree \(f_p(d)=\operatorname{ord}_{2d}(p)\), with no repeated roots. The successive-squaring valuation \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\) shows that each \(f_p(d)/d\) stabilizes and is positive. Over \(\mathbb Z/p^e\), the coprime factors lift, and each monic factor quotient is free over the base, with residue field of size \(p^{f_p(d)}\). Its only maximal ideal is generated by \(p\); elements not in it are units, and divisibility by successive powers of \(p\) shows that all its ideals are \(p^j\) times the quotient. In detail, choose an element of an ideal with the smallest valuation \(j\); it is \(p^j\) times a unit, and every other element of that ideal is in \(p^j\) times the quotient. CRT over the factors and primes proves (1) and bounds the total number of ideals by a constant depending only on \(q\).

There is also a nonzero coefficient vector of bounded integer squared norm in a smallest ideal, uniformly as \(d\) grows. Choose a fixed dyadic \(d_0\) for which all residue degree ratios have stabilized. The substitution \(X_0\mapsto X^{d/d_0}\) embeds the base ring of dimension \(d_0\) into \(R\). Each residue irreducible of degree \(f_p(d_0)\) substitutes to an irreducible of degree \(f_p(d)\): it divides \(X^d+1\) and all of that polynomial's irreducibles have exactly that degree. The lifted factorization at \(p^e\) is preserved by substitution because it remains monic and pairwise coprime. A CRT idempotent for a selected factor and prime remains the corresponding idempotent in \(R\). Multiply the idempotent by \(p^{e-1}\) in the selected \(p^e\) factor and set the other components to zero; this nonzero element generates the minimal ideal there. Its coefficients are obtained from the fixed base coefficients solely by inserting zeros. Choose a factor attaining the minimum in (1).

## 4. Typical truncation preserves proper-ideal bounds

Under the actual product residual noise, the log likelihood \(\log L\) is a sum of \(dk\) independent scalar variables \(\log(f_b/g_1)\). Their magnitudes are \(O_q(b)\); their mean under \(f_b\) is \(b^2+O_q(b^3)\) by a uniform Taylor expansion of \(\log(1+2b\cos(2\pi y)+O(b^4))\), with \(\log g_1=O(b^{q^2})\). Thus \(\mathbb E\log L=td+O(1)\). For fixed \(\eta>0\), or for \(\eta=d^{-1/4}\), Hoeffding gives
\[
 \Pr_{p^{\otimes k}}\bigl(|\log L-td|>\eta d\bigr)
 \le C\exp(-c\eta^2 d)
\tag{6}
\]
for sufficiently large \(d\). The constants can depend on the fixed parameters but not on \(\eta\) in that range. Replace \(L\) by
\[
 L_\eta=L\mathbf1_{\{\log L\le(t+\eta)d\}}/Z,\qquad
 Z=\Pr_{p^{\otimes k}}\bigl(\log L\le(t+\eta)d\bigr).
\]
This is one normalized batch likelihood in residual coordinates, independent of the design and shift label; the same \(Z\) applies for every \(s\). It changes each batch law by total variation \(1-Z\). Also
\[
 \|L_\eta\|^2\le Z^{-1}e^{(t+\eta)d}.
\tag{7}
\]

The crucial fact is that discarding an exceptional Gaussian tail does not create a large proper-ideal energy. For an ideal \(J\), the projector onto sectors \(\mathbf w\in J^k\) is the average of translations by \((J^\perp)^k\) on the \(q\)-grid, where \(J^\perp\) is the annihilator for the coefficient pairing. This is a **positive** projection. The pointwise bound \(0\le L_\eta\le L/Z\) therefore gives
\[
 \sum_{\mathbf w\in J^k}\| (L_\eta)_{\mathbf w}\|^2
 =\|\Pi_{J^k}L_\eta\|^2\le Z^{-2}\|\Pi_{J^k}L\|^2=Z^{-2}W(J)^k.
\tag{8}
\]
The use of positivity is essential; an arbitrary clipped orthogonal sum need not satisfy (8). For \(z\ne0\), split (3) into the full ideal and nonzero proper ideals. Equations (1), (4), (7), and (8) give
\[
 \lambda_*\le Z^{-1}e^{(t+\eta-\log q)d}
                  +O_q(Z^{-2}e^{-\alpha_q d}).
\tag{9}
\]

For clarity, (9) has the correct exponential rates for this truncated *operator*, not necessarily for communication complexity. With \(\eta=d^{-1/4}\),
\[
 \lim_{d\to\infty}\tfrac1d\log \lambda_*=
 \max\{t-\log q,-\alpha_q\}.
\tag{10}
\]
Indeed the lower half of (6) gives \(\|L_\eta\|^2
 =Z^{-2}\mathbb E_{p^{\otimes k}}[L\,\mathbf1_{\{\log L\le(t+\eta)d\}}]\ge\exp(td-o(d))\). Proper-ideal sectors have total norm \(O_q(1)\) by (8), and all the remaining full-ideal sectors contribute equally to each \(\lambda(z)\). For the second lower bound take the bounded-weight vector \(w\) from Section 3, in a minimal ideal of size \(\exp(\alpha_qd)\). Use \(\mathbf w=(w,0,\ldots,0)\) in (3). A torus character with a bounded-norm integer frequency representing this residue tuple has unit norm in \(L^2(G)\), lies in that sector, and pairs with \(L\) to give \(b^{O_q(1)}\) with a fixed bounded exponent. Its pairing changes by at most \(2(1-Z)=e^{-\Omega(\sqrt d)}\) after truncation, because the pairing is an ordinary response characteristic coefficient of the original and clipped probability densities. Thus \(\|(L_\eta)_{\mathbf w}\|^2\ge e^{-o(d)}\), and \(\lambda(z)\) is at least this divided by \(\exp(\alpha_qd)\) for any nonzero \(z\in wR\). This proves (10).

## 5. From the batch operator to an adaptive transcript

Let \(K_u(v)\) be the probability that a party's encoder produces message \(u\) on a batch \(v\). Set \(r_u=\mathbb E_{\nu^{\otimes k}} K_u\), so \(\sum_ur_u=1\) and \(\|K_u\|_2^2\le r_u\). For the clipped family write \(p_s(u)=\mathbb E[K_u(V)\mid S=s]\) and \(\bar p(u)=\mathbb E_s p_s(u)\). By duality, \(p_s(u)-\bar p(u)\) is the centered adjoint applied to \(K_u\). Hence (3) implies
\[
 \mathbb E_s(p_s(u)-\bar p(u))^2\le\lambda_* r_u,\qquad
 \operatorname{TV}(P_{S,M},U_R\times\bar p)\le\tfrac12\sqrt{2^m\lambda_*},
\tag{11}
\]
The second inequality is Cauchy--Schwarz using the weights \(r_u\); if \(r_u=0\) all the probabilities for that message are zero. For the original family use the clipped average \(\bar p\) as the simulator; the same bound has an additional \(1-Z\). This is uniform over all encoders, including stochastic ones.

For a complete transcript, replace messages sequentially by the independent-prior simulator. In the hybrid pair whose first \(j-1\) messages are simulated and whose later messages after position \(j\) are real, the prefix has carried no information about \(S\). Consequently (11) with a uniform prior applies conditionally on every such prefix, even though the requested encoder is chosen using it. Appending all remaining real messages is a common channel given the prefix and \(S\), so total variation cannot increase. Shared randomness can be included before the prefix replacement. Summing the hybrid costs gives a total bound of
\[
 B\left(1-Z+\tfrac12\sqrt{2^m\lambda_*}\right).
\tag{12}
\]
By (2) choose a sufficiently small **fixed** \(\eta>0\); then (6) and (9) are both exponentially small at rates paying (12) for suitable \(B\le e^{cd}\). The shrinking \(\eta\) of (10) is not used for this exponential composition. The view in the fully simulated experiment is independent of the actual uniform \(S\), proving the claim.

## 6. Comparison to unbounded statistical inference and prior results

For \(t>\log q\), the true candidate's likelihood exceeds \(e^{(t-\eta)d}\) with probability \(1-e^{-\Omega(d)}\) by (6), with \(0<\eta<t-\log q\). If \(v=s'-s\ne0\), then \(A_iv\) is uniform on the nonzero ideal \(vR\). Averaging the false candidate likelihood over the design and the true residual yields for one row
\[
 \mathbb E_{A,E}\ell(E-A v/q)
 =\langle\ell,\Pi_{(vR)^\perp}\ell\rangle_{L^2(g)}
 =W((vR)^\perp).
\]
The additive annihilator \((vR)^\perp\) is a proper ideal by the adjoint pairing. Independence over the batch and (4) show the expected false likelihood is \(1+O(d^{-1})\). Markov and the union bound over \(q^d-1\) false labels give an exponentially small probability that any false candidate matches the true threshold. This proves the statistical comparison without placing any compute bound on a hypothetical maximum-likelihood rule. Conversely for \(t<\log q\) the same one-batch good likelihood cutoff, measured against \(\nu^{\otimes k}\) and an independent uniform \(S\), shows unrestricted single-batch exact success at most \(e^{(t+\eta-\log q)d}+1-Z\). Neither direction claims an efficient local solver.

[Steinhardt, Valiant and Wager, COLT 2016, §4, Theorem 11 and Lemmas 13–15](https://jmlr.csail.mit.edu/proceedings/papers/v49/steinhardt16.pdf) study the same general direction of sequential \(k\)-ary communication, with quadratic divergence and a spectral spending bound. Our message bound is a centered Hilbert-space version of that approach; the resource model and the general spectral idea are not new. The ring-specific content is the exact ideal-sector formula (3), the exhaustion of both first shells by units for every fixed odd modulus, and the subgroup-positive clipping in (8). Together they replace the full \(2t\) quadratic exponent by \(t\) without sacrificing exponentially small real-versus-simulated transcript error for fixed margins. The companion [constant-pass result](ring-lwe-constant-pass-memory-lower-bound.md) limits total retained state between individual samples instead; here only each fresh batch's outgoing message is limited. Neither result treats deployed parameters, public leakage of coefficient batches, interleaving repeated calls to one party, or unrestricted classical running time.

The companion script checks exact finite instances of (3), the ideal and compact witness claims and the positivity mechanism (8) on discrete algebraic examples. No target protocol, data, cryptographic secret or attack is in the test.
