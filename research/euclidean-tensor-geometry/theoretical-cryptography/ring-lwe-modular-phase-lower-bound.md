# Dense modular polynomial tests of quantized broad dyadic observations

Even a single polynomial of algebraic degree two over a prime field may depend on every reported digit, so local-coordinate degree does not bound it. Quantized broad dyadic observations nevertheless fool all such polynomials, including programs that pick the coefficients of a dense quadratic after inspecting the entire public design. The argument also handles linear-size adaptive quadratic probes, output labels with quadratic digits, and subquadratically many unions of quadratic fibers. Section 5 extends these conclusions to all cubic phases in every characteristic and gives bounds for higher fixed degrees in high characteristic.

## 1. Model and results

Fix an odd integer \(q\ge3\), any digit prime \(p\), and fixed constants \(\beta,K,A_0>0\). Let \(d\) grow through powers of two, \(R=(\mathbb Z/q)[X]/(X^d+1)\), and \(1\le m\le d^{A_0}\). Use uniform independent \(S,A_1,\ldots,A_m\) in \(R\), with continuous observations
\[
 Y_i=A_i S/q+E_i,\qquad
 f_b(x)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i kx},\qquad b=\beta/d.
\]
Every noise coefficient has density \(f_b\) on the coefficient circle, independently given the label and the design. Let \(g_b=q^{-1}\sum_a f_b(\cdot-a/q)\) be the scalar reference. Partition each scalar response into \(p^s\) equal-\(g_b\)-probability sets, with \(1\le s\le K\log d\), and identify those sets bijectively with \(\mathbb F_p^s\). The reference is independent uniform digits \(U\). The partitions and bijections may depend on the public design, not on the other observations. Write \(B\in\mathbb F_p^{smd}\) for the digits obtained.

There are constants \(c_0,c_1>0\) such that, except on an event of public designs of probability \(e^{-c_1d}\), the following hold simultaneously for every \(I\subseteq[d]\) of size at most \(c_0d\), and every \(w=S_I\):

1. For every algebraic quadratic \(F:\mathbb F_p^{smd}\to\mathbb F_p\), including every affine function, and every nontrivial character \(\chi\) of \(\mathbb F_p\),
\[
 \left|{\mathbb E}[\chi(F(B))\mid A,S_I=w]
                  -{\mathbb E}[\chi(F(U))\mid A]\right|\le e^{-c_1d}.
\tag{1}
\]
The quantifier covers arbitrary affine digit preprocessing (including dependent outputs) followed by a quadratic, by substitution.
2. A program can adaptively query the value of at most \(c_2d\) quadratics, chosen from prior answers and the design, and perform arbitrary additional computations **on those replies**. For a sufficiently small \(c_2>0\), its entire view differs in total variation by at most \(e^{-c_3d}\) from its view on \(U\), for every conditional label \(w\). In particular the probability of returning the correct projection among a list of at most \(L\) is at most \(L/q^{|I|}+e^{-c_3d}\) conditional on a good design. The same conclusions for guessing a full label follow by choosing \(|I|\) a small positive fraction of \(d\). Independent randomness is allowed.
3. Alternatively, there is no limit on the number of output digits if each returned candidate is a tuple of quadratics of the input digits, with no nonlinear postprocessing after those quadratics except interpretation as a candidate. For any fixed injective encoding of projection candidates the list success bound is \(L/q^{|I|}+L e^{-c_1d}\). It also bounds full-label success when full labels are encoded coefficient by coefficient, so the projected digits can be selected as a subset of the output.
4. A union of \(M\) events, each of which is an arbitrary conjunction of equations \(F_j(B)=a_j\) with quadratic \(F_j\), differs in acceptance probability from the same test on \(U\) by at most
\[
             C \exp[-c_4 d/\sqrt{M}]+e^{-c_4 d}\quad(M\ge1).
\tag{2}
\]
Here \(C,c_4\) can be fixed uniformly. At \(p=2\) this includes DNFs of arbitrary quadratic literals, without a term-width bound. Thus a fixed such decision succeeds no better than the reference to \(o(1)\) error when \(M=o(d^2)\); no independence of the conjunctions or their literals is assumed.

The model is naturally incomparable with low coordinate-degree scores: a dense linear digit phase may have full coordinate degree as a real-valued function. These results do not rule out arbitrary compositions of modular polynomials, threshold circuits, or unrestricted classical computation.

## 2. Two properties of the same conditional digit law

Let \(V_I\subset R\) consist of vectors supported on \(I\). A short nontrivial linear combination of scalar phases of \(A_iS\) is represented on \(S\) by \(\sum_i P_i\overline A_i\), with bar the substitution \(X\mapsto X^{-1}\), and with each \(P_i\) collecting the chosen weights at positions of its row. This is the adjoint identity because multiplication by \(X\) is a signed permutation. Uniform independent designs make this sum uniform on the nonzero ideal \(\sum_i R P_i\).

Every nonzero ideal has size \(\ge e^{c_qd}\) for a fixed \(c_q>0\). To see this, a nonzero finite \(R\)-module has a simple quotient, of the form \(R/\mathfrak m\); maximal ideals correspond to irreducible factors of \(X^d+1\) over some prime \(r\mid q\). Such factors have degree \({\rm ord}_{2d}(r)=\Theta_q(d)\), since every root has order \(2d\) and the successive-squaring identity \(v_2(r^{2^k}-1)=v_2(r^2-1)+k-1\) gives eventual doubling of the order. Thus for each choice of nonzero weights and each \(I\), the chance of a relation in \(V_I\) is at most \(q^{|I|}e^{-c_qd}\). There are at most \((qmd+1)^{h+1}\) short combinations of length \(\le h\) and at most \(\exp(H(c_0)d+o(d))\) sets \(I\) of size at most \(c_0d\). Choose \(h=\lfloor c_5 d/\log d\rfloor\) and \(c_0,c_5\) small. A union bound proves that no such relation occurs on a good design, with exponentially small failure probability.

This rules out every nontrivial character of the combined short-sample phases and the declared label coordinates that vanishes identically on their linear image. By finite additive-group duality (also at composite \(q\)), every such combined map is onto. Hence under any \(S_I=w\), any \(h\) selected scalar phases are jointly uniform; independent noises then give product \(g_b\) on those positions. Their digit blocks are exactly independent uniform. This is the same bounded-independence ingredient as in our [previous Boolean circuit result](https://github.com/mxym/math/blob/0407833e73454bc7b1b05e969fd5fa911f3d0e9e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-classical-ac0-lower-bound.md).

The new use of the scalar channel is its **common uniform component**. Uniformly in the true signal symbol and the response, \(f_b(y-a/q)/g_b(y)=1+O_q(b)\) by the convergent Fourier series. Integrating over any reference-quantile set, the digit law at a coordinate given the entire label \(S\) has density between \(1-\epsilon\) and \(1+\epsilon\) relative to uniform on \(\mathbb F_p^s\), where \(\epsilon=C_q\beta/d\). In particular it decomposes exactly as \((1-\epsilon)U_j+\epsilon R_{j,S}\). Conditional on the full label, the blocks are independent: they can be generated with independent tags of probability \(\epsilon\), independent uniform outputs on untagged blocks, and residual laws \(R_{j,S}\) on tagged blocks. The tags can be independent of \(S\), also conditional on \(S_I=w\); the untagged digits remain uniform even after revealing the tag mask and every tagged output.

Every linear digit character that tests at most \(h\) blocks has zero nontrivial expectation by the exact independence. Every one testing \(k>h\) blocks has expectation of modulus at most \(\epsilon^k\): given the full label, a nonzero local character has zero mean under uniform and modulus at most 1 on its residual law. Combining the two estimates, the conditional digit law is \(\Delta\)-biased in the additive group \(\mathbb F_p^{smd}\) with
\[
                        \Delta\le\epsilon^{h+1}=e^{-\Omega(d)}.
\tag{3}
\]
No restriction on how a linear digit character crosses blocks or is chosen from the design is necessary.

## 3. General lemma: small bias plus fresh blocks fools every quadratic

Consider **any** distribution on \(n\) blocks of at most \(s\) digits over \(\mathbb F_p\) with linear-character bias at most \(\Delta\), and with the common-uniform-tag property above at parameter \(\epsilon\). Let \(F\) be a quadratic with polar form
\[
 B_F(x,z)=F(x+z)-F(x)-F(z)+F(0),
\]
whose rank is \(r\). Constants below work for any odd or even digit prime.

For \(f=\chi(F)\) use normalized Fourier coefficients. Squaring their modulus and taking differences of pairs of inputs gives
\[
 |\widehat f(u)|^2 =
 p^{-n'}\!\sum_{z\in\ker B_F}\chi(F(z)-F(0)-u\cdot z),
\tag{4}
\]
where \(n'\) is the total number of digits. The character sum over the first input is zero unless \(z\) annihilates the polar form, giving the expression. On the kernel \(F(z)-F(0)\) is additive, hence linear over the prime field. Thus the Fourier support is one affine subspace of size \(p^r\), on which every coefficient has modulus \(p^{-r/2}\). The small-bias bound alone controls the difference of \(F\)-phase expectations by \(\Delta p^{r/2}\). This includes rank zero.

For large rank, fix a nonsingular principal \(r\times r\) minor of the symmetric polar matrix. One exists: pivot on a nonzero diagonal if available, otherwise on an invertible two-by-two off-diagonal block of a nonzero matrix, and recurse on the symmetric Schur complement. The selected principal index set has the cardinality of the rank and nonzero determinant by the Schur determinant formula. Let \(r_j\) be the number of its variables in block \(j\), so \(0\le r_j\le s,\ \sum_jr_j=r\). Write \(H=\sum_j r_j\,1_{\{j\ {\rm tagged}\}}\). Conditional on the tagged values, the restriction of \(F\) to the independent uniform untagged inputs has rank at least \(r-2H\) when \(H\le r/2\): deleting each fixed index from the nonsingular minor removes one row and one column and lowers rank by at most two. Setting fixed variables only changes the lower-degree terms of the remaining polynomial. When \(H\le r/4\), formula (4) for the restricted polynomial gives uniform-phase magnitude at most \(p^{-r/4}\).

For \(t>0\), independent tags and the convex-chord bound \(e^{t r_j}-1\le(r_j/s)(e^{ts}-1)\) give
\[
        {\mathbb E} e^{tH}
        \le \exp\!\left[\epsilon\frac{r}{s}\bigl(e^{ts}-1\bigr)\right].
\]
Set \(t=\log(1/\epsilon)/(2s)\). For all sufficiently small \(\epsilon\),
\[
 \Pr[H>r/4]\le
   \exp\left[-\frac{r\log(1/\epsilon)}{16s}\right].
\tag{5}
\]
The unconditional phase under the tagged product mixture has magnitude at most this probability plus \(p^{-r/4}\). The null phase has magnitude at most \(p^{-r/2}\).

The resulting general bound is the minimum of \(\Delta p^{r/2}\) and the sum of (5), \(p^{-r/4}\) and \(p^{-r/2}\). For \(r\le\log(1/\Delta)/\log p\), the first bound is at most \(\sqrt{\Delta}\). Above that cutoff and for \(s=O(\log(1/\epsilon))\), the second bound is \(e^{-\Omega(\log(1/\Delta))}\). Applying (3) proves (1).

Both premises matter. In \(\mathbb F_2^{2k}\), take the uniform law conditioned on \(\sum_{i=1}^k x_{2i-1}x_{2i}=0\). Its nonzero linear biases are at most \(2^{-k}/(1+2^{-k})\), by (4) and the positive uniform phase mean \(2^{-k}\). Yet the quadratic is identically zero on it. Thus small bias alone is not enough; the high-rank bound uses the exact independence of the fresh uniform blocks. Conversely, tagging a single binary block and outputting 0 on its tagged branch gives a linear bias of \(\epsilon\), so the fresh-block property alone need not give exponential accuracy. This differs from [Viola's sum of independent small-bias distributions](https://doi.org/10.1007/s00037-009-0273-5), which is a different sufficient mechanism, and from the scope of [Derksen, Ivanov, Lee and Viola's smoothing results](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.18), which do not assert this conditional ring statement.

## 4. Fibers, adaptive transcripts and unions

For any list \(F_1,\ldots,F_k\) of quadratics, the indicator of simultaneous equations \(F_i(y)=a_i\) is
\[
   p^{-k}\sum_{\lambda\in\mathbb F_p^k}
        \chi\!\left(\sum_i\lambda_i(F_i(y)-a_i)\right).
\tag{6}
\]
Every summand is a quadratic phase and their coefficient absolute values sum to 1. Hence the acceptance-probability error for any fiber or any intersection of fibers is at most \(\eta=e^{-c_1d}\), with no dependence on \(k\). The equations need not be independent.

For a fixed path in an adaptive algorithm the chosen quadratics are fixed by the prescribed earlier replies. Its path event is exactly a fiber (6). A tree with at most \(k\) queries and \(p\)-valued replies has at most \(p^k\) leaves, giving total variation error at most \(p^k\eta/2\); choose \(k\le c_2d\). Fixing and averaging the program's independent random coins is harmless. Since the reference law \(U\) does not depend on \(w\), the conditional reference probability of guessing a uniform \(w\) among \(L\) candidates is at most \(L/q^{|I|}\). This proves the adaptive-list result. For outputs whose digits are directly quadratic, the event of matching one specified label is itself a fiber no matter how many digits are output. Apply (6) before summing over candidates and averaging over the target label (or label projection) to obtain the \(L\eta\) version. For full candidates under the stated coordinatewise encoding, read the required projection digits directly, then use the projected success bound; a full match implies a projected match.

For the union claim, take \(X=M^{-1}\sum_{j=1}^M 1_{\{E_j\}}\), where the \(E_j\)'s are arbitrary fibers. Every power \(X^r\) is an **average** of indicators of intersections of fibers (repetitions allowed), so its expectation differs by at most \(\eta\) for every \(r\ge1\). For \(M\ge2\), let \(T_k\) be the Chebyshev polynomial of the first kind and put
\[
     P_k(x)=1-\frac{T_k((M+1-2Mx)/(M-1))}
                        {T_k((M+1)/(M-1))}.
\]
It is zero at \(x=0\), and \(|P_k(x)-1|\le 2e^{-c k/\sqrt M}\) on \(1/M\le x\le1\), since the numerator's argument is in \([-1,1]\) and \({\rm arcosh}((M+1)/(M-1))=\Omega(1/\sqrt M)\). As a polynomial in \(x\) its coefficient \(\ell^1\) norm is at most \(1+15^k\): the numerator's affine argument has coefficient norm at most 7, apply the Chebyshev recurrence and the fact that the denominator is at least 1. The expectation error of \(P_k\) is at most \(\eta(1+15^k)\). Taking \(k\) a sufficiently small fixed positive multiple of \(d\) proves (2), with a single fiber handled by (6). This uses polynomial approximation only for the number of **already defined events**, not a low-degree expansion in the original data digits.

## 5. Cubic phases in every characteristic, and higher degrees

The same conditional law of §2 gives an exponential bound for **all cubic phases over every prime field**, not just quadratics. For every fixed degree \(k\ge4\) and digit prime \(p>k\), the unconditional quasi-linear partition-rank comparison gives the bound
\[
                  \eta_k(d)\le \exp[-c_k d/(\log d)^{k-3}].
\tag{7}
\]
Here \(\eta_k(d)\) is the worst difference in the two expectations in (1) with any polynomial of degree \(\le k\). If one invokes the claimed linear comparison in the [November 2026 preprint Chen–Ye, arXiv:2611.30721v1, Theorem 1.1](https://arxiv.org/html/2611.30721v1), the same argument improves (7) to \(\exp[-c_k'd]\); the preceding claims do not depend on the new preprint. All the fiber arguments of §4 still apply to degree \(\le k\) polynomials, with \(d\) in the query budget and the two exponential error terms of (2) replaced by the error exponent scale of the corresponding phase result. There is no low-characteristic claim above degree three.

For completeness, write the top polarization of a polynomial \(F\) of degree at most \(k\) as \(T_F(h_1,\ldots,h_k)=\Delta_{h_1}\cdots\Delta_{h_k}F(x)\). It is independent of \(x\) and multilinear in the directions, by expanding each monomial. The analytic rank \(r\) of this tensor is \(-\log_p\mathbb E_{h_1,\ldots,h_k}\chi(T_F(h_1,\ldots,h_k))\); the character average is real positive since averaging over the last direction leaves the proportion of zero contractions. Repeated Cauchy-Schwarz (or the Gowers norm inequality) gives for uniform arguments
\[
                      |{\mathbb E}\chi(F)|\le p^{-r/2^k}.
\tag{8}
\]
Setting arbitrary variables to constants leaves the top polarization on the remaining coordinates exactly the restriction of \(T_F\), so (8) applies uniformly in those fixed values.

**High analytic rank, including the grouped tags.** By [Briët and Castro-Silva, Random Restrictions of High-Rank Tensors and Polynomial Maps, Corollary 1.5](https://arxiv.org/abs/2212.13728), independent retention of each digit coordinate with any fixed probability \(\sigma>0\) preserves a positive constant fraction of the analytic rank except with probability \(C e^{-c r}\); the same retained subset is used in all \(k\) slots. We cannot simply treat the actual digit tags from §2 as independent per digit, since all digits of a scalar block share a tag. Instead sample the independently retained coordinate set \(J\) first. Choose \(\sigma\) so small that \((1-\sigma)^s\ge d^{-1/2}\) when \(s\le K\log d\). At each block with \(s_j\le s\) digits, give it a tag only if \(J\) entirely misses the block, and then with probability \(\epsilon/(1-\sigma)^{s_j}\). This is at most 1 for all sufficiently large \(d\), the tags have exactly their original independent Bernoulli-\(\epsilon\) law, and every digit in \(J\) is untagged. After sampling the label and all block outputs in the original way, condition on \(J\), the labels and tag masks, and all values outside \(J\). The remaining digits are still jointly uniform, so (8) on \(J\) and the rank retention bound give \(|\mathbb E_P\chi(F)|\le C'e^{-c'r}\). The reference has the same type of bound by (8) without any restriction.

**Cubic low rank without dividing by \(3!\).** For order three, partition rank equals slice rank; [Lampert, Slice Rank and Analytic Rank for Trilinear Forms](https://discreteanalysisjournal.com/article/145198-slice-rank-and-analytic-rank-for-trilinear-forms) proves a linear bound \(R\le C r\) in every finite field. Write the polarization as a sum of \(R\) slices, each distinguished factor a linear form on one slot. Intersect the kernels of all these linear factors in the common variable space, obtaining a subspace \(H\) of codimension \(j\le R\), with \(T_F|_{H^3}=0\). For every affine coset of \(H\) the restriction of \(F\) has degree at most two, including in characteristics 2 and 3. In detail, for a function represented in reduced form (individual powers \(<p\)), the highest nonzero total degree equals its highest nonzero additive derivative order. Apply coordinate differences on any highest monomial \(x^\nu\), taking \(\nu_i\) differences along the \(i\)-th unit vector; other monomials of that degree cannot survive those same differences unless their exponents equal \(\nu\), and the surviving factor is \(\prod_i\nu_i!\ne0\) in \(\mathbb F_p\). Thus vanishing of the top derivative is sufficient on each coset. A linear choice of coordinates \(Bx=z\) for the cosets gives quadratic polynomials \(Q_z\) on the full input space by composing the coset restriction with a linear projection onto \(H\). Hence
\[
                 \chi(F(x))=\sum_{z\in\mathbb F_p^j}1_{\{Bx=z\}}\chi(Q_z(x)).
\]
Expanding each indicator as in (6) expresses each summand as a combination of quadratic phases with coefficient \(\ell^1\) norm exactly 1 before merging. The error is therefore at most \(p^j\eta_2(d)\). Combining this with the preceding high-rank bound and splitting at \(r=a d\) for a sufficiently small fixed \(a>0\) proves \(\eta_3\le e^{-c_3'd}\). This argument does not use diagonal recovery of a cubic from its tensor in small characteristic.

**Higher-degree low rank in high characteristic.** If \(p>k\), the degree-\(k\) homogeneous part of \(F\) equals \(T_F(x,\ldots,x)/k!\). A partition-rank decomposition with \(R\) terms therefore writes \(F=F_{<k}+\sum_{j=1}^{R} U_j V_j\), with all displayed factor polynomials of degree at most \(k-1\): evaluate each tensor partition factor on the appropriate number of copies of \(x\) and absorb \(1/k!\) into one factor. The \(\mathbb F_p^2\) Fourier expansion of \((u,v)\mapsto\chi(uv)\) has coefficient \(\ell^1\) norm at most \(p\) by Parseval and Cauchy-Schwarz. Taking the product and including \(F_{<k}\) makes \(p^R\eta_{k-1}(d)\) an error bound, since every summand is again a lower-degree phase.

For [Moshkovitz and Zhu, Quasi-linear Relation, Theorem 2](https://arxiv.org/html/2211.05780), \(R\le C_k r[1+\log(1+r)]\). If \(\eta_{k-1}\le e^{-E}\), split at \(r=aE/\log(2+E)\) with \(a\) small, using the structural bound below and \(C'e^{-c'r}\) above. This gives error \(\exp[-\Omega(E/\log(2+E))]\), which iterates from the cubic case to (7). Replacing that comparison by the recent claimed \(R\le C_k r\) changes the split to \(r=aE\), giving the separately stated exponential consequence. Treating that preprint as an input is not a verification of its new proof.

The structure/large-rank strategy already appears in [Briët, Buhrman, Castro-Silva and Neumann, Noisy Decoding by Shallow Circuits with Parities, §7](https://homepages.cwi.nl/~jop/qccodes.pdf). Their Theorem 7.1 bounds recovery of a full message by a polynomial map after digitwise symmetric noise on an arbitrary encoding. The claims here compare **individual phase expectations against a common reference conditional on a public ring design and on any small label projection**, with a block tag shared by all digits of each quantile; a message recovery bound alone does not say that. We use their qualitative strategy, an explicit coupling for the dependent digit restrictions, and a cubic coset argument to avoid a high-characteristic assumption at degree three. Neither result implies a general classical complexity lower bound.

## 6. Statistical contrast and scope

For the particular choice of equal-probability intervals under \(g_b\) with \(p^s\gg\sqrt d\), take \(m b^2\to t>\log q\). The [previous fixed-modulus statistical theorem](https://github.com/mxym/math/blob/18d24b1b111079badad2799860d77be0c27ec244/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-odd-modulus-threshold.md) gives unrestricted statistical success tending to one before rounding. It persists after these bins: transform to the scalar cumulative-probability coordinate and reconstruct with independent uniform reference inside each reported bin. The conditional density ratio has derivative uniformly \(O(b)\) in that coordinate, so the per-coordinate pointwise replacement error is \(O(b/p^s)\); densities are bounded away from zero. Hellinger tensorization gives total variation error \(O(\sqrt{md}\,b/p^s)=o(1)\), uniformly in label and design. Binned sufficiency is only an information statement, not an efficient algorithm.

The results distinguish bounded algebraic modular computation from either a single coordinate-degree likelihood score or the earlier \(\mathrm{AC}^0\) result that allowed an independent collection of parity precomputations. Arbitrary dependent affine preprocessing is permitted here because it preserves algebraic degree; arbitrary Boolean circuits following those affine or quadratic computations are not thereby covered. No actual cryptographic system, deployment parameter, implementation, or recovery procedure is studied.
