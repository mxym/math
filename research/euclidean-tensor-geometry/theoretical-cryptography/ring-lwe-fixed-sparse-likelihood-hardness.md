# Worst-case likelihood over a fixed family of sparse negacyclic designs

**Result.** For every fixed odd prime \(q\), exact worst-case maximum-likelihood optimization with coefficientwise wrapped-Gaussian observations over \(\mathbb F_q[X]/(X^d+1)\) is NP-hard. The dimensions \(d\) are powers of two. The public designs can be fixed, uniformly computably, by dimension alone: every row is a distinct unit with exactly two nonzero coefficients, and the number of rows is at most \(d\). Only the rational-grid observations vary. At \(q=3\), the corresponding nearest coefficient-Hamming decision problem is NP-complete even on such a fixed design family. There is also a perfect-completeness \(11/12+\epsilon\) hardness gap for an explicitly normalized likelihood increment, using a second fixed-design family. These are deterministic worst-case statements about finite graph codes, not average-case Ring-LWE results.

## 1. Model and exact conclusion

Write \(R_d=\mathbb F_q[X]/(X^d+1)\), \(\mathbb T=\mathbb R/\mathbb Z\), and embed \(r\in\mathbb F_q\) additively in \(\mathbb T\) by \(r\mapsto r/q\). The wrapped-Gaussian density is
\[
 f_b(x)=\sum_{j\in\mathbb Z} b^{j^2}e^{2\pi i jx},\qquad 0<b<1.
\]
Poisson summation (or the positive periodized ordinary Gaussian formula) gives \(f_b>0\); it is smooth and even. Put \(h(x)=\log f_b(x)\) and \(H_q=\sum_{r\in\mathbb F_q} h(r/q)\). Also
\[
 f_b(0)-f_b(x)=2\sum_{j\ge1}b^{j^2}(1-\cos(2\pi jx))>0
 \quad(x\ne0\text{ in }\mathbb T).
\]
Given a design \(a=(a_1,\ldots,a_T)\) and observations \(y_t\in\mathbb T^d\), the log-likelihood of a label \(s\in R_d\) is
\[
 \ell_y(s)=\sum_{t=1}^T\sum_{j=0}^{d-1}
 h\big(y_{tj}-(a_t s)_j/q\big).
 \tag{1}
\]
A uniform label prior leaves the maximizers unchanged. In the algorithmic question here, inputs \(y_t\) are given on the rational grid. The claim is about returning a label maximizing (1); the reductions give explicit affine transformations of integer objectives, with no numerical evaluation of a transcendental threshold. In fact one family below works for every common \(b\in(0,1)\) simultaneously, including \(b=\beta/d\) for fixed \(\beta>0\) and sufficiently large \(d\).

The coefficient-Hamming question has a grid word \(v\in R_d^T\) and integer threshold \(D_0\) as input: is there an \(s\) with \(\#\{(t,j):v_{tj}\ne (a_ts)_j\}\le D_0\)? At \(q=3\) write \(h_0=h(0)\), \(h_1=h(1/3)=h(2/3)\), and \(\gamma=h_0-h_1>0\). On this grid, (1) is exactly \(Td h_0-\gamma D(s)\). Because all \(a_t\) are units, the graph code \(\{(a_1s,\ldots,a_Ts):s\in R_d\}\) is a free rank-one \(R_d\)-module and any block alone is an invertible linear map. Thus the conclusion is not caused by rank deficiency, a singular row, or a row repeated in the design.

## 2. Fixed public designs and phase balancing

Pad the number of abstract vertices to a power of two \(N\ge4\). Pick the least prime \(P>N\); Bertrand's postulate places it below \(2N\), so even trial division in this finite range is polynomial in \(N\). For \(0\le i<N\) take
\[
 p_i=2Pi+(i^2\bmod P).
 \tag{2}
\]
All positive differences \(p_j-p_i\) for \(i<j\) are distinct. In an equality of two differences their main terms \(2P(j-i)\) must agree since the difference of the two residual terms has magnitude \(<2P\). Writing \(u=j-i>0\), equality modulo \(P\) makes \(u(j+i)\) the same for both pairs. Since \(u\ne0\bmod P\) and \(P\) is odd, both indices agree modulo \(P\), hence agree as integers. Take \(d\) a power of two with \(d>2p_{N-1}\) and \(d\ge T\). Below it is a fixed constant multiple of \(N^2\), or of \(N^4\) for the gap construction.

For slot \(\{i,j\}\), \(i<j\), take base \(a_{ij}=X^{-p_i}-X^{-p_j}\). Its product with \(s\) has coordinate zero equal to \(z=s_{p_i}-s_{p_j}\): exponents \(k-p_i\) for other coordinates \(k\) are not zero modulo \(d\). For any nonzero scalar \(u\), \(u a_{ij}\) is a two-term unit. In fact, after factoring a signed monomial and a nonzero scalar, the relevant factor has form \(1-W\), with \(W=\pm X^\ell\), \(0<\ell<d\). Set \(e=d/\gcd(d,\ell)\). Then \(e\) is even and \(W^e=-1\), since \(\ell/\gcd(d,\ell)\) is odd. Thus \((1-W)(1+W+\cdots+W^{e-1})=2\), a unit for odd \(q\).

Fix any ordering of all the rows of all allocated slots, including inactive slots, and give row number \(t=0,\ldots,T-1\) public coefficient \(X^t u a_{ij}\). Whenever the unshifted observation is \(y\), use shifted observation \(X^t y\), where \(X^t\) acts on \(\mathbb T^d\) by the same signed coordinate permutation as on \(R_d\). This does not change the row contribution to (1), or the Hamming distance on the grid, by evenness of \(h\). Every public coefficient is distinct. The two-position support of each row has shorter cyclic separation \(p_j-p_i<d/2\); different unordered pairs have different separations, by (2). A two-point set on the cycle with non-antipodal points has no nonzero translation stabilizer: such a translation would have to exchange the points and then have order two. Thus different shifts of the same pair have distinct supports as well. In particular no equality between row coefficients is needed to balance phases.

For a fixed base \(u a_{ij}\), allocate a number \(K\) of rows divisible by \(q\). In the unshifted observations every nuisance coordinate \(j\ne0\) runs through all \(q\) phases \(r/q\) equally often; the active coordinate \(j=0\) is assigned independently with an arbitrary target multiset of size \(K\). The sum at every nuisance coordinate is \((K/q)H_q\), independent of \(s\). At the active coordinate the score is \(\sum_{c} n_c h((c-uz)/q)\), where \(n_c\) is the chosen target count. These are identities on the complete \(d\)-coordinate observations, not measurements in which coordinates have been discarded.

## 3. Fixed-design hardness for every fixed odd prime

Allocate a slot for every pair \(i<j\). Each slot has a subblock for every \(u\ne0\), each of \(q(q-1)\) rows for \(u a_{ij}\), with the public shifts from Section 2. Thus \(T=q(q-1)^2\binom N2\). Choose \(d=C_q N^2\) with fixed power-of-two \(C_q\ge\max(16,q(q-1)^2)\). This guarantees \(d>2p_{N-1}\), \(d\ge T\). Distinct dyadic \(N\) give distinct \(d\); designs for irrelevant dimensions may be arbitrary. The only dependence on the input graph is in the observations:

* In an active slot (edge), each nonzero \(c\) is an active target \(q\) times for each \(u\); zero never is.
* In an inactive slot, each \(c\), zero included, is an active target \(q-1\) times for each \(u\); the score is constant.

For an active slot the sum of its active-coordinate contributions is
\[
 q\left((q-1)H_q-\sum_{u\ne0}h(uz/q)\right).
\]
Here the minus sign inside the original residual is immaterial by evenness. For \(z=0\) the final sum is \((q-1)h(0)\); for \(z\ne0\), \(u\mapsto uz\) permutes \(\mathbb F_q^\times\), so the sum is \(H_q-h(0)\). Therefore the whole batch has
\[
 \ell_y(s)=C_y+\kappa_b\#\{\{i,j\}\text{ active}:s_{p_i}\ne s_{p_j}\},
 \qquad
 \kappa_b=q\big(qh(0)-H_q\big)>0.
 \tag{3}
\]
Here \(C_y\) is explicit, independent of \(s\), with an additive contribution per active slot equal to its score at \(z=0\). Any assignment of the vertex labels extends to a label in \(R_d\). The input graph is \(q\)-colorable iff its optimal score in (3) satisfies every edge, something checked on a returned maximizing label with finite arithmetic. For \(q=3\) use 3-colorability (e.g. the exact consequence of [Austrin–O'Donnell–Tan–Wright, Theorem 1.1](https://www.cs.utexas.edu/~wright/papers/coloring.pdf)), and for each fixed \(q>3\) append a \(q-3\) vertex clique adjacent to every original vertex. This proves NP-hardness of the search objective under a single-call deterministic polynomial reduction. No comparison of irrational thresholds is used.

## 4. Ternary Hamming completeness and a perfect-completeness gap

Use only \(u=1\) at \(q=3\) and six rows per pair slot. Every nuisance coordinate visits each phase twice. An active slot asks for \(z\ne c_0\) for a grid residue \(c_0\), and gives target count zero at \(c_0\), three at each of the other two residues. An inactive slot gives each residue target count two. Both have the same fixed public design. Whenever a pair is presented in reverse order, negate its forbidden residue as well. In a batch of \(L\) slots, of which \(M\) are active, let \(U(s)\) count satisfied active inequalities. Counting matches gives the exact formula
\[
 D(s)=L(4d+2)-2(L-M)-3U(s).
 \tag{4}
\]
In particular, use one slot for every pair at \(d=16N^2\), set \(c_0=0\) on graph edges and mark other slots inactive. The integer threshold \(D_0=L(4d+2)-2(L-M)-3M\) gives a many-one reduction from 3-colorability. Membership in NP simply multiplies the supplied label by each public polynomial and counts mismatches. This is an NP-complete decision problem for the fixed uniformly computable design family. If polynomial-time query algorithms were instead allowed arbitrary offline preprocessing of the design into polynomial-size advice, (4) would give 3-colorability in P/poly, hence \(\mathrm{NP}\subseteq\mathrm{P}/\mathrm{poly}\); one may include advice for the polynomially many possible padded sizes for each input length.

A stronger fixed-family gap follows from Austrin, O'Donnell, Tan and Wright, [New NP-hardness results for 3-Coloring and 2-to-1 Label Cover](https://www.cs.utexas.edu/~wright/papers/coloring.pdf), Theorem 1.4 (also Section 3.1 and Lemma 3.1). Their weighted \(\mathrm{2NLin}(\mathbb Z_3)\) instance consists of inequalities \(x_i-x_j\ne c\), and distinguishing perfect satisfiability from optimum \(<11/12+\epsilon\) is NP-hard for each fixed \(\epsilon>0\). Section 2.1 uses weights; the construction must not silently assume an unweighted simple graph.

For clarity, take \(0<\epsilon<1/12\) and use the source with error slack \(\epsilon/4\). Combine duplicate constraints after orientation. Remove positive tautological loops, renormalizing the remaining weights; this preserves perfect satisfiability and can only decrease the soundness. If a positive always-false loop is present, the source instance is a NO on its promise and we may use a fixed NO consisting of all three forbidden values on one pair, with optimum \(2/3\). If no constraints remain in the tautology-removal case, use a fixed YES. Otherwise there are at most \(S=3\binom N2\) weighted entries. Choose \(K=\lceil4S/\epsilon\rceil\), approximate the weights by integer multiples of \(1/K\) summing to one, taking floors followed by assigning the unused units to largest remainders. Each coordinate error is at most \(1/K\); on every assignment the value changes by at most \(S/K\le\epsilon/4\). The support never leaves the original constraints, hence perfect satisfiability is preserved.

Give every pair \(K\) public slots of six rows, fixed before the instance. Activate the required integer number of slots for each constraint and fill others with inactive observations. We have \(L=K\binom N2\) and \(M=K\). Now choose \(d=C_\epsilon N^4\) with a fixed sufficiently large power-of-two \(C_\epsilon\) so that the design of Section 2 applies uniformly for all \(N\); for fixed rational slack all choices are polynomial-time. For any fixed real slack one can take a smaller rational slack. By (4), if \(C_y\) means the part of \(Td h_0-\gamma D(s)\) independent of \(U(s)\), then
\[
 \frac{\max_s\ell_y(s)-C_y}{3\gamma M}
   =\frac{\max_s U(s)}{M}.
 \tag{5}
\]
Thus distinguishing value one from value below \(11/12+\epsilon\) for (5) is NP-hard. The ratio in (5) concerns an explicit objective after removal of its baseline, not a multiplicative gap in raw log-likelihood, raw likelihood or Hamming distance. This section transfers an existing perfect-completeness gap, not a new PCP theorem.

## 5. Positive-measure robustness does not imply a random-instance theorem

Let \(L_b=\|h'\|_\infty\); it is finite and positive. Perturb each of the \(Td\) circle coordinates by at most \(\kappa/(8Td L_b)\), where \(\kappa=\kappa_b\) in (3) or \(3\gamma\) in the ternary construction, using any smaller positive radius if necessary. By the uniform Lipschitz bound the score of every label changes by at most \(\kappa/8\). A label one or more objective units below the synthetic optimum therefore remains worse than some optimum label by at least \(3\kappa/4\). Every perturbed maximizer, even any label within an additive \(\kappa/2\) of the perturbed optimum, gives a synthetic optimum of the corresponding graph objective.

The radius is inverse-polynomial for fixed \(b\), and also for \(b=\beta/d\). For the latter, \(f_b(x)=1+2b\cos(2\pi x)+O(b^4)\) and \(f_b'(x)=-4\pi b\sin(2\pi x)+O(b^4)\) uniformly as \(b\downarrow0\), by the convergent Fourier sums. Thus \(L_b=O(b)\) and for each fixed nonzero \(c/q\) the peak log gap is \(\Theta_q(b)\), implying \(\kappa/L_b\) bounded below. The neighborhoods are positive-measure under every label because the density is strictly positive. This is only a deterministic robustness assertion. With independently uniform \(a_t\in R_d\), the probability that all \(T\) rows are two-sparse is at most \((\binom d2(q-1)^2/q^d)^T\). The constructed observations also need not be typical. Positivity of the conditional density does not furnish a probability or a distribution-preserving reduction sufficient for average-case hardness.

## 6. Related results and limitations

* [Berlekamp–McEliece–van Tilborg (1978)](https://authors.library.caltech.edu/records/aw9vs-ann16) gave the general code-decoding hardness theorem. [Domínguez Fiallo–Freyre Arrozarena–Piñeiro, ePrint 2023/1064](https://eprint.iacr.org/2023/1064) give general quasi-cyclic syndrome-decoding hardness; the displayed code structure there uses ordinary circulant blocks. Neither stated theorem specifies this particular fixed-design, rank-one negacyclic, two-sparse-unit restriction and likelihood correspondence. The available author abstract of [Wang–Wang–Wang, ePrint 2026/3059](https://eprint.iacr.org/2026/3059) states a distinct binary \(X^n-1\) worst-case syndrome problem, including low equal block weights and fixed index; the comparison here is at the stated abstract scope, not a claim about all consequences of that paper.
* [Liu–Feng–Pan, arXiv:2608.23828v2](https://arxiv.org/abs/2608.23828v2) concern exact Euclidean CVP on integral coefficient lattices of principal cyclotomic ideals, including fixed-family form, and [Feng–Liu–Luo–Pan, arXiv:2611.14334](https://arxiv.org/abs/2611.14334) address exact coefficient-\(\ell_\infty\) SVP on related ideals/modules. The graph code here is finite modulo a fixed prime, the objective is a wrapped likelihood or coefficient-Hamming, and no lattice approximation reduction is used. The proof above is self-contained apart from elementary arithmetic and the cited constraint hardness.
* [Lyubashevsky–Peikert–Regev](https://sites.cc.gatech.edu/fac/cpeikert/pubs/ideal-lwe.pdf) concern randomly generated samples and (approximate) worst-case ideal-lattice reductions. An algorithm guaranteed to optimize every possible deterministic batch as above would have to solve this worst case. That statement neither proves nor disproves a classical polynomial-time algorithm for the standard average-case search problem. It is not an efficient decoder, a claim about a security parameter set, or a concrete cryptosystem result.

The companion Python checker only verifies finite identities (unit products, unique separations, signed shifts, and scores on given toy assignments). It does not optimize labels or decode an instance.
