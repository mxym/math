# Prior work, consequences and verification

## What this note does and does not establish

[Song–Wang–Tomamichel–Fang, Eq. (2)](https://arxiv.org/html/2609.37240v2) asks for exact majorization at every blocklength for **every** input under identical depolarizing noise. Its Theorems 1 and 4 give an approximate comparison and an exact shifted log-determinant ordering, respectively; neither is the unrestricted exact comparison. [King's maximal output Schatten norm theorem](https://arxiv.org/abs/quant-ph/0204172) is not a Ky Fan ordering either. Our direct proof handles a restricted family of inputs, allowing unequal local noise strengths. It gives no conclusion on the unrestricted conjecture beyond the stated consequences.

The graph-basis treatment of local Weyl errors and stabilizer normal forms are established techniques: [Aolita et al., noisy graph states](https://doi.org/10.1103/PhysRevA.82.032317), [qudit noisy stabilizer formalism](https://doi.org/10.1103/gqfw-x72s), [Van den Nest et al. for qubits](https://arxiv.org/abs/quant-ph/0308151), and [Bahramgiri–Beigi, Lemma 7, for odd prime dimensions](https://arxiv.org/pdf/quant-ph/0610267). In the erasure case the graph-basis identification reduces the comparison to [Alhejji–Knill's classical spin alignment](https://arxiv.org/html/2307.06894v3), not a new classical spin-alignment theorem.

**Weyl-channel priority qualification.** [Amosov (2024), Eq. (8), Thm. 2 and Eq. (17)](https://arxiv.org/pdf/2401.05104) formulates a tensor-product majorization theorem for group-generated mixed-unitary channels under coset-ordering hypotheses. Its scope is close enough that we do **not** claim priority for the graph-state statement. A local depolarizing Weyl law has one exceptional identity weight. When comparing *different* cosets, the usual computational-basis cosets can be sorted; an ordering condition also applied *within* an equal-total coset would be more restrictive. The precise applicability of the earlier theorem to the tensor products considered here has not been settled by this review. Our proof does not use an implication from single-channel to tensor-channel majorization.

See also [Amosov (2025), on majorization by probability distributions](https://doi.org/10.3103/S1066369X25700070) and [Amosov–Ryskin (2025), conditions for mixed-unitary channels](https://doi.org/10.1134/S1995080225607945). In particular, ordering of an entire tensor-product Weyl law is not automatic from an ordering of its local factors: if the identity error has weight $h$ and each other error weight $\ell$, with $h>\ell>0$, then at two equal sites the highest-total phase-error coset contains a weight $\ell^2$, while a lower-total coset contains $h\ell>\ell^2$. No claim is made that this observation decides every possible application of earlier work. Independent specialist review of the literature is still needed.

## Two all-input consequences of prior work, not new results

**Two identical uses, any local dimension.** The positive-contraction case is [Fujiwara–Hashizumé](https://doi.org/10.1016/S0375-9601(02)00735-1) as cited in [SWTF §1](https://arxiv.org/html/2609.37240v2). For negative contraction $t=1-p$, [Fannes–Haegeman–Mosonyi–Vanpeteghem, §3](https://arxiv.org/pdf/quant-ph/0410195) already supply the needed comparison in the proof, although their abstract highlights entropy. Their transpose-depolarizing channel and the depolarizing channel differ by an output transpose; for two uses this is a full transpose and preserves the spectrum. For a pure input in Schmidt form, with coefficients $s_i$ in its reduced **density matrix**, they compare the block on $\operatorname{span}\{|ii\rangle\}$ to its value at a simplex vertex by full eigenvalue majorization (their phrase is “more mixed”). The range $-2/(d^2-2)\le t\le0$ over which the comparison holds includes the ordinary depolarizing range $-1/(d^2-1)\le t\le0$. On the complementary block the eigenvalues for $i\ne j$ are
$$
 \eta_{ij}(s)=\left(\frac{1-t}{d}\right)^2+\frac{t(1-t)}d(s_i+s_j).
$$
This vector is a convex combination of permutations of $\eta(e_1)$ by affinity in $s$ and the symmetry of the simplex vertices. It too is majorized. Taking the direct sum of the two doubly stochastic comparisons and then using convexity covers arbitrary inputs. The independent verifier checks finite examples but is not the source of this result.

**Three identical qubit uses.** For $p\le1$, write $S_j=\sum_{|J|=j}\rho_J\otimes I_{J^c}$ and $S_j^*$ for the same sum from $|000\rangle$. The output is $\sum_j (1-p)^j(p/2)^{3-j}S_j$. For $j=0,3$, $S_j\prec S_j^*$ is immediate; for $j=1$, a tensor product of local random-unitary channels taking $|0\rangle\langle0|$ to each one-site marginal sends $S_1^*$ to $S_1$. The only nontrivial layer, $j=2$, is precisely [Song–Chen, Prop. 3, Eq. (15)](https://arxiv.org/html/2603.25410v1) at equal weights, multiplied by three. On computational strings with $z$ zeros the reference entries are $\binom zj$, hence they sort in a common order for all $j$. For each $k$, Ky Fan subadditivity bounds the top-$k$ sum of the output by the sum of the weighted reference top-$k$ sums; with this common order that is exactly the reference top-$k$ sum. For $1<p\le4/3$, $D_p=F\circ D_{2-p}$ with $F(X)=\sigma_yX^T\sigma_y=\operatorname{Tr}(X)I-X$. Applying $F$ to **all** sites amounts to full transpose and unitary conjugation, so the same inequality follows. This deduction is credited to Song–Chen's compatible two-body inequality; it does not extend their proposition to arbitrary mask weights or arbitrary $Q$.

## Independent internal AI cross-check

One independent AI review examined the sign of the graph label, the common-order requirement at endpoints, convexification, composite-dimensional graphs, the two-site thresholds, and the use of compatible marginals. It identified the two-use negative range as a prior-work consequence. This is not external peer review or a guarantee of priority.

The published check file for this draft is [check.py](check.py). Run `python3 -B -O check.py` with SymPy 1.14. It uses mandatory exceptions and begins with a false majorization which must be rejected. An earlier preliminary script used removable Python `assert` statements: its optimized-mode run verified nothing and its case totals are **excluded**.

The independent run, with a fixed seed, gives:

| Test | Cases |
|---|---:|
| Graph spectra under independent local channels | 640 |
| Graph spectra under correlated erasure masks | 192 |
| Ordered-prefix comparisons in the preceding two sets | 23,244 |
| Two-use rational characteristic-polynomial checks | 270 |
| Three-qubit spectra with exact root isolation | 21 |

The graph checker independently expands the state in stabilizer characters indexed by $r$. Each term acquires a factor $1-p_i$ on site $i$ iff $(r_i,(\Gamma r)_i)\ne(0,0)$; for erasure masks it survives iff the mask misses those sites. Averaging characters under multiplication by units modulo $d$ gives integer Ramanujan sums, so the resulting spectra are checked without approximating roots of unity. Tested dimensions include composite $d=4,6$. The two-use checker uses a rank-one determinant polynomial and exact sign variation at the reference spectral thresholds. The three-qubit check constructs the actual complex rational output, isolates every real root of its characteristic polynomial in rational intervals, and uses the worse endpoint to bound each spectral prefix. These finite tests are cross-checks, not proofs of the infinite families.
