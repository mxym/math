# A fractional-support obstruction for Ramsey multiplicity optimizers
Research note for review, 18 Nov 2026. No claim of determining the multiplicity constant or of priority; the kernel tensor mechanism is due to Csóka–Hubai–Lovász.

Let $W:X^2\to[0,1]$ be a symmetric measurable graphon on a standard atomless probability space, and $t(F,W)=\int_{X^{V(F)}}\prod_{uv\in E(F)}W(x_u,x_v)\,dx$. Set $M_F(W)=t(F,W)+t(F,1-W)$, $U=\min(W,1-W)$, and $P=1_{\{0<W<1\}}$. The topology here is graphon cut distance (up to weak isomorphism); graphons on products are valid refinements of the original model.

**Theorem.** If a finite simple graph $F$ contains a $K_4$, then at any cut-local minimizer of $M_F$ one has $t(F,P)=0$. This remains true if the optimization fixes the degree distribution: each strict improvement we use preserves the old degree at every point of every fiber, up to null sets. In particular the fractional support of every minimizer for the $K_4$ Ramsey problem is $K_4$-free and occupies at most $2/3$ of the pair area. No positive-measure diagonal block of a step minimizer can be strictly fractional. These conclusions are necessary conditions, not a characterization. The same proof works when the red and blue terms have arbitrary fixed positive weights.

**Balanced seed.** The first factor below is exactly the looped four-vertex example in Claim 1 of [Csóka, Hubai & Lovász, proof of Theorem 3.1](https://pmc.ncbi.nlm.nih.gov/articles/PMC10087361/). For uniform types $i,j\in[4]$ take $L_{ij}=1-2\mathbf 1_{i=j}$. For independent uniform types $a,b\in[9]$ take $S_{ab}=(9\mathbf 1_{a=b}-1)/8$. Set $V=L\otimes S$. This symmetric kernel is bounded in absolute value by one, and all its row integrals vanish. Directly
$$
t(C_4,L)=1/4,\quad t(K_4,L)=-1/2,\qquad
t(C_4,S)=1/512,\quad t(K_4,S)=21/16384 .
$$
These identities can all be verified by at most $9^4$ terms, as in kernel_check.py. For example, for the clique, classify assignments by the five set partition types of 4; for the cycle, use the eigenvalues of the normalized matrix and the trace of its fourth power. Hence $a=t(C_4,V)=1/2048$, $t(K_4,V)=-b=-21/32768$, and $b/a=21/16>1$. For odd $m$ let $V_m=V^{\otimes m}$. The same two signed densities are $a^m$ and $-b^m$ by Fubini; all its row integrals remain zero. A leaf edge of a nonempty graph makes its density in $V_m$ vanish, by integration over the leaf.

**Four vertices.** On the product space, put $W_\pm((x,z),(y,z'))=W(x,y)\pm h U(x,y)V_m(z,z')$ for $0<h\le1$. The definition of $U$ keeps both in $[0,1]$; integrating out $z'$ shows exact preservation of degrees and the cut distance to the old kernel is at most $h$ under the natural pullback coupling. For a cycle $Q$ spanning the four labeled vertices of $K_4$, write $e,f$ for its two omitted diagonals and abbreviate edge evaluations by subscripts. Set
$$
 A=\sum_Q \int \left(\prod_{g\in E(Q)}U_g\right)[W_eW_f+(1-W_e)(1-W_f)],\qquad T=t(K_4,U).
$$
There are three terms, and $0\le A\le3/16$, since $U\le1/2$ and the bracket is at most one. Expand each of the six factors in the two color terms and average over $\pm$. Odd terms cancel. In every even term with a leaf, the independent fiber integral is zero. The only remaining nonconstant even edge subsets are the three 4-cycles and the whole clique, giving the exact identity
$$
 \frac{M_{K_4}(W_+)+M_{K_4}(W_-)}2-M_{K_4}(W)
 = h^4 A a^m - 2 h^6 T b^m .
$$
When $t(K_4,P)>0$, the nonnegative product of the six $U_g$'s is positive on a set of positive measure, so $T>0$. For any fixed $h>0$, large odd $m$ makes the right-hand side negative. At least one of the two graphons is strictly better, even for arbitrarily small $h$. Finally, an $n$-vertex sample from $P$ is almost surely $K_4$-free, so has at most $n^2/3$ edges by Turán. Taking expectations, dividing by $\binom n2$ and passing to the limit proves the area bound.

**Quantified stability of this necessary condition.** Let $c_4=\inf_W M_{K_4}(W)$, $C=3/16$, $s=\log(1/b)/\log(b/a)>0$. Then
$$
 M_{K_4}(W)-c_4\ \ge\ b^2 T (T/C)^s.
$$
For $T>0$ put $h=1$ and take the first positive odd $m\ge\log(C/T)/\log(b/a)$. Since $T\le1/64<C$, this $m$ is less than the threshold plus 2. The expected decrement is at least $T b^m$, proving the stated bound. For any fixed $0<\eta\le1/2$ this forces the $K_4$-density of $1_{\{\eta\le W\le1-\eta\}}$ to vanish along near-minimizing sequences, by comparison with $T/\eta^6$. No control on all of $\{0<W<1\}$ for merely approximate minimizers is asserted.

**General graph.** Give each fiber an additional independent uniform coordinate $u$ and replace $V_m$ by $V_m(z,z')\mathbf1_{u\le\delta}\mathbf1_{u'\le\delta}$. Each term for a perturbed edge set $J\subseteq E(F)$ picks up $\delta^{v_+(J)}$, where $v_+$ counts its nonisolated vertices. Average the two signs again. Nonempty even graphs with no leaf on at most four nonisolated vertices are precisely $C_4$ and $K_4$. At order $\delta^4$ the coefficient consequently equals $h^4a^m A_F-h^6 b^m B_F$, where for a selected $J$ of the indicated type the nonnegative summand of $A_F$ or $B_F$ is
$$
 \int \left(\prod_{e\in J}U_e\right)
 \left[\prod_{e\notin J}W_e+\prod_{e\notin J}(1-W_e)\right].
$$
If $t(F,P)>0$, then $t(F,U)>0$. As $F$ contains a 4-clique, at least one $K_4$ summand is present, each at least $2t(F,U)$ since $U\le W,1-W$. Thus $B_F>0$. For fixed $h>0$ first choose large odd $m$ to make the order-4 coefficient negative. Every remaining term is bounded in absolute value by $2\delta^5$, and there are at most $2^{|E(F)|}$ subsets. Taking $\delta>0$ small completes the argument. In fact the proof gives the stronger weighted assertion $B_F=0$ at a local minimum. For more than two colors, varying a fixed color pair with opposite perturbations gives an analogous pairwise-overlap statement; calling the union of pairwise overlaps $F$-free does not follow.

**Relation to earlier work and limits.** [Csóka, Hubai & L. Lovász, Locally common graphs](https://arxiv.org/abs/1912.02926) already established that any graph containing a 4-clique is not locally common via a balanced signed kernel, its tensor powers, and vertex localization. This is not a rediscovery claim for their theorem or their perturbation mechanism. Here the perturbation is masked by an arbitrary (possibly inhomogeneous) graphon's fractional capacity; averaging the two perturbation signs removes odd terms even when the two base colors are not identical. This gives the support obstruction, preservation of degrees and the modulus above. Searches of primary Ramsey multiplicity and local-commonality papers and indexed text under “fractional support”, “random part”, “random-free”, “minimizers” and variations have not located this precise arbitrary-background statement; this is not a priority determination. [Parczyk, Pokutta, Spiegel & Szabó](https://doi.org/10.1007/s10208-024-09675-6) give modern extremal evidence and spectral/computational upper bounds. The exact $K_4$ Ramsey multiplicity remains unknown.

**Companion cubic stationarity condition (from balanced sign refinement).** For almost every triangle of fractional pairs at a cut-local $K_4$ minimizer,
$$
 S(x,y,z):=\int [W_{xu}W_{yu}W_{zu}-(1-W_{xu})(1-W_{yu})(1-W_{zu})]\,du=0.
$$
Indeed, for any symmetric $|A|\le U$, perturb by $hA(x,y)st$ with independent uniform vertex signs. Only Eulerian perturbed edge sets survive. Their nonempty possibilities are a triangle and a 4-cycle, so the change is
$4h^3\int S(x,y,z)A_{xy}A_{yz}A_{zx}+O(h^4)$.
Both signs of arbitrarily small $h$ are allowed, hence the displayed cubic integral vanishes. Take $A$ equal to $U$ on the pairs that go between three arbitrary pairwise disjoint measurable sets, zero elsewhere. The integral is six times the integral of $S U_{xy}U_{yz}U_{zx}$ over their ordered product. Apply this also to all measurable subsets of each of three disjoint dyadic cells. These rectangles generate the product sigma algebra there; a countable union of triples of disjoint cells covers almost every triple. Thus the integrand vanishes almost everywhere. The finite balanced-refinement identity was already used by Van Seters–Jothimani and Koshta (citations in README.md); the triangle packing in our certificate exploits violations of this condition at the SK input, independently of the 4-clique support theorem.
