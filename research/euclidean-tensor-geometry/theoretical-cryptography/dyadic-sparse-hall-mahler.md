# Sparse dyadic Gaussian module generation: the Hall–Mahler limit

A centered discrete Gaussian in a dyadic coefficient basis can have only a bounded expected number of nonzero coefficients per entry. In this regime and for fixed matrix shape, the probability that its columns generate the free module has a finite-type limit. Merely having full row rank at the ramified prime does **not** give the limit: a tight Hall block has a determinant whose unit condition survives in the asymptotic law. The exact additional condition is a unique colored perfect matching in the maximal tight block.

**Scope and comparison.** This addresses the column-generation ingredient of [Albrecht–Felderhoff–Lai–Lapiha–Woo, §3, in particular Corollary 3.9](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), not their kernel smoothing or leftover-hash theorem. Related earlier work is [Micheli–Weger](https://arxiv.org/abs/1803.08785) for densities as boxes grow in a fixed number field, and [Nguyen–Wood, §2](https://math.osu.edu/~nguyen.1261/cikk/CL-Laplacian.pdf) for growing-rank random integer matrices. Here the number-field degree grows, the row and column counts are fixed, and the individual ring entries retain only a bounded expected number of active coefficients. The wider coefficient range of the [earlier dyadic generation note](dyadic-subfield-generation.md) does not reach this Poisson regime. [Düzlü–Gargava–Tairi, ePrint 2026/2180](https://opencryptology.org/2026/2180) studies joint generation and kernel smoothing including coefficient width one; here \(t_n\to0\) and no smoothing claim is made. Ordinary local rank, Hall decomposition, and Mahler convergence are used as ingredients; the new statement is the generation limit in the model below. No kernel-smoothing bound, preimage sampler, or cryptographic implication is asserted.

## 1. Model and exact limit

Take \(n\to\infty\) through powers of two and set \(R_n=\mathbb Z[\zeta]\), \(\zeta\) a primitive \(2n\)-th root. Fix positive integers \(r,m\). Each entry of the \(r\times m\) matrix \(X\) has \(n\) independent integer coefficients with mass proportional to \(\exp(-\pi a^2/t_n^2)\), all entries independent. This is the centered canonical spherical discrete Gaussian with width \(\sqrt n\,t_n\), since the unscaled canonical Gram matrix of the powers of \(\zeta\) is \(nI\). Assume
\[
 n\exp(-\pi/t_n^2)\longrightarrow \lambda\in(0,\infty).
\]
Write \(\mu=2\lambda\). Define the following predicate \(\mathsf{Good}(L)\) of an \(r\times m\) nonnegative integer array \(L=(\ell_{ij})\).

1. Make the bipartite graph of rows and columns with an edge \((i,j)\) when \(\ell_{ij}>0\). If any row set has fewer neighbors than its size, reject. Let \(S_*\) be the union of all row sets \(S\) with \(|N(S)|=|S|\), including the empty set, and \(T_*=N(S_*)\). On a graph that passed the inequalities, \(S_*\) is itself tight.
2. In the square block of rows \(S_*\) and columns \(T_*\), give edge \((i,j)\) exactly \(\ell_{ij}\) colors. Require **exactly one** perfect matching including its edge colors. The empty block has one empty matching. Equivalently, the square block has a unique uncolored perfect matching, and each of its matched edges has count one.
3. On the complementary rows and complementary columns, take the matrix \((\ell_{ij}\bmod 2)\). Require full row rank over \(\mathbb F_2\); a matrix with no rows passes.

Then, for independent \(L_{ij}\sim\operatorname{Pois}(\mu)\),
\[
 \lim_{n\to\infty}\Pr\!\left(XR_n^m=R_n^r\right)
 =\Pr\big(\mathsf{Good}(L)\big). \tag{1}
\]
Only the four entry types zero, one, positive even, and odd at least three matter in this finite probability. There is also a fixed-type version: choose a fixed array \(L\), give entry \((i,j)\) exactly \(\ell_{ij}\) uniformly chosen distinct coefficient positions, and give each such position an independent uniform sign in \(\{\pm1\}\). Independently across entries, this model satisfies
\[
 \Pr(XR_n^m=R_n^r\mid L)=\mathbf1_{\mathsf{Good}(L)}
                   +O_{L,r,m}(1/\log n). \tag{2}
\]
This denotes the fixed-type experiment, not conditioning on a positive-probability event in a limiting continuous model. Neither the constants in (2) nor (1) are asserted uniformly for a growing matrix shape.

In rank one put \(a=(1-e^{-2\mu})/2\), \(p_0=e^{-\mu}\) and \(p_1=\mu e^{-\mu}\). For \(r=1\), the answer in (1) is
\[
 1-(1-a)^m-mp_0^{m-1}(a-p_1). \tag{3}
\]
Indeed with at least two active columns the graph is strict Hall, so at least one odd count suffices in the limit. With only one active column its count must be exactly one. In the square \(2\times2\) case the answer is \(2p_1^2(2p_0-p_0^2)\): the two possible diagonal matchings contribute disjoint cases, with both matching counts equal to one and at least one of the two other entries absent.

## 2. Tight-block decomposition

With Hall's inequalities, the union of two tight sets is tight: neighborhood cardinality is submodular, so
\[
 |N(S\cup T)|+|N(S\cap T)|\le |N(S)|+|N(T)|
 =|S\cup T|+|S\cap T|.
\]
Hall's lower bounds force both inequalities to be equalities. Thus \(S_*\) is tight, and permuting the matrix puts it in the form
\[
 X=\begin{pmatrix}B&0\\ C&D\end{pmatrix},\qquad
 B=X[S_*,T_*],\quad D=X[S_*^c,T_*^c]. \tag{4}
\]
For any nonempty subset \(U\) of the residual rows, its neighbors outside \(T_*\) number at least \(|U|+1\). Otherwise Hall applied to \(S_*\cup U\) either fails or produces a larger tight set. Call this the **strict Hall** condition. If the initial Hall test fails, row rank over the number field is impossible for that zero pattern.

Over a commutative ring, (4) is surjective if and only if \(B\) is invertible and \(D\) is surjective. Projecting to the top coordinates gives necessity of square surjectivity of \(B\), which implies invertibility by determinants. After using the invertible \(B\) to eliminate the first coordinates, the bottom coordinates range over the image of \(D\); equivalently the lower-left block can be removed by an invertible row operation. Empty blocks cause no exception. Fixed entry counts in \(B\) and \(D\) leave their random choices independent.

## 3. Strict Hall eliminates all odd prime-ideal obstructions

Fix an entry array and let \(b\ge1\) upper-bound its positive counts. In an odd residue field \(R_n/\mathfrak p\), the image of \(\zeta\) has order \(2n\), since its \(n\)-th power is \(-1\) in odd characteristic and \(n\) is a power of two. Consequently every odd prime-ideal norm is at least \(2n+1\).

**One-entry anti-concentration.** For a positive-count entry of count \(\ell\), order its \(\ell\) positions uniformly at random. Condition on all but one ordered position and their signs. The last term ranges uniformly over \(2(n-\ell+1)\) distinct signed roots, both in the number field and in every odd residue field. Hence the remaining entry has maximum atom at most \(1/[2(n-b+1)]\). Multiplication by a nonzero scalar and addition of an arbitrary specified constant preserve this bound.

Now take a matrix \(D\) on any fixed strict Hall shape, with independent entries as above. Suppose its rows are dependent modulo an odd prime ideal. Among nonzero left-kernel vectors pick one with minimal row support \(S\), of size \(k\ge1\). Every proper row subset of \(S\) is independent and the restricted matrix on \(S\) has row rank \(k-1\). There is a set \(J\) of \(k-1\) columns (necessarily neighbors of \(S\) if nonempty) such that \(D[S,J]\) has rank \(k-1\) there. The signed cofactors \(c_i\in R_n\), \(i\in S\), of this \(k\times(k-1)\) matrix give a nonzero relation on its columns modulo that ideal, and each \(c_i\) is nonzero modulo that ideal: its nullspace there is one-dimensional and the minimal relation uses all of \(S\). For \(k=1\), use the empty column set and cofactor \(1\).

It suffices to union over the finitely many possible choices \(S,J\). For each preselect two distinct test columns \(j_1,j_2\) in \(N(S)\setminus J\), which exist by strict Hall. Expose the anchor columns \(J\). If any \(c_i\) vanishes identically, this anchor cannot witness one of the minimal-support relations. Otherwise let \(\beta=\sum_{i\in S}c_i D_{ij_1}\). Column \(j_1\) contains a positive-count entry on \(S\), and its corresponding \(c_i\ne0\), so the anti-concentration bound over the number field gives
\[
 \Pr(\beta=0\mid D[S,J])\le \frac{1}{2(n-b+1)}.
\]
Once column \(j_1\) has been exposed, if \(\beta\ne0\), every candidate prime ideal divides \((\beta)\). Each conjugate of every positive-count entry has absolute value at most \(b\), and \(\beta\) is a signed determinant of size \(k\). Thus
\[
 \#\{\mathfrak p\text{ odd}:\ \beta\in\mathfrak p\}
 \le\frac{\log|\mathrm N_{K_n/\mathbb Q}(\beta)|}{\log(2n+1)}
 \le\frac{n\log(k!b^k)}{\log(2n+1)}. \tag{5}
\]
The first inequality uses unique ideal factorization, including each distinct factor at least once. Discard candidates where any cofactor vanishes modulo the prime, since those cannot witness the anchor. For every remaining candidate the fresh column \(j_2\) has \(\Pr(\sum_i c_i D_{ij_2}=0\bmod\mathfrak p)\le1/[2(n-b+1)]\), by using any active entry on \(S\) and the same anti-concentration at that prime. The union bound and (5), followed by the finite union over anchors, give probability \(O_{L,r,m}(1/\log n)\) of failure at **any** odd prime ideal. The proof counts prime ideals and does not require factoring \(\beta\) or constructing a preimage.

The only prime ideal over 2 has residue field \(\mathbb F_2\) and sends \(\zeta\) to \(1\), since \(Z^n+1=(Z+1)^n\bmod2\). The matrix reduced there is deterministically \((\ell_{ij}\bmod2)\). A matrix over \(R_n\) is surjective if and only if it has full row rank modulo every maximal ideal: the full-row minors generate the unit ideal exactly when none of the maximal ideals contains them all, and the adjugate identities for these minors then give a right inverse. We conclude that for a strict Hall array the residual parity-rank test is necessary, and is sufficient up to \(O_{L,r,m}(1/\log n)\).

## 4. Square bottlenecks and positive Mahler measure

For a fixed square count array with a perfect matching, attach a distinct variable \(z_{ijh}\) to every colored edge. Form the determinant polynomial
\[
 P(z)=\det\!\left(\sum_{h=1}^{\ell_{ij}}z_{ijh}\right).
\]
Each colored perfect matching contributes one distinct monomial with coefficient \(+1\) or \(-1\). Edges not in any perfect matching are unused. Delete them, take the connected components of the remaining colored bipartite multigraph, and permute rows and columns. These components are balanced, because each has a perfect matching induced by any full matching. The determinant is then, up to an overall sign, the product of the component polynomials. Every edge retained in a component occurs in some matching of that component, and any combination of component matchings gives a full matching.

Each component polynomial \(Q\) is irreducible over \(\mathbb C\) in its ordinary polynomial ring. Here is a direct factor argument. It is multiaffine, so in a factorization any variable appears in at most one factor (degree in a variable adds under multiplication in a polynomial domain). The polynomial is homogeneous of degree one in the group of variables of any row, and separately of any column. In a factorization both factors are homogeneous with respect to each such grading, because smallest and largest degrees add under multiplication; the resulting degree spread is zero. Therefore the variables of each row must all lie in the same factor, and so must the variables of each column. Connectedness forces all variables into one factor. A single colored edge contributes just its variable, which is a unit in the Laurent polynomial ring.

For any non-monomial component every variable occurs both with exponent zero and with exponent one: otherwise it would divide \(Q\), contradicting irreducibility. Its reciprocal polynomial after clearing negative exponents is \(Q^*(z)=(\prod z_{ijh})Q(z^{-1})\). A Laurent association of \(Q^*\) and \(Q\) would have no shift of the exponent box, so the variable supports of their monomials would be closed under complement. Because each monomial uses exactly one variable of every row and column, every row and column would then be incident to exactly two colored edges. A connected finite bipartite multigraph of that degree is a cycle, allowing a two-edge cycle from parallel colors. It has exactly two colored perfect matchings. Conversely, in such a cycle the two matching monomials are complementary and the polynomial is a reciprocal binomial up to sign, since the coefficients are \(\pm1\).

Thus all components are of three types:
* A single edge gives a Laurent monomial unit.
* A cycle gives a binomial \(\pm(M_1\pm M_2)\) whose zero set in the algebraic torus is a torsion coset. Its unit-torus zeros are Zariski-dense in that coset, as seen by an integral torus coordinate change sending the primitive exponent difference to the first coordinate. Jensen's formula gives logarithmic Mahler measure zero.
* Any other component is irreducible and not reciprocal. Its torus zero set lies in the intersection of \(Q=0\) and \(Q(z^{-1})=0\), since its coefficients are real. These Laurent polynomials have no common irreducible factor, making the Zariski closure of that intersection of codimension at least two. In particular the polynomial is atoral. Its logarithmic Mahler measure is strictly positive: a nonzero integral Laurent polynomial has nonnegative logarithmic Mahler measure, and the [multivariate Kronecker theorem of Boyd, Lawton and Smyth](https://www.sciencedirect.com/science/article/pii/0022314X81900330) characterizes measure zero by generalized cyclotomic factors, excluded by this nonreciprocal irreducible form. Equivalently, its irreducible torus hypersurface cannot be a torsion coset. The same positivity implication is used in [Dimitrov–Habegger, proof of Corollary 1.4](https://arxiv.org/abs/1909.06051).

In every case the polynomial is essentially atoral in the sense of [Dimitrov–Habegger](https://arxiv.org/abs/1909.06051), as is their product \(P\), whose torus zeros form the corresponding union. Write \(E\) for the number of variables after unused edges are removed. In our fixed-type experiment evaluate the variables at \(\xi_\ell=\varepsilon_\ell\zeta^{a_\ell}\), \(\ell=1,\ldots,E\). To check the hypothesis of their Theorem 1.1, include the unused variables if needed and regard all exponents before enforcing distinct positions as independent uniform \(u_\ell\in\mathbb Z/(2n)\), with \(\xi_\ell=\zeta^{u_\ell}\). The restriction to distinct positions within each entry is exactly conditioning on no within-entry equality modulo \(n\), which has probability \(1-O_L(1/n)\); this representation also follows by ordering each entry's positions uniformly. For any nonzero integer vector \(c\) on the \(E\) used variables with \(\|c\|_\infty\le H\), the probability of \(\sum c_\ell u_\ell=0\bmod 2n\) before conditioning is
\[
 \frac{\gcd(2n,c_1,\ldots,c_E)}{2n}\le \frac{H}{2n}.
\]
A union bound, then division by the conditioning probability, gives
\[
 \Pr\big(\delta(\xi)\le H\big)
 \le \frac{(2H+1)^E H}{2n(1-O_L(1/n))},\qquad
 \delta(\xi)=\min_{c\ne0:\ \xi^c=1}\|c\|_\infty. \tag{6}
\]
Take \(H=\lfloor n^{1/(2(E+1))}\rfloor\); then the right side is \(O_L(n^{-1/2})\).

Dimitrov–Habegger's Theorem 1.1 gives, as this shortest relation size grows, nonzero evaluation throughout the Galois orbit and convergence of its average of \(\log|P|\) to the logarithmic Mahler measure \(\mathfrak m(P)\), with a fixed power-saving error in \(\delta\). All coefficients here are rational. Averaging over the \(n\) embeddings of \(K_n=\mathbb Q(\zeta)\) is the same as averaging over that orbit, because the restriction map to the Galois group of the field of the tuple is surjective with equal fibers. Signs are absorbed in the exponents \(u_\ell\). Hence, with probability \(1-O_L(n^{-1/2})\),
\[
 \frac1n\log|\mathrm N_{K_n/\mathbb Q}(\det B)|
       =\mathfrak m(P)+O_L(n^{-c_L}) \tag{7}
\]
for some \(c_L>0\), in every nonempty square block admitting a matching. In particular if a component is nonreciprocal, the norm is exponentially large with high probability. This is a statement for fixed colored graph and growing field degree.

The criterion for \(B\) now follows:
* If there is one colored perfect matching, \(\det B\) is a signed product of roots of unity for every sample and is a unit.
* If the number of colored perfect matchings is even, \(\det B\equiv P(\mathbf1)=0\bmod\mathfrak p_2\), so it is never a unit.
* If there are multiple colored perfect matchings and their number is odd, no allowed component is a two-matching cycle (whose even count would make the full matching count even). At least one component is not a single edge, thus nonreciprocal, and (7) implies \(\det B\) is not a unit with probability \(1-O_L(n^{-1/2})\) for large \(n\).

This proves the bottleneck test without treating parity as sufficient for square matrices. A finite example is the rank-one square entry \(1+\zeta_{16}+\zeta_{16}^3\): its coefficient count is odd, but its absolute norm is 17. The finite verifier checks the integer determinant giving this norm.

## 5. Gaussian counts and verification

With \(w_n=e^{-\pi/t_n^2}\) the scalar normalization is \(1+2w_n+O(w_n^4)\). The chance of absolute coefficient at least two is \(O(w_n^4)\), and all \(rmn\) coefficients avoid this with probability \(1-O(rmnw_n^4)\to1\). Conditional on this event, coefficients remain independent and have probabilities \(w_n/(1+2w_n)\) at each of \(\pm1\). Counts therefore have independent binomial laws with parameters \(n\) and \(2w_n/(1+2w_n)\), tending in total variation to independent \(\operatorname{Pois}(2\lambda)\) for the fixed matrix shape. Conditional on each count, positions are uniform and signs independent. Equations (4), the strict Hall bound and the bottleneck criterion give (2). To pass to (1), restrict first to a finite set of count arrays with limiting probability arbitrarily close to one, apply (2) there, then remove the restriction. This avoids interchanging an unproved uniform asymptotic over unbounded counts.

The companion `verify-dyadic-sparse-hall-mahler.py` is an exact finite check of the combinatorial and algebraic steps and the low-rank formulas. It uses only Python's standard library. It does not simulate or claim to verify the Galois asymptotics numerically; those use the cited theorem. No real-system inputs, cryptographic instances or practical scheme parameters are involved.
