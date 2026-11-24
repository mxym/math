# Growing-seed rank and many cyclic SCCs at targets with moving small radical

This is a structural restriction on genuine all-composite prime-factor closures. It does not prove the existence of any Goldbach exception, or prove a prime-pair representation.

**Theorem.** Fix real \(b,\theta,c>0\) with \(b+2c+\theta<1\), and a fixed exponent \(B_0>0\). Write \(L=\log N\) for an even target, and suppose \(\operatorname{rad}(N)\le L^b\) (allowing a fixed multiplier does not change the conclusion). Set
\[
 s=\Big\lfloor c\,\frac{\log L}{\log\log L}\Big\rfloor .
\]
Let \(P\) be any \(s\) distinct odd unit prime labels of value at most \(L^{B_0}\). Suppose a genuine forward-closed all-composite factor set \(C\) contains \(P\), with \(k=|C|\le L^\theta\): all labels are odd primes coprime to \(N\) and \(<N-1\), and each \(N-x\) has all prime factors in \(C\) and is composite. Write \(A_{ij}=v_{x_j}(N-x_i)\) and \(B=I-A\). Then the \(s\) coordinate classes at the chosen seed labels are linearly independent in \(\mathbb Q^C/\operatorname{row}_{\mathbb Q}(B)\) for all sufficiently large \(N\), uniformly over the varying local prime, seed choices and such closures. In particular \(\operatorname{corank}B\ge s\) and every feedback vertex set of this directed closure has at least \(s+1\) vertices.

The [Kummer sharpening](SmallRadicalGrowingSeedKummer.md) improves the parameter constraint to \(b+c+\theta<1\).

The main distinction from the repository's earlier PrimeOrbitDyadicRank and fixed-\(F\) independence results is that both the local prime divisor of \(N\) and the number of genuine seeds now move. A consequence for bounded individual orbits is given below.

## 1. The moving local prime and its valuation budget

The logarithmic prime-power masses sum to \(L\). Choose \(\ell\mid N\) maximizing \(a_\ell\log\ell\), \(a_\ell=v_\ell(N)\). If \(t=\omega(N)\), then \(a_\ell\log\ell\ge L/t\). By the radical hypothesis \(t=O_b(\log L)\) and \(\ell\le L^b\), hence
\[
 a_\ell\gg_b \frac{L}{(\log L)^2}=L^{1-o(1)}.                    \tag{1}
\]
The estimates allow \(\ell\) to vary at every \(N\). Each original seed is an \(\ell\)-unit.

The local field parameters used for Yu are as follows:

* If \(\ell\equiv3\pmod4\), take \(K=\mathbb Q\), \(d=1\), \(f=1\), \(e=1\).
* If \(\ell\equiv1\pmod4\), take \(K=\mathbb Q(i)\), \(d=2\). The rational prime \(\ell\) splits, so either prime ideal above it has \(f=1,e=1\).
* If \(\ell=2\), take \(K=\mathbb Q(\zeta_3)\), \(d=2,f=2,e=1\): \(X^2+X+1\) is irreducible mod 2 and the quadratic extension is unramified there.

These are exactly the auxiliary-field conditions of Yu (1.2). In all cases the prime ideal valuation on rationals is \(v_\ell\) (unramified), and \(\ell^f\le 4\max(1,L^b)\). In particular there is **no** \(L^{2b}\) loss for an odd moving \(\ell\).

## 2. Short integer relation if the seed classes are dependent

By dependence there is a nonzero rational row-space vector supported only on the seed columns. Choose a maximal independent set of columns among the nonseed ones and add one seed column increasing their rank. Select equally many rows with nonzero augmented determinant and take the signed maximal minors of just the nonseed columns on those rows. Their integral row combination \(u\) vanishes on those columns and hence all nonseed columns, and the added seed coordinate is the nonzero determinant. This is an integer combination, not merely a vector in a saturated lattice.

Let \(D=\max_i\Omega(N-x_i)\le L/\log 3\). Each row of \(B\) has Euclidean norm at most \(\sqrt{1+D^2}\), since its diagonal label is not a factor of its complement. Each seed coordinate of \(u\) is a minor of order at most \(k\), so \(|u_j|\le (1+D)^k\). Map the row vectors multiplicatively modulo \(\ell^{a_\ell}\): each original row has value \(x_i/(N-x_i)\equiv -1\). Therefore
\[
 \Xi=\prod_{p_j\in P} p_j^{2u_j}-1\ne0,\qquad v_\ell(\Xi)\ge a_\ell.
\]
Negative exponents are legitimate for these units. Nonvanishing over \(\mathbb Q\) is unique factorization of the distinct prime labels and \(u\ne0\). The Yu exponent bound may be taken \(\mathcal B=\max(3,2\max_j|u_j|)\), with \(\log\mathcal B=O(k\log L)\).

## 3. The explicit Yu constant, simultaneously in dimension and local prime

Use Kunrui Yu, *p-adic logarithmic forms and group varieties II*, Acta Arith. 89 (1999), 337–378, [DOI:10.4064/aa-89-4-337-378](https://doi.org/10.4064/aa-89-4-337-378), [original paper PDF](https://bibliotekanauki.pl/articles/1390501.pdf). Theorem 1 with (1.9) applies to the \(n\le s\) nonzero exponents, because the rational primes \(\alpha_j=p_j\) have zero local valuation and \(\Xi\ne0\). Use (1.5), (1.8), and the **first** explicit coefficient (1.10); no additional independence assumption (1.11) is needed.

Here is the growth bound directly from (1.10), including its varying-\(\ell\) dependence. In the preceding fields \(e=1,d\le2,f\le2\). Yu's \(\kappa\) in (1.6) has \(\ell^\kappa\le4\) when \(e=1\): the possibilities are \(\ell=2,\kappa=2\); \(\ell=3,\kappa=1\); or \(\ell\ge5,\kappa=0\). The max in (1.10) with nonpositive exponents is at most one; \(\Phi(\mathfrak p)/q_{\mathrm{Yu}}^u\le \ell^f\). The factor \((n+1)^{n+2}\omega_{q_{\mathrm{Yu}}}(n)/(n-1)!\) is at most \(n(n+1)^{n+2}/2^{n-1}\), using the stated bound \(\omega_{q_{\mathrm{Yu}}}(n)\le n!/2^{n-1}\) immediately preceding Theorem 1. The denominator involving \(f\log\ell\) and its last max cost at most a factor \(O(\log(n+2))\), since \(f\log\ell\ge\log2\). All other factors of (1.10) are bounded by an absolute exponential in \(n\). Hence the full coefficient is bounded by
\[
 \ell^f\exp\!\big(n\log(n+2)+O(n)\big)
\]
with an absolute \(O(n)\), uniform over \(\ell\). This reads the dimension cost of Yu's original formula, not a fixed-prime black box.

Here \(h'(\alpha_j)=\max(\log p_j,f\log\ell/d)=O_{B_0,b}(\log L)\). Consequently Theorem 1 gives
\[
 v_\ell(\Xi)
 \le L^b\,\exp\!\big(s\log(s+2)+O(s)\big)
       \big(O_{B_0,b}(\log L)\big)^s\,O(k\log L)
 \le L^{\,b+2c+\theta+o(1)}.
\]
Indeed \(s\log(s+2)\le(c+o(1))\log L\) and \(s\log\log L\le(c+o(1))\log L\), while \(k\le L^\theta\). The strict inequality \(b+2c+\theta<1\) makes this smaller than (1). No dependence is possible, proving the rank result.

## 4. Concrete necessary consequences at a hypothetical Goldbach exception

Such seeds exist for large \(N\) by Bertrand: take one prime in each of \(s\) successive dyadic intervals above \(\lfloor L^b\rfloor+1\); all exceed \(\operatorname{rad}(N)\), hence are unit primes, and their total maximum is \(L^{b+o(1)}\), so one may take \(B_0=b+1\). Other seed families are allowed by the theorem. At a hypothetical exception, all complementary rows of primes reached from them are odd composite and have prime factors still coprime to \(N\) and less than \(N-1\). Thus the joint forward closure is a genuine finite \(C\) of the indicated kind (although it can exceed \(L^\theta\)). If the joint closure already exceeds \(L^\theta\), it is much larger than \(2s+2\) for large \(N\).

When the rank estimate applies, the usual upward forest gives a feedback set of size at most \(\lfloor k/2\rfloor\): each target label \(y\) can have at most one strictly smaller parent (the input is the least positive residue \(N\bmod y\)), so the maximum vertex on any undirected cycle of upward edges would have two smaller parents, impossible. Each smaller two-color shore of a tree component covers its edges, and every directed cycle uses an upward edge. Eliminating vertices outside any feedback set \(F\) in the eigenvalue-one equations gives the first-return matrix on \(F\). In the full closed all-composite graph each of a row's at least two outgoing arcs counted with multiplicity extends to a return (the complement is acyclic and no vertex has zero outdegree), so this matrix has row sums at least two; its \(I-K\) is nonzero, and \(\nu\le |F|-1\). Thus every \(F\) has \(\ge s+1\), and \(k\ge2s+2\). This latter size bound holds even when \(k>L^\theta\) by growth of the threshold.

More concretely, choose any integer \(K\ge2\) with \(sK\le L^\theta\). At a hypothetical exception among the selected seeds one of the alternatives holds:

1. some seed has individual all-composite forward orbit of size \(>K\); or
2. their joint forward closure has at least \(\lceil s/\lfloor K/2\rfloor\rceil\) **distinct singular cyclic strongly connected components**.

In the second case their joint size is at most \(sK\), so \(\nu\ge s\). Each SCC lies wholly in at least one seed's orbit, hence has size at most \(K\). A topological block decomposition bounds \(\nu\) by the sum of nullities of the diagonal SCC blocks \(I-A_{DD}\). An acyclic singleton has nullity zero. For a cyclic block its *internal* upward forest gives an internal feedback set of size at most \(\lfloor |D|/2\rfloor\) and eliminating its acyclic complement gives the same upper bound on block nullity. One may not subtract another one for this internal bound, since some arcs may leave \(D\); no assertion that these singular SCCs are terminal is made. The stated number follows. For fixed \(K\), this lower bound diverges like \(\log\log N/\log\log\log N\), not merely a fixed list of seeds.

This is a necessary structure conditional on a Goldbach failure (or an actually verified all-composite closure). It leaves open unbounded individual orbits, large terminal SCCs, and many small nonterminal singular SCCs; none of these alternatives is ruled out by the theorem. No count of missing prime pairs or existence of a Goldbach exception follows. Relevant prior local input is the existing PrimeOrbitDyadicRank.md and fixed-\(F\) moving-seed result; the present change is the simultaneous growth in the number of seeds and allowable varying local prime at sublinear logarithmic radical.
