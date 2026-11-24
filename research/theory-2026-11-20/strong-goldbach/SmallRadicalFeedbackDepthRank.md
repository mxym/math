# Growing seed rank after exact acyclic elimination

This strengthens [the earlier moving-small-radical theorem](SmallRadicalGrowingSeedKummer.md): the total cardinality of the forward-closed prime-factor set is no longer in the analytic bound. The theorem applies only to genuine all-composite closures, not arbitrary integer matrices or real graph realizations.

## 1. Statement and local hypotheses

Let \(N\) be even, \(L=\log N\), and \(C\) a finite, nonempty set of distinct odd primes \(x_i<N-1\) with \(\gcd(x_i,N)=1\). Suppose every \(N-x_i\) is composite and all its prime factors lie in \(C\). Put \(A_{ij}=v_{x_j}(N-x_i)\) and \(B=I-A\). Arcs are directed from input to prime factor and counted with multiplicity. Let \(P\) be a set of \(s\) seed labels in \(C\); let \(R\supseteq P\) be any retained set such that \(U=C\setminus R\) induces a directed acyclic graph. Write \(r=|R|\). The depth \(h\) is the maximum **number of vertices of \(U\)** in a directed path inside \(U\), or \(0\) if \(U=\varnothing\). In particular, an isolated vertex of \(U\) gives \(h=1\).

Fix \(b,c,\theta,B_0>0\) with \(b+c+\theta<1\). Suppose \(\operatorname{rad}(N)\le L^b\), \(s=\lfloor c\log L/\log\log L\rfloor\), and the \(s\) distinct unit seeds satisfy \(p\le L^{B_0}\). For all sufficiently large \(N\), uniformly over all such choices, the implication is
\[
 r(h+1)\le L^\theta
 \quad\Longrightarrow\quad
 \{[e_p]:p\in P\}\text{ is linearly independent in }
                  \mathbb Q^C/\operatorname{row}_{\mathbb Q}B .
\]
The same implication holds with these alternative local hypotheses: a rational prime \(\ell\mid N\) has \(\ell\le(\log L)^{A_0}\) for a fixed \(A_0>0\) and \(v_\ell(N)\ge L^{1-o(1)}\); seeds \(p\le(\log L)^{B_1}\) for fixed \(B_1>0\) are given; \(s=\lfloor c\log L/\log\log\log L\rfloor\) and \(c+\theta<1\). In this alternative the seed supply is a separate premise. If the local lower bound is stated asymptotically along a family of \(N\), so is the conclusion.

## 2. Exact Schur reduction, preserving the modular relation

As \(U\) is acyclic, \((I-A_{UU})^{-1}\) is an integer matrix: for \(h\ge1\) it equals \(\sum_{j=0}^{h-1}A_{UU}^j\), since a path in \(U\) has at most \(h-1\) arcs. The \(U=\varnothing\) case just omits this block. Set
\[
 B^*=B_{RR}-B_{RU}B_{UU}^{-1}B_{UR}=I-K,\qquad
 K=A_{RR}+A_{RU}(I-A_{UU})^{-1}A_{UR}.
\]
In fact, every lifted row of \(B^*\) is exactly an **integer** row combination of \(B\), as witnessed by
\[
 (I_R,-B_{RU}B_{UU}^{-1})B=(B^*,0)
\]
in the order \(R,U\). Conversely, if \(v=(v_R,0)=\lambda B\) with rational coefficients \(\lambda\), its zero \(U\)-coordinates force \(\lambda_U=-\lambda_R B_{RU}B_{UU}^{-1}\), and hence \(v_R=\lambda_R B^*\). Thus rational row-space dependence among seed coordinates is exactly preserved in both directions, and replacing vanishing rows with the \(B_{UU}\)-rows shows \(\operatorname{corank} B=\operatorname{corank}B^*\). In particular the lifts used for arithmetic do not require dividing or replacing a lattice with its saturation.

The \((i,j)\) entry of \(K\) counts all paths from \(i\in R\) to \(j\in R\) with interior vertices in \(U\), using the product of arc multiplicities. A direct \(R\)-to-\(R\) arc has length 1. A path traversing \(t\) internal \(U\)-vertices has one entering arc, \(t-1\) arcs between them, and one return arc: \(t+1\) total arcs, at most \(h+1\), not \(h+2\). For \(h=0\), the same maximal length 1 covers the direct arcs.

Put \(D=\max_i\Omega(N-x_i)\le L/\log 3\); here \(D\ge2\). For fixed \(i\in R\), unfold the multiplicity-counted choices until first hitting \(R\). Every unfolded branch terminates at \(R\): otherwise, a path kept in finite acyclic \(U\) eventually reaches a vertex with no outgoing \(U\)-arc, but that vertex has at least two outgoing arcs in the full closed graph. The unfolded tree has branching at most \(D\) and depth at most \(h+1\). It has at most \(D^{h+1}\) leaves (pad shorter branches by single-child steps if necessary); hence every row of \(K\) has sum at most \(D^{h+1}\). In particular every row of \(B^*\) has Euclidean norm at most \(M=1+D^{h+1}\).

If the seed coordinates are dependent, there is a nonzero rational row-space vector of \(B^*\) supported on \(P\). Choose a maximal independent set of nonseed columns, of size \(t\), and one seed column extending that set, and select \(t+1\) rows with nonzero augmented determinant. The signed cofactors of the \(t\) nonseed columns give an integer row combination \(u_R\) on these rows, vanishing on every nonseed column and taking a nonzero value at the chosen seed. Both facts follow by expanding the corresponding column determinants. For \(t=0\) the empty cofactor is 1. By Hadamard each \(|u_p|\) is at most \(M^{t+1}\le M^r\). Lift \(u_R\) to \(u=(u_R,0)\) using the displayed integer row identity. For \(a=v_\ell(N)\) and any \(\ell\mid N\), the multiplicative homomorphism \(\mathbb Z^C\to(\mathbb Z/\ell^a\mathbb Z)^\times\) sending \((z_i)\) to \(\prod x_i^{z_i}\) takes original row \(i\) to \(x_i/(N-x_i)\equiv-1\). Thus it maps \(u\) to a sign, even though its integer lifts could have large coefficients. Squaring eliminates the sign, and unique factorization gives
\[
 \Xi=\prod_{p\in P} p^{2u_p}-1\ne0,\qquad
 v_\ell(\Xi)\ge a,\qquad
 \log \mathcal B=O(r(h+1)\log L),
 \quad \mathcal B=\max(3,2\max_{p\in P}|u_p|).
\]
The last bound counts only seed exponents, not coefficients in the lift. Negative exponents are units at \(\ell\), so they cause no issue.

## 3. Moving local prime and analytical comparison

Under \(\operatorname{rad}(N)\le L^b\), choose \(\ell\mid N\) maximizing \(v_\ell(N)\log\ell\). Then \(\omega(N)=O_b(\log L)\), \(\ell\le L^b\), and \(v_\ell(N)\gg_b L/(\log L)^2=L^{1-o(1)}\). The alternative local hypothesis supplies a (possibly varying) \(\ell\) directly.

Use Kunrui Yu, *p-adic logarithmic forms and group varieties II*, Acta Arith. 89 (1999), 337–378, [DOI](https://doi.org/10.4064/aa-89-4-337-378), [original PDF](https://bibliotekanauki.pl/articles/1390501.pdf), Theorem 1 and (1.9)–(1.11). In the notation of that theorem, choose \(K=\mathbb Q\) for \(\ell\equiv3\pmod4\); \(K=\mathbb Q(i)\) for \(\ell\equiv1\pmod4\), where \(\ell\) splits; \(K=\mathbb Q(\zeta_3)\) for \(\ell=2\), which is inert there. These satisfy (1.2), with ramification \(e=1\), field degree at most 2, and residue degree \(f=1\) at odd \(\ell\) and 2 at \(\ell=2\). Thus on rational elements the local normalized valuation is exactly \(v_\ell\). This does not use constants uniform only in a fixed local prime.

For the \(n\le s\) primes of nonzero exponent, condition (1.11) is automatic. Yu's Kummer prime is \(q=2\) at odd \(\ell\) and \(q=3\) at 2. The auxiliary base \(\alpha_0\) is respectively \(-1,i,\zeta_3\) in the listed fields, a maximal \(q\)-power root of unity and not itself a \(q\)-th power in that field. A prime ideal above any nonzero-exponent seed sees the corresponding base with ramification prime to \(q\), sees the other seed bases and \(\alpha_0\) as units, and forces the exponent of that seed to vanish modulo \(q\) in a relation in \(K^\times/(K^\times)^q\). Consequently all bases are independent in that quotient. In a field with the \(q\)-th roots of unity, the Galois multipliers on their chosen \(q\)-th roots form a linear subspace of \(\mathbb F_q^{n+1}\); if proper, a nonzero annihilator gives a root monomial fixed by the entire Galois group, contradicting that class independence. The extension therefore has degree \(q^{n+1}\), exactly (1.11).

One may therefore divide the coefficient (1.10) by \(\omega_q(n)\). Its remaining dimension factor \((n+1)^{n+2}/(n-1)!\) is \(\exp(O(n))\); all further factors together cost at most \(\ell^f\exp(O(n))\) since \(e=1\), degree and \(f\) are at most 2, \(\ell^\kappa\le4\), \(\Phi(\mathfrak p)\le\ell^f\), and the logarithmic max and denominator cost \(O(\log(n+2))\). The modified height (1.5) for a rational seed \(p\) is \(\max\{\log p,f\log\ell/[K:\mathbb Q]\}\). In the radical case it is \(O_{b,B_0}(\log L)\) and in the alternative local case \(O_{A_0,B_1}(\log\log L)\). Combining those heights, the explicit coefficient, and \(\log\mathcal B\) in (1.9) gives the uniform upper bounds \(L^{b+c+\theta+o(1)}\) and \(L^{c+\theta+o(1)}\), respectively, when \(r(h+1)\le L^\theta\). Either contradicts the local lower bound. This proves the claimed implication. See [the growing-seed Kummer proof](SmallRadicalGrowingSeedKummer.md) for the full independent expansion of (1.10).

## 4. Feedback and depth consequences, with scope

Write \(\nu=\operatorname{corank}B\). For **any feedback set \(F\) alone**, eliminating \(C\setminus F\) gives the same first-return construction and preserves \(\nu\). Every one of the at least two outgoing arcs at each \(f\in F\) extends to a first return to \(F\), by the finite-DAG argument applied to \(C\setminus F\). There is no feedback set of size zero in this finite nonempty closed positive-outdegree graph. Hence the first-return matrix on \(F\) has row sums at least two, \(I-K_F\) is nonzero, and \(\nu\le |F|-1\). This bound uses \(F\) alone; it does not presume that the retained set \(R=P\cup F\) equals \(F\) or that only seed-compatible feedback sets are allowed.

Consequently if there is a feedback set \(F\) of size at most \(s\), form \(R=P\cup F\). Had it satisfied \(r(h+1)\le L^\theta\), the seed independence would give \(\nu\ge s\), contradicting the feedback bound. Thus
\[
 h+1>L^\theta/|P\cup F|\ \ge L^\theta/(2s).
\]
This is a long directed simple path in the genuine graph avoiding all of \(P\cup F\), not just a walk in a compressed system. In particular the graph has either every feedback set of size at least \(s+1\), or this depth obstruction for each feedback set of size at most \(s\).

One may instead retain \(P\) and all \(g\) vertices that belong to directed cycles. This also leaves a DAG. In a topological decomposition of \(B\) into strongly connected component blocks, full nullity is at most the sum \(J\) of the local nullities of the cyclic diagonal blocks: each acyclic singleton contributes zero, and the inequality follows successively by projecting a kernel to the last block and considering its kernel. Thus if \(J<s\), the same implication yields \((s+g)(h+1)>L^\theta\). Conversely if the retained depth budget holds, \(J\ge s\). If every cyclic block has size at most \(K\) for an integer \(K\ge2\), each such block has nullity at most \(\lfloor K/2\rfloor\): within the block the strictly increasing arcs have at most one smaller parent per target because it is the least positive residue of \(N\) modulo that target prime. Their underlying graph is a forest (the largest vertex of a cycle would have two smaller parents). Its smaller color shore in every tree component covers the increasing arcs, meets every directed cycle of the component block, and has size at most \(\lfloor K/2\rfloor\). Acyclic elimination of its complement gives the stated nullity cap; it is not necessary to assume row sums two within a nonterminal block. Hence under the retained depth budget and the cap \(K\) there are at least \(\lceil s/\lfloor K/2\rfloor\rceil\) distinct **singular cyclic** blocks.

At a hypothetical Goldbach exception the chosen odd unit seeds below \(N-1\) have a genuine finite joint all-composite forward closure, so the necessary alternatives above apply to it. For example under the radical bound, a polylogarithmic seed family can be supplied by successive Bertrand intervals above \(L^b\), and no chosen seed divides \(N\). These are conditional graph restrictions, not statements that singular blocks are terminal, not a bound on the number of missing pairs, and not a proof for or against a Goldbach representation. The finite-size assumption on the **joint graph** in the previous theorem is replaced with a bound on retained cardinality times internal acyclic depth, not silently removed.
