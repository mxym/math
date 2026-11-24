# Low-factor dictionary versus individual high excursions

This is a genuine necessary structural restriction at small-radical targets, stronger than applying a general acyclic-depth or feedback-size bound to a high-only deletion. It applies to actual all-composite prime-factor closures, not formal graphs or distributional models.

## 1. Setup and theorem

Let \(N\) be even, \(L=\log N\). Let \(C\) be a nonempty finite forward-closed set of odd unit primes \(x<N-1\), each with \(N-x\) composite. A row \(x\) has arcs to the prime factors of its true complement, counted with multiplicity. Write
\[
 S=\{q\in C:q\le\sqrt N\},\qquad T=C\setminus S,\qquad
 A_{xy}=v_y(N-x),\quad B=I-A .
\]
Every row has at least one low prime factor (a composite below \(N\) cannot be a product of two high primes), and at most one high successor even with multiplicity. Thus \(S\ne\varnothing\), and a factor in \(T\) always has multiplicity one. In fact \(S\) has at least two labels: if \(S=\{q\}\), the row at \(q\) must contain \(q\), contradicting \((q,N)=1\).

Fix \(b,c,\theta,B_0>0\) with \(b+c+\theta<1\). Suppose \(\operatorname{rad}(N)\le L^b\), \(|S|\le s=\lfloor c\log L/\log\log L\rfloor\), and every label of \(S\) is at most \(L^{B_0}\). For sufficiently large \(N\), uniformly in \(C,S\), the following hold:

1. From **each** low label \(p\in S\), follow the unique high successor, stopping when it does not exist or when a high label would repeat. This path contains more than \(\exp(L^\theta)\) distinct high labels. In particular every low row has a high successor; no short or entirely-low excursion is possible with this restricted dictionary.
2. Every directed cycle wholly in \(T\) has length more than \(\exp(L^\theta)\), regardless of whether it is reached from \(S\).

An alternative local version replaces the radical/seed assumptions by an existing prime divisor \(\ell\mid N\) with \(\ell\le(\log L)^{A_0}\), \(v_\ell(N)\ge L^{1-o(1)}\), all \(S\)-labels at most \((\log L)^{B_1}\), and \(|S|\le\lfloor c\log L/\log\log\log L\rfloor\) with \(c+\theta<1\). The small low dictionary is still explicitly assumed.

## 2. Direct integer telescoping

For every row \(x\), write its low factor count vector as
\[
 E_x=(v_q(N-x))_{q\in S}\in\mathbb Z_{\ge0}^{S}.
\]
Its coordinate sum is at least 1 in all rows, and at least 2 if no high successor exists. Each row has total prime multiplicity at most \(D=L/\log3\).

If a high excursion from \(p=x_0\in S\) visits \(m\) distinct high labels \(x_1,\ldots,x_m\) and then ends (the last complement has no high successor), sum the original rows \(B_{x_0},\dots,B_{x_m}\). Each high coordinate \(-e_{x_i}\) in the preceding row cancels the \(+e_{x_i}\) in its own row, leaving exactly
\[
 u=e_p-\sum_{i=0}^m E_{x_i}
\]
supported on \(S\). This is not zero: its coordinate sum is \(1-\sum_i\|E_{x_i}\|_1\le-1\), using the last row, also when \(m=0\). If a high label repeats before termination, use only the directed cycle encountered. Summing its original rows cancels every high coordinate and gives \(u=-\sum_{x\in\mathrm{cycle}}E_x\ne0\), since every cycle row has the high successor and at least one low factor. This same argument works for any high cycle in the graph, not only one reached by the chosen low entrance. In either case the relation is an integer sum of actual rows, with \(\max_q |u_q|\le1+(m+1)D\) for an excursion of length \(m\) in high vertices, or \(1+(\text{cycle length})D\) for a cycle.

For every prime divisor \(\ell\) of \(N\), the product associated to a row is \(x/(N-x)\equiv-1\bmod\ell^{v_\ell(N)}\), since all labels are units. Thus the products for their sum have sign \(\pm1\) modulo that prime power. Squaring gives
\[
 \Xi=\prod_{q\in S}q^{2u_q}-1\ne0,\qquad v_\ell(\Xi)\ge v_\ell(N).
\]
Nonvanishing uses distinct actual primes and \(u\ne0\); negative exponents are units. If the high length is at most \(\exp(L^\theta)\), the exponent size parameter satisfies \(\log\mathcal B=O(\log(\mathrm{length}+1)+\log L)=O(L^\theta)\). No Schur determinant and no factor of \(s\) is needed here.

For the radical hypothesis choose \(\ell\mid N\) maximizing \(v_\ell(N)\log\ell\); then \(\ell\le L^b\) and \(v_\ell(N)\gg_b L/(\log L)^2=L^{1-o(1)}\). Apply [Kunrui Yu, Acta Arith. 89 (1999), Theorem 1 and (1.9)–(1.11)](https://bibliotekanauki.pl/articles/1390501.pdf) to the actual nonzero-exponent low labels. The auxiliary local field is \(\mathbb Q\) at odd \(\ell=3\bmod4\), \(\mathbb Q(i)\) with a split place at odd \(\ell=1\bmod4\), and \(\mathbb Q(\zeta_3)\) at 2. Thus \(e=1\), residue degree \(f=1\) at odd \(\ell\) and \(f=2\) at 2. The Kummer hypothesis (1.11) holds because at a prime ideal above each distinct odd seed its valuation is coprime to the Kummer prime (2 for odd \(\ell\), 3 for 2), while the other seeds are units and the additional root of unity is maximal in the auxiliary field. The resulting uniform coefficient is \(\ell^f\exp(O(|S|))\); the product of modified seed heights costs at most \(L^{c+o(1)}\) (each height is \(O(\log L)\)). The valuation upper bound is \(L^{b+c+\theta+o(1)}\), contradicting its actual \(L^{1-o(1)}\). In the alternative local case \(\ell^f=L^{o(1)}\), modified heights are \(O(\log\log L)\), and the enlarged \(s\) still gives height cost \(L^{c+o(1)}\), yielding \(L^{c+\theta+o(1)}\). The referenced moving-prime Kummer and DAG notes expand the same constants; no fixed-\(\ell\) uniformity is assumed.

## 3. Independent low-dimension rank structure

Suppose further that \(C\) is **generated by its low labels** under traversal of all factor arcs (equivalently, every vertex is reachable from some member of \(S\)). Then restriction of a vector in \(\ker_{\mathbb Q}B\) to its low coordinates is injective. To see this, set all low coordinates to zero. A high chain ending at a row without high successor has zero at its end and all earlier high values equal zero by backward substitution. A high chain leading to a high cycle has one free constant shared by the cycle and all such high chains (with zero low coordinates all high-successor equations identify the two endpoint values). Each high cycle is reachable by a path from a low label. Take the **last** low label on that path before entering the cycle. Its low row has one high successor, and its row equation with low coordinates zero sets that successor's value to zero. Propagation down the high path kills the cycle's free constant. Every high row ultimately ends or reaches a cycle because the high subgraph is finite and functional. Hence all coordinates vanish once the lows vanish.

Let \(E\) have one row \(\sum_{x\in D} E_x\) for each high cycle \(D\). Along a high cycle the equations \(v_x-v_{\mathrm{succ}(x)}=E_x\cdot v_S\) telescope to \(E v_S=0\). Each row of \(E\) is nonnegative and nonzero: the cycle factor occurs only once and the complement has at least one further low factor. If there is a high cycle, injection gives
\[
 \operatorname{corank} B\le |S|-\operatorname{rank}_{\mathbb Q}E
                              \le |S|-1.
\]
If no high cycle exists, exact acyclic elimination onto \(S\) gives the same \(|S|-1\) bound: each of the at least two initial factor arcs from a low row extends to a first return to \(S\) (high graph finite acyclic and full rows have positive outdegree), so the first-return matrix has row sums at least 2 and is not the identity. Also the number of high cycles is at most \(|S|\): each is approached by the unique high trajectory from some last low row, and no one such row can approach two different high cycles. This rank structure is independent of the analytic estimates and requires the stated reachability, unlike the elementary telescoping obstruction in section 2.

## 4. Conditional seed dichotomy and scope

At a hypothetical no-prime-pair target, take exactly \(s\) distinct small unit prime starting labels \(P\subset (0,\sqrt N]\) satisfying one of the local hypotheses, and their genuine joint forward closure. If no new low prime appears, then \(S=P\), and from **each** of these starting labels the unique high-only excursion must contain more than \(\exp(L^\theta)\) distinct true high primes. Thus either the seed dictionary expands through a new actual prime \(\le\sqrt N\), or every seed has this very long real high escape. There is no division by the seed count in the exponent. This does not assert the same escape in the expanding-dictionary branch.

By the global low-parent lemma in [the high-entry dichotomy](PrimeOppositeHighEntryDichotomy.md), the long high path on the second branch also contains \(\gg \exp(L^\theta)/L\) labels lacking any genuine low prime composite predecessor, not just lacking one inside this closure. The sieve-generated cloud of primes at the \(\sqrt N\) scale in that other note is not assumed to belong to this chosen polylogarithmic-seed closure. These are graph restrictions at a hypothetical exception; they neither establish an exception nor rule out all such long excursions.
