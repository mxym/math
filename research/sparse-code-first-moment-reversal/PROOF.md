# Unequal first-moment certificates

## 1. Exact comparison and conventions

Let \(3\le k\le n\), \(k\mid n\), \(m\ge1\), and \(N=n/k\). Matrix rows are independent. In the binary regular model, each row is a concatenation of \(k\) independently chosen binary unit vectors of length \(N\). In the sparse model over \(\mathbb F_p\), each row is uniform among the vectors of length \(n\) with exactly \(k\) nonzero coordinates. Let \(u_j\) be the probability that \(j\) uniform independent binary unit vectors of length \(N\) sum to zero. It is zero for odd \(j\). Let \(\pi_j(p)\) be the corresponding zero-sum probability for \(j\) sparse rows.

For positive integer \(d\) and \(T=2^{-\rho}\in(0,1)\), define
\[
 B(d)=\sum_{1\le j<d}\binom mj u_j^k,\qquad
 S_p(d)=\sum_{1\le j<d}\binom mj(p-1)^j\pi_j(p),
\]
where \(\binom mj=0\) for \(j>m\). These are exactly the two sums in c/0059: its \(q_w=u_{2w}\). It asks whether the largest feasible \(d\) for \(B(d)\le T\) is always at most the largest feasible \(d\) for \(S_p(d)\le T\), for every prime \(p>2\) with no further bound in terms of \(m,n,\rho\). We write \(D_2,D_p\) for these two largest cutoffs when finite. Every example here has a strict crossing on both sides; no convention on saturation or a trivial cutoff affects it. The ensembles differ, as in the statement.

For the interpretation as a first moment, fix a choice of \(j\) row indices and nonzero multipliers on those rows. Multiplication by a nonzero scalar preserves the uniform row distribution, so the expected number of such relations is \(\binom mj(p-1)^j\pi_j(p)\). In a binary row each block has coordinate sum one, so a relation uses an even number of rows; independence of the \(k\) blocks gives \(u_j^k\). In both models the union bound uses the first moment of the number of relations, not the probability of a relation. In the sparse model, scalar multiplication acts freely on nonzero coefficient vectors, preserving their supports and the relation, so the first moment for distinct lines of relation vectors is exactly \(S_p(d)/(p-1)\). Denote its largest feasible cutoff by \(D_p^{\rm lines}\).

## 2. Explicit strict crossings

Set \(k=3,n=54,m=55,N=18,T=1/2\). The integer counts of even occupancy at lengths 2, 4 and 6 are
\[
\begin{array}{c|l}
 2&N\\
 4&N+6\binom N2\\
 6&N+15N(N-1)+90\binom N3 .
\end{array}
\]
Indeed, an even occupancy pattern consists of one box of size 2, a size-4 box or two size-2 boxes, or a size-6 box, an ordered size-\((4,2)\) pair, or three size-2 boxes, respectively. The multinomial factors are \(6,15,90\). Division by \(N^j\) gives \(u_2=1/N\), \(u_4=(3N-2)/N^3\), and \(u_6=(15N^2-30N+16)/N^5\). In particular,
\[
 B(6)=\frac{21367885}{43046721}<\frac12,\qquad
 B(7)=\frac{154953641997605}{183014339639688}>\frac12 .
\]
The numerator differences after cross multiplication are \(43046721-2\cdot21367885=310951>0\) and \(2\cdot154953641997605-183014339639688=126892944355522>0\). Thus \(D_2=6\).

Put \(C=\binom{54}{3}=24804\). For \(j\) fixed rows, their supports all coincide with probability \(C^{1-j}\). Conditioned on this support pattern, the zero-sum probability is \(\alpha_j(p)^3\), where
\[
 \alpha_j(p)=\frac{1+(-1)^j(p-1)^{1-j}}{p}.
\]
To see the last formula, the sum of any fixed number of independent uniform nonzero field elements has the same probability at every nonzero value by invariance under scaling. Therefore \(\alpha_1=0\) and \(\alpha_{j+1}=(1-\alpha_j)/(p-1)\); solving gives the display. Independence of entries on different support positions gives the cube, regardless of the common support chosen. The contribution to the weight-\(j\) term from this event alone is
\[
 L_j(p)=\binom{55}{j}C^{1-j}(p-1)^j\alpha_j(p)^3.
\]
It is a lower bound on that term, not an approximation to the probability of any relation.

For \(p=2147483647\), \(L_4(p)>47>1/2\), so \(S_p(5)>1/2\) and \(D_p\le4\). For \(p=100000000003\), \(L_5(p)/(p-1)>9/10>1/2\), so even the line-normalized sum crosses by cutoff \(6\). For clarity, those lower bounds follow already from \(\alpha_4\ge1/p\) and \(\alpha_5\ge(1-1/(p-1)^4)/p\), substituting the displayed integers; the checkers verify each comparison by exact rational arithmetic and independently certify both primes by trial divisibility. The projective crossing is separate and does not enter the refutation of the literal statement.

For the reverse inequalities at the preceding cutoffs, use \(\alpha_a\le1/(p-1)\) for every \(a\ge2\). If \(j=2\) then \(h\ge3\) bounds the raw term by \(\binom{55}{2}/(p-1)\). If \(j=3\) then \(h=3\) has probability \(C^{-2}\), while \(h\ge4\) bounds the conditional weighted term by \(1/(p-1)\); the raw term is thus at most \(\binom{55}{3}(C^{-2}+1/(p-1))\). Their sum at \(p=2147483647\) is below \(1/10000\). For the line terms of weights \(2,3,4\), the same argument gives respective upper bounds \(\binom{55}{2}/(p-1)^2\), \(\binom{55}{3}/(p-1)\), and \(\binom{55}{4}(C^{-3}+1/(p-1))\). At \(p=100000000003\) their sum is below \(1/100000<1/2\). Thus the exact cutoffs follow already from support counting and integer comparison. The two independent exact counts in this package additionally verify the sharper pair of inequalities
\[
 \begin{split}
 S_{2147483647}(4)&<1/10000,\\
 S_{100000000003}(5)/(100000000003-1)&<1/10000000.
 \end{split}
\]
Thus \(D_{2147483647}=4\) and \(D_{100000000003}^{\rm lines}=5\). The elementary lower contributions and the binary computation already establish the strict reversals without these exact preceding-cutoff checks.

## 3. Why the comparison fails over arbitrarily large fields

Fix \(k,n,m\) and \(2\le j\le m\). Condition on the \(j\) row supports \(A_1,\ldots,A_j\). Write \(h=|\bigcup A_i|\) and let \(a_x\ge1\) be the multiplicity at each position in the union. If there is a singleton then cancellation is impossible, since \(\alpha_1=0\). Otherwise the conditional probability of zero is \(\prod_x\alpha_{a_x}(p)\). For each \(a\ge2\) fixed, \(\alpha_a(p)=p^{-1}(1+O(p^{-1}))\), by the exact scalar formula. Hence every support pattern with \(h>k\) contributes \(O(p^{-(k+1)})\) to the unweighted zero-sum probability; the number of patterns depends on \(k,n,j\) but not on \(p\). The minimum \(h=k\) occurs exactly when all supports coincide, and then every \(a_x=j\). It follows that, as \(p\) tends to infinity through primes,
\[
 \pi_j(p) = \binom nk^{1-j}p^{-k} + O(p^{-(k+1)}),\qquad
 \binom mj(p-1)^j\pi_j(p)
 = \binom mj\binom nk^{1-j}p^{j-k}\bigl(1+O(p^{-1})\bigr).
\]
The term for \(j=1\) is zero. In particular, for fixed \(m\ge k+1\), the raw certificate is at most \(k+1\) for every sufficiently large prime. For \(m\ge k+2\), the line-normalized certificate is at most \(k+2\) for every sufficiently large prime.

Now fix \(k\ge3\), \(T\in(0,1)\), and a positive integer cutoff \(d\). Let \(n\to\infty\) through multiples of \(k\), with \(m=n+1\). For fixed even \(j\) the number of partitions of the \(j\) labelled draws into occupancy classes is bounded just in terms of \(j\); each even partition has at most \(j/2\) classes and so at most \(N^{j/2}\) assignments of labels to boxes. Consequently \(u_j=O_j(N^{-j/2})\) and \(\binom mj u_j^k=O_{j,k}(n^{-j(k/2-1)})\). The odd terms vanish. Thus \(B(d)\to0\). At cutoff \(m+1\) every matrix in either model has a nonzero relation because \(m>n\), so each full first moment (including the line version) is at least one. All maxima in this family are finite. Choose \(n\) large to ensure \(D_2\ge d\), then choose a sufficiently large prime to bound \(D_p,D_p^{\rm lines}\) as above. This gives unbounded additive gaps as \(d\) varies. It does not assert the same behavior as \(n\to\infty\) with \(p\) fixed.

## 4. A field-uniform upper bound on the underlying probability

A relation with a specified support of \(j\) row indices and nonzero coefficients is impossible if some column appears in exactly one of those rows. This necessary condition depends only on supports and is valid over every field. Indeed the one nonzero entry multiplied by its nonzero coefficient cannot cancel. Thus if any relation on those indices exists, the union of the \(j\) row supports has size at most \(h=\min(n,\lfloor jk/2\rfloor)\). Any union of size at most \(h\) is contained in some \(h\)-subset of the \(n\) columns. A union bound over those \(h\)-subsets (and then over row-index sets, not coefficient vectors) gives
\[
 \Pr(\exists \text{ relation of weight }<d)
 \ \le\sum_{j=2}^{d-1}\binom mj\binom nh
   \left(\frac{\binom hk}{\binom nk}\right)^j,\qquad h=\min(n,\lfloor jk/2\rfloor).
\]
Here binomial coefficients outside their range are zero. A single row cannot give a relation, accounting for the lower index 2. Along the sequence in Section 3 every term on the right is \(O_{j,k}(n^{h-kj+j})=O_{j,k}(n^{-j(k/2-1)})\). This tends to zero uniformly over the field size. It also bounds the binary sparse first moment, because in the binary field there is only one coefficient pattern for each choice of indices. Thus the same unbounded reversal of certificate comparisons holds for exact-weight sparse rows on both sides. This support-only inequality is the direct no-singleton counting argument; the new use here is to separate the first-moment failure from the underlying event, not a new random-code distance theorem.
