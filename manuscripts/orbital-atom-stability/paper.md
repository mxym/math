# Orbital duality and sharp atom stability for permutation actions

mxym/math research project. AI-assisted manuscript, 7 October 2026.

We determine the best single-atom response to a marginal-preserving signed
perturbation of a uniform finite-group law. A universal orbital primal--dual
theorem reduces the problem to an exact rational linear program on conjugacy
classes. It applies to arbitrary finite actions, including nonfaithful and
nontransitive ones. It gives a sharp formula for doubly transitive actions and
an explicit parity-dependent formula for every symmetric-group action on
two-element subsets. For three-element subsets we give a complete finite
classification for degrees 3 through 120 and separately prove the all-degree
sharp asymptotic coefficient \(1-18/n+O(n^{-2})\). An all-rank short-cycle
transfer theorem gives polynomial-size exact rational optimization at each
fixed subset rank. Four-subset certificates determine every degree 11 through
50; the subset-rank hierarchy and uniform Bernstein limit are also proved.

The full proof of the general principle is in Section 18; Sections 15--17 give
the analytic applications. Sections 19--21 give the three-subset certificate
classification, Section 22 proves its asymptotic, and Section 23 proves the
Bernstein limit. Part J contains the general transfer theorem, rank hierarchy
and the four-subset certificates.
The original connected theorem/section/equation numbering is retained, so that
the independently published certificate documentation remains unambiguous.
Earlier permanent inequalities from the source note are not assumptions of
this paper. The finite-group actions and their familiar minimal degrees are
standard inputs; the orbital optimization and displayed sharp witnesses are
proved below. Ordinary finite-dimensional LP duality is stated and applied to
an explicit bounded feasible polytope, rather than inferred from a solver.

For each three-subset degree, the checker enumerates every conjugacy class,
computes all image-intersection orbital moments, and verifies the rational
primal feasibility, all dual inequalities and equality of objective values.
The published coefficients are optimal in the specified finite ranges. The
three-subset asymptotic is a separate analytic dual bound matched by four
explicit rational primal families; it is not extrapolated from the finite
certificates. A closed exact all-degree three-subset formula, and the proposed
higher-rank \(2k^2/n\) asymptotic, remain open. The two-subset formula is proved
for all degrees analytically; its finite checker is supplementary evidence.

The checkers use Python assertions. The reproduction launcher explicitly
compiles them with assertions enabled even when invoked under `python -O`,
restarting an isolated unoptimized child to preserve imported helper assertions.
An optimized execution that strips those assertions is not accepted as a proof
replay. This paper currently has no Lean formalization. The manuscript is
AI-assisted; external human peer review and literature-wide priority assessment
have not been supplied.


## 15. A sharp atom-modulus theorem for all doubly transitive groups

The fixed-point method applies beyond the symmetric groups. The correct invariant is the **minimal degree** of the permutation action, and the sharpness mechanism works for every finite doubly transitive group. This is a separate infinite-family structural statement, independent of the uniform permanent bound and the special three-row analysis.

Let a finite group \(G\le S_\Omega\) act faithfully and doubly transitively on a set \(\Omega\) of \(n\ge3\) points. Write \(u_G\) for its uniform measure and let

\[
m(G)=\min_{g\in G\setminus\{1\}}
\big|\{i\in\Omega:g(i)\ne i\}\big|,
\qquad \beta_G=\frac{n-m(G)}n. \tag{54}
\]

Because the point stabilizer in a doubly transitive action has at least \(n-1\ge2\) elements, some nonidentity element fixes a point; thus \(2\le m(G)\le n-1\) and \(\beta_G>0\).

**Theorem 15 (optimal atom-TV modulus for doubly transitive permutation groups).** Let \(\nu\) be any probability measure on \(G\) with the same one-point marginals as \(u_G\), namely

\[
\nu\{g:g(i)=j\}=\frac1n \qquad(i,j\in\Omega).
\]

Then, for every \(\sigma\in G\),

\[
\boxed{\left|\nu(\sigma)-\frac1{|G|}\right|
\le\beta_G\,\|\nu-u_G\|_{\mathrm{TV}}.} \tag{55}
\]

The coefficient \(\beta_G\) is the **smallest possible universal coefficient**. More precisely, let \(M=\{g\in G:|\operatorname{supp}(g)|=m(G)\}\). For every \(\sigma\in G\) and every

\[
0\le\delta\le \frac{|M|}{|G|}, \tag{56}
\]

there exists a probability measure \(\nu_{\sigma,\delta}\) with uniform one-point marginals for which

\[
\|\nu_{\sigma,\delta}-u_G\|_{\mathrm{TV}}=\delta,\qquad
\nu_{\sigma,\delta}(\sigma)=\frac1{|G|}+\beta_G\delta. \tag{57}
\]

The proof is elementary and makes no assumption of conjugacy-invariance on an arbitrary \(\nu\).

**Proof.** For a fixed \(\sigma\in G\), define the agreement count

\[
F_\sigma(g)=|\{i:g(i)=\sigma(i)\}|=\operatorname{Fix}(\sigma^{-1}g).
\]

This equals \(n\) for \(g=\sigma\), and at most \(n-m(G)\) for every \(g\ne\sigma\). Set \(v=\nu-u_G=v_+-v_-\) with positive and negative parts of equal total mass \(\delta=\|\nu-u_G\|_{\mathrm{TV}}\). Uniform one-point marginals imply

\[
\sum_{g\in G}v(g)F_\sigma(g)
=\sum_{i\in\Omega}
\left(\nu\{g:g(i)=\sigma(i)\}-\frac1n\right)=0.
\]

If \(v(\sigma)>0\), the positive \(F_\sigma\)-weighted mass is at least \(nv(\sigma)\), while the negative contribution is at most \((n-m(G))\delta\), because its support excludes \(\sigma\). This gives \(nv(\sigma)\le(n-m(G))\delta\). If \(v(\sigma)<0\), exchange the positive and negative parts. This proves (55).

For sharpness, let \(D\subseteq G\) be the derangements (elements fixing no point). It is nonempty: Burnside's orbit-counting identity for a transitive action says \(\sum_{g\in G}\operatorname{Fix}(g)=|G|\); if every element fixed a point, the identity with \(n\) fixed points and all other elements with at least one fixed point would make the sum strictly exceed \(|G|\). Define

\[
P=\left(1-\frac{m(G)}n\right)\delta_1+
\frac{m(G)}n\,U_D,\qquad Q=U_M, \tag{58}
\]

where \(U_D,U_M\) are uniform measures on the indicated sets. Both \(D\) and \(M\) are invariant under conjugation in \(G\). Since \(G\) is **doubly transitive**, any conjugacy-invariant probability law has constant probability for all diagonal pairs \(g(i)=i\), and constant probability for all ordered off-diagonal pairs \(g(i)=j\) with \(i\ne j\). Every element of \(M\) fixes exactly \(n-m(G)\) points, so under \(Q\),

\[
Q\{g:g(i)=i\}=1-\frac{m(G)}n,\qquad
Q\{g:g(i)=j\}=\frac{m(G)}{n(n-1)}\quad(i\ne j).
\]

Under \(U_D\), these probabilities are \(0\) and \(1/(n-1)\), respectively. Hence \(P\) has **exactly the same** one-point marginals as \(Q\).

Because \(m(G)<n\), every \(g\in M\) is nonidentity and has a fixed point, while \(P\) is supported on the identity and derangements. Thus \(P,Q\) have disjoint supports. For \(0\le\delta\le |M|/|G|\), define

\[
\nu_\delta=u_G+\delta(P-Q). \tag{59}
\]

It is a nonnegative probability law: at every \(g\in M\), its mass is \(|G|^{-1}-\delta|M|^{-1}\ge0\), and at all other elements no mass is subtracted. Its one-point marginals agree with \(u_G\), since \(P\) and \(Q\) have identical marginals. Disjointness gives \(\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta\), and

\[
\nu_\delta(1)=\frac1{|G|}+
\left(1-\frac{m(G)}n\right)\delta.
\]

Left translation by \(\sigma\) sends the identity atom to \(\sigma\), preserves the uniform law and total variation, and preserves uniform one-point marginals. This establishes (57) and proves sharpness. QED.

**Concrete infinite families.**

* **Symmetric groups.** For \(G=S_n\), \(m(G)=2\); (55) is precisely the optimal constant \((n-2)/n\) obtained from Theorem 15. Here \(M\) is the set of transpositions.
* **Alternating groups.** For \(G=A_n\) in its natural action with \(n\ge4\), double transitivity holds and \(m(G)=3\), attained by three-cycles. The exact optimal constant is \((n-3)/n\). In particular, the constants for \(A_4,A_5,A_6\) are \(1/4,2/5,1/2\). The sharp construction mixes identity/derangements against the three-cycle class.
* **Affine groups.** For \(G=\operatorname{AGL}(1,\mathbb F_q)\), \(q\) any prime power at least three, the natural action is doubly transitive and \(m(G)=q-1\). The exact coefficient is therefore \(1/q\), attained by contrasting nontrivial translations with affine maps having exactly one fixed point.

The finite independent checker code/check_doubly_transitive.py exhaustively verifies the signed-measure construction, one-point marginals, TV values, and optimal atom excess in several small symmetric, alternating and affine examples. The **theorem for all finite doubly transitive groups is proved above** and does not rest on those finite enumerations.

**Publication and novelty scope.** Minimal degree and derangements are classical objects; this paper claims only the stated exact distributional inequality with its displayed proof, not that the minimal-degree invariant or derangement existence is new. No generalization of Bristiel--Caputo's permanent bound to arbitrary group-uniform permutation laws is asserted.


## 16. Exact non-doubly-transitive obstruction: the edge action of \(S_5\)

Double transitivity in Theorem 15 is not merely a convenience for its extremizing construction. In a natural **transitive but not doubly transitive** action, the fixed-point/minimal-degree coefficient is **strictly non-sharp**. Moreover, the true optimal constant can still be determined exactly by a short primal-dual certificate.

Let \(G=S_5\) act on the \(n=10\) edges \(\Omega=\binom{[5]}2\) of the complete graph \(K_5\). This action is transitive but not doubly transitive: ordered pairs of edges fall into the equal, adjacent and disjoint orbitals. A vertex transposition moves six of the ten edges, so \(m(G)=6\), giving the general fixed-point upper coefficient \((10-6)/10=2/5\).

**Theorem 16 (sharp non-doubly-transitive atom modulus).** Let \(u_G\) be uniform on the 120 permutations of \(S_5\), viewed in their action on \(\Omega\). If a law \(\nu\) on \(S_5\) satisfies

\[
\nu\{g:g(E)=F\}=\frac1{10}\qquad(E,F\in\Omega),
\]

then for every \(\sigma\in S_5\),

\[
\boxed{\left|\nu(\sigma)-\frac1{120}\right|
\le\frac13\,\|\nu-u_G\|_{\mathrm{TV}}.} \tag{60}
\]

The coefficient \(1/3\) is optimal. For every \(\sigma\in S_5\) and every \(0\le\delta\le1/12\), there exists such a law with TV distance exactly \(\delta\) and atom excess exactly \(\delta/3\). Consequently, the minimal-degree bound \(2/5\) is **not sharp** for this transitive action.

**Proof (exact dual certificate).** For \(g\in S_5\), let \(F(g)\) be the number of edges \(E\in\Omega\) fixed setwise by \(g\), and let \(A(g)\) be the number of edges \(E\) whose image \(g(E)\) is **adjacent** to \(E\) (shares exactly one vertex).

Both counts depend only on the vertex-cycle type of \(g\). Directly applying a representative of each of the seven cycle types to the ten unordered pairs gives the following complete table. Every row can also be checked using the independent integer enumerator in code/check_edge_action_s5.py.

| Cycle type in \(S_5\) | Number of elements | \(F(g)\) | \(A(g)\) | \(h(g)\) |
| --- | ---: | ---: | ---: | ---: |
| \(1^5\) | 1 | 10 | 0 | \(4/9\) |
| \(2\,1^3\) | 10 | 4 | 6 | \(1/9\) |
| \(2^2\,1\) | 15 | 2 | 4 | \(1/9\) |
| \(3\,1^2\) | 20 | 1 | 9 | \(4/9\) |
| \(3\,2\) | 20 | 1 | 3 | \(1/9\) |
| \(4\,1\) | 30 | 0 | 8 | \(4/9\) |
| \(5\) | 24 | 0 | 5 | \(5/18\) |

Here the certificate function is

\[
h(g)=\mathbf1_{\{g=1\}}-\frac{F(g)-A(g)}{18}. \tag{61}
\]

The table proves, **for all 120 group elements**, the exact pointwise interval

\[
\frac19\le h(g)\le\frac49. \tag{62}
\]

Set \(v=\nu-u_G\). Uniform one-point marginals imply \(\sum_g v(g)F(g)=0\), because \(F(g)\) is a sum of diagonal marginal indicators. They also imply \(\sum_g v(g)A(g)=0\), because \(A(g)\) is a sum of indicators of specified **adjacent** image edges. Hence

\[
\nu(1)-\frac1{120}=\sum_{g\in G}v(g)h(g).
\]

Since \(v\) has total mass zero and its positive and negative parts each have mass \(\delta=\|\nu-u_G\|_{\mathrm{TV}}\), any function whose range is contained in an interval of length \(L\) has \(|\sum_g v(g)h(g)|\le L\delta\). Here \(L=4/9-1/9=1/3\), proving (60) at the identity. Left translation by \(\sigma^{-1}\) reduces any other atom to the identity while preserving the uniform edge-marginal condition.

**Proof (matching sharp construction).** Let \(T\) denote the set of the ten vertex transpositions, and \(C\) the class of twenty vertex 3-cycles. Define probability laws

\[
P=\frac13\delta_1+\frac23 U_C,\qquad Q=U_T, \tag{63}
\]

where \(U_C\) and \(U_T\) are uniform on their respective conjugacy classes. Both laws are conjugation-invariant. Because the action on ordered edge pairs has exactly the three orbitals (equal, adjacent, disjoint), their complete one-point marginal matrices are determined by the average counts of \(F\) and \(A\). From the table,

\[
\mathbb E_P F=\frac13(10)+\frac23(1)=4=\mathbb E_Q F,
\qquad
\mathbb E_P A=\frac23(9)=6=\mathbb E_Q A.
\]

The disjoint-image count is the complement to ten, so it also agrees. It follows that \(P\) and \(Q\) have **exactly the same** one-point marginals for each ordered pair of edges.

The supports of \(P\) and \(Q\) are disjoint. For \(0\le\delta\le |T|/|G|=10/120=1/12\), the signed perturbation

\[
\nu_\delta=u_G+\delta(P-Q) \tag{64}
\]

is nonnegative because every transposition retains mass \(1/120-\delta/10\ge0\). All edge-marginals remain uniform, \(\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta\), and

\[
\nu_\delta(1)=\frac1{120}+\frac{\delta}{3}.
\]

The construction attains (60) at every stated \(\delta\), and left translation again handles any \(\sigma\). This completes the exact optimality proof. QED.

**Structural interpretation.** The fixed-point argument alone sees the maximum of \(F(g)\) among nonidentity elements (four fixed edges) and gives \(2/5\). The additional adjacent-edge orbital supplies a new linear constraint. The dual function \(h\) in (61) gives the better coefficient \(1/3\), while (63)--(64) attain that coefficient. The result illustrates why extending Theorem 15 to arbitrary transitive actions requires the full *orbital-marginal geometry*, rather than minimal degree alone.

The table, explicit dual range, equal marginal matrices, nonnegative perturbation, exact TV value and atom excess are replayed with Python integer/Fraction arithmetic in code/check_edge_action_s5.py. No linear-programming solver output is used as final evidence. A floating-point LP was used only to discover the certificate, and the proof above replaces it entirely.


## 17. Exact sharp atom modulus for every two-subset action of \(S_n\)

The exact \(S_5\) theorem has an **all-\(n\) closed-form extension**. The dual obstacle and the matching primal probability measures admit elementary polynomial proofs for both parities. This yields an infinite family of non-doubly-transitive actions whose atom-concentration constant is completely determined.

Write \(\Omega_n=\binom{[n]}2\), \(N=\binom n2\), and let \(G=S_n\) act on \(\Omega_n\) in the natural way. Let \(u\) be uniform on the \(n!\) elements of \(G\). A probability law \(\nu\) on \(G\) has *uniform edge-image marginals* if

\[
\nu\{g:g(E)=H\}=\frac1N\quad(E,H\in\Omega_n).
\]

**Theorem 17 (the complete two-subset atom-modulus law).** For every integer \(n\ge4\) define

\[
\boxed{
C_n=
\begin{cases}
\displaystyle\frac{n^2-2n+8}{(n+2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac{n^2-n+4}{(n+3)(n+4)},&n\text{ odd}.
\end{cases}} \tag{65}
\]

If \(\nu\) has uniform edge-image marginals, then for **every** \(\sigma\in S_n\),

\[
\left|\nu(\sigma)-\frac1{n!}\right|
\le C_n\,\|\nu-u\|_{\mathrm{TV}}. \tag{66}
\]

The coefficient \(C_n\) is **optimal for every \(n\ge4\)**. More precisely, for every \(\sigma\) there exists \(\delta_0(n)>0\) such that for every \(0\le\delta\le\delta_0(n)\) a uniform-edge-marginal law attains the positive equality

\[
\|\nu-u\|_{\mathrm{TV}}=\delta,\qquad
\nu(\sigma)=\frac1{n!}+C_n\delta. \tag{67}
\]

In particular,

\[
C_{2r}=1-\frac{8(2r)}{(2r+2)(2r+4)},\qquad
C_{2r+1}=1-\frac{8(2r+2)}{(2r+4)(2r+5)}.
\]

Thus \(C_n=1-8/n+O(n^{-2})\). In contrast, for this action the fixed-point/minimal-degree estimate is \(1-4(n-2)/(n(n-1))=1-4/n+O(n^{-2})\), which is strictly larger for every \(n\ge5\). The \(n=5\) case specializes to Theorem 16.

### 17.1. Two conjugacy statistics control all edge marginals

For a vertex permutation \(g\in S_n\), let \(x=x(g)\) be its number of fixed vertices, and \(y=y(g)\) its number of 2-cycles. Define \(F(g)\) as the number of unordered vertex pairs fixed as *sets*, and \(A(g)\) as the number of pairs whose images share exactly one vertex with the original pair. Then

\[
F(g)=\binom x2+y,\qquad
A(g)=(x+1)(n-x)-2y. \tag{68}
\]

To see the first identity, a fixed edge consists either of two fixed vertices or of one transposition cycle. For the second, edges joining a fixed to a moved vertex contribute \(x(n-x)\). Among edges joining moved vertices, those whose images intersect in exactly one vertex are exactly the consecutive pairs in each cycle of length at least three, one for each vertex in these cycles, giving \(n-x-2y\). All other edges are disjoint from their images.

Because simultaneous relabeling of the two edges has precisely three orbitals—equal, adjacent, and disjoint—any *conjugation-invariant* probability measure on \(S_n\) has its complete edge-image transition matrix determined by \(\mathbb EF\) and \(\mathbb EA\). No invariance is assumed for the arbitrary law \(\nu\) in (66).

Let \(T\) be the class of vertex transpositions. Then

\[
(F_T,A_T)=(N-2(n-2),\,2(n-2)). \tag{69}
\]

Let \(K_k\) be the class of one \(k\)-cycle with all other vertices fixed, \(3\le k\le n\). Then

\[
(F_{K_k},A_{K_k})
=\left(\binom{n-k}{2},\ k(n-k+1)\right),\quad
D_{K_k}:=N-F_{K_k}-A_{K_k}=\frac{k(k-3)}2. \tag{70}
\]

Let \(H\) denote the class of perfect vertex matchings if \(n\) is even (cycle type \(2^{n/2}\)), or of one 3-cycle together with \((n-3)/2\) transpositions if \(n\) is odd (cycle type \(3\,2^{(n-3)/2}\)). Its relevant statistics are

\[
(F_H,A_H,D_H)=
\begin{cases}
\left(n/2,0,n(n-2)/2\right),&n\text{ even},\\[2pt]
\left((n-3)/2,3,(n-3)(n+1)/2\right),&n\text{ odd}.
\end{cases} \tag{71}
\]

### 17.2. Explicit sharp measures for every \(n\)

Choose

\[
k=\begin{cases}
n/2+1,&n\text{ even},\\
(n+3)/2,&n\text{ odd},
\end{cases}
\qquad
s_n=\begin{cases}
\displaystyle\frac{2(n-4)}{(n-2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac2{n+4},&n\text{ odd}.
\end{cases} \tag{72}
\]

For all \(n\ge4\), \(0<C_n<1\), \(0\le s_n<1\), and the following are probability laws on \(S_n\):

\[
P=C_n\delta_{\mathrm{id}}+(1-C_n)\,U_{K_k},
\qquad
Q=(1-s_n)U_T+s_n U_H. \tag{73}
\]

Their supports are disjoint (at \(n=4\), \(s_n=0\)). We claim that \(P,Q\) have **identical edge-image marginals**. Both are conjugation-invariant, so it suffices to check the two expectations \(F,A\) discussed above.

Put \(w=1-C_n\). Formulae (69)–(72) give, in both parity cases,

\[
w\frac{k(k-3)}2=s_nD_H,\qquad
wk(n-k+1)=(1-s_n)\,2(n-2)+s_n A_H. \tag{74}
\]

For even \(n\), these identities follow by substituting
\(w=8n/((n+2)(n+4))\), \(k=(n+2)/2\), and
\(D_H=n(n-2)/2\). For odd \(n\), substitute
\(w=8(n+1)/((n+3)(n+4))\), \(k=(n+3)/2\), and \(D_H=(n-3)(n+1)/2\). The first identity matches the mean number of disjoint edge-images, while the second matches adjacent images. The fixed-image mean agrees automatically, since these three counts sum to \(N\). Therefore all marginal probabilities agree.

Because \(P,Q\) are disjoint, for any sufficiently small \(\delta\ge0\) the signed perturbation

\[
\nu_\delta=u+\delta(P-Q) \tag{75}
\]

remains a probability law. Specifically, one may take

\[
0\le\delta\le \delta_0(n):=
\left(n!\max_{g\in S_n}Q(g)\right)^{-1}>0.
\]

It has uniform edge-image marginals, TV distance exactly \(\delta\), and \(\nu_\delta(\mathrm{id})=1/n!+C_n\delta\). Left translation extends this to any \(\sigma\). Thus to complete Theorem 17 it remains only to prove the universal upper bound (66).

### 17.3. Exact even-degree dual certificate

Suppose \(n\ge4\) is even. Define

\[
L_e(g)=4F(g)-(n-4)A(g),\qquad
D_e=(n-2)(n+2)(n+4),
\quad h_e(g)=\mathbf1_{\{g=\mathrm{id}\}}-\frac{4L_e(g)}{D_e}. \tag{76}
\]

For any nonidentity permutation \(g\), \(0\le x(g)\le n-2\) and
\(0\le y(g)\le(n-x(g))/2\). By (68),

\[
L_e(x,y)=
(n-2)x^2-(n-2)(n-3)x-n(n-4)+2(n-2)y. \tag{77}
\]

The positive coefficient of \(y\) and the quadratic minimum at
\(x=(n-3)/2\) show that for integer \(x\), \(L_e(x,y)\ge L_e(K_k)\), attained by either adjacent integer closest to that half-integer. Our chosen \(K_k\), for which \(x=(n-2)/2\) and \(y=0\), is one such minimizer.

For the other side, insert \(y\le(n-x)/2\) in (77). Elementary factorization gives

\[
L_e(x,y)\le 2n-(n-2)x(n-2-x)\le2n=L_e(T)=L_e(H). \tag{78}
\]

Thus every \(g\ne\mathrm{id}\) satisfies \(L_e(K_k)\le L_e(g)\le2n\). Direct substitution also gives

\[
4\big(L_e(\mathrm{id})-L_e(K_k)\big)=D_e. \tag{79}
\]

Consequently \(h_e\) lies **everywhere on \(S_n\)** in the interval

\[
-\frac{8n}{D_e}
\ \le\ h_e(g)\ \le\
1-\frac{16N}{D_e},
\]

whose length is exactly

\[
\left(1-\frac{16N}{D_e}\right)+\frac{8n}{D_e}
=\frac{n^2-2n+8}{(n+2)(n+4)}=C_n. \tag{80}
\]

Since \(v=\nu-u\) has zero total mass and the same edge-image marginals as zero, it annihilates both \(F\) and \(A\). Therefore

\[
\nu(\mathrm{id})-\frac1{n!}
=\sum_{g\in S_n}v(g)h_e(g),
\]

whose absolute value is at most \(C_n\|v\|_{\mathrm{TV}}\), because the positive and negative parts of \(v\) have equal total mass \(\|v\|_{\mathrm{TV}}\) and the range length of \(h_e\) is \(C_n\).

### 17.4. Exact odd-degree dual certificate

Suppose \(n\ge5\) is odd. Put

\[
\begin{gathered}
L_o(g)=\frac{n^2-6n+11}{2}\,A(g)-(2n-7)\,F(g),\\
D_o=\frac{(n-3)(n-2)(n+3)(n+4)}8,\qquad
h_o(g)=\mathbf1_{\{g=\mathrm{id}\}}+\frac{L_o(g)}{D_o}.
\end{gathered}\tag{81}
\]

We claim that for all nonidentity \(g\),

\[
L_o(T)=L_o(H)\le L_o(g)\le L_o(K_k). \tag{82}
\]

For the upper bound, the coefficient of \(y\) in \(L_o(x,y)\) is exactly \(-(n-2)^2<0\), so \(L_o(x,y)\le L_o(x,0)\). The latter is a concave quadratic in \(x\), with real maximum at

\[
x_*=\frac{n-3}{2}+\frac{3}{2(n-2)}.
\]

Because \(x\) is an integer and \(n\ge5\) is odd, its maximum is attained at \(x=(n-3)/2\) (also at the adjacent integer when \(n=5\)). This is exactly the fixed-vertex count of \(K_k\), proving the upper bound.

For the lower bound first assume \(1\le x\le n-2\). Because \(y\le(n-x)/2\) and its coefficient is negative, direct factorization gives

\[
\begin{aligned}
L_o(x,y)-L_o(T)
&\ge L_o\!\left(x,\frac{n-x}{2}\right)-L_o(T)\\
&=\frac{n-2}{2}(n-2-x)\big((n-2)x-3\big)\ge0,
\end{aligned}\tag{83}
\]

where the final inequality uses \(n\ge5\) and \(x\ge1\). If \(x=0\), the number of 2-cycles satisfies \(y\le(n-3)/2\): otherwise the odd number \(n-2y\) of remaining vertices would equal one and create a fixed point. Therefore

\[
L_o(0,y)\ge L_o\!\left(0,\frac{n-3}{2}\right)=L_o(T). \tag{84}
\]

This proves (82) for every nonidentity element. Direct substitution also verifies

\[
L_o(K_k)-L_o(\mathrm{id})=D_o,\qquad
L_o(K_k)-L_o(T)=
\frac{(n-3)(n-2)(n^2-n+4)}8. \tag{85}
\]

Hence the identity attains the same **maximum** of \(h_o\) as \(K_k\), and the transposition class attains its minimum. Their difference is

\[
\frac{L_o(K_k)-L_o(T)}{D_o}
=\frac{n^2-n+4}{(n+3)(n+4)}=C_n. \tag{86}
\]

As in the even case, the difference \(v=\nu-u\) annihilates both \(F,A\) and has equal positive/negative total variation masses. Integrating \(h_o\) proves
\(\left|\nu(\mathrm{id})-1/n!\right|\le C_n\|v\|_{\mathrm{TV}}\).
Left translation again treats arbitrary \(\sigma\). This concludes the universal inequality, while the matching construction (73)–(75) gives sharpness. **Theorem 17 is proved for all \(n\ge4\).** QED.

**Why minimal degree is genuinely weaker.** For the edge action, the vertex transposition fixes \(N-2(n-2)\) edges and maximizes the number of fixed edges among nonidentity vertex permutations (use \(F=\binom x2+y\), \(x\le n-2\), \(y\le(n-x)/2\)). The resulting upper coefficient is \(1-4(n-2)/(n(n-1))\). Subtracting \(C_n\) gives

\[
\begin{cases}
\displaystyle\frac{4(n-4)(n^2-2n-4)}{n(n-1)(n+2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac{4(n^3-5n^2+24)}{n(n-1)(n+3)(n+4)},&n\text{ odd},
\end{cases}
\]

strictly positive for every \(n\ge5\). The improvement is of order \(4/n\).

**Reproducibility.** The checker code/check_all_two_subset_actions.py exhausts all conjugacy types (integer partitions) for \(4\le n\le40\), checks the exact rational dual range and all four moment/positivity conditions for the primal construction, and matches the closed formula \(C_n\). This finite replay is **not** the proof for arbitrary \(n\); the symbolic quadratic estimates (77)–(86) and the explicit measures (73)–(75) supply that proof. In particular, the original floating-point LP exploration is discovery-only and no solver result is used as a theorem premise.


## 18. Universal orbital primal-dual theorem for finite permutation actions

Theorems 15–17 are instances of a general exact principle: **the sharp single-atom response to marginal-preserving perturbations is determined by a finite rational linear program on the conjugacy classes and the orbitals of the permutation representation**. In a doubly transitive action there are only two orbitals; in the two-subset action there are three. This explains the difference between the minimal-degree formula and the exact edge-action law.

Let \(G\) be a finite group acting (not necessarily transitively or faithfully) on a finite nonempty set \(\Omega\), with \(e\in G\) its identity. Write \(u_G\) for the uniform law on \(G\), and let \(\mathcal V\) be the real vector space of signed functions \(v:G\to\mathbb R\) satisfying

\[
\sum_{g\in G}v(g)=0,\qquad
\sum_{\substack{g\in G\\g(x)=y}}v(g)=0
\quad\text{for all }x,y\in\Omega. \tag{87}
\]

Let \(\mathcal O_1,\ldots,\mathcal O_r\) be the orbitals of the action, i.e. the orbits of \(G\) on \(\Omega\times\Omega\) under simultaneous relabeling. Define their *orbital displacement counts*

\[
F_j(g)=\#\{x\in\Omega:(x,g(x))\in\mathcal O_j\}. \tag{88}
\]

Each \(F_j\) is constant on conjugacy classes of \(G\). Let \(C_1,\ldots,C_s\) be those conjugacy classes, with \(C_1=\{e\}\), and put

\[
M_{ji}=\frac1{|C_i|}\sum_{g\in C_i}F_j(g),\qquad
M\in\mathbb Q^{r\times s}. \tag{89}
\]

For \(\mathcal V\ne\{0\}\), define

\[
\mathcal C(G,\Omega)=\sup_{\substack{v\in\mathcal V\\v\ne0}}
\frac{|v(e)|}{\tfrac12\sum_g|v(g)|}. \tag{90}
\]

For \(\mathcal V=\{0\}\), set \(\mathcal C(G,\Omega)=0\). The supremum is finite and \(0\le\mathcal C(G,\Omega)\le1\).

**Theorem 18 (exact orbital primal-dual characterization).** The following four quantities are all equal:

\[
\begin{aligned}
\mathcal C(G,\Omega)
&=\max_{\substack{P,Q\text{ probability laws on }G\\
P\{g:gx=y\}=Q\{g:gx=y\}\ \forall x,y}}
\big(P(e)-Q(e)\big)\\
&=\max_{\substack{p,q\in\mathbb R_{\ge0}^{s}\\
\mathbf1^Tp=\mathbf1^Tq=1,\ Mp=Mq}}
(p_1-q_1)\\
&=\min_{\lambda\in\mathbb R^r}
\left[
\max_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
-\min_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
\right]\\
&=\min_{\varphi\in\mathrm{span}_{\mathbb R}\{F_1,\ldots,F_r\}}
\operatorname{osc}_{g\in G}\big(\mathbf1_{\{g=e\}}-\varphi(g)\big).
\end{aligned}\tag{91}
\]

Both finite LPs in the middle have **rational optimal solutions**, so \(\mathcal C(G,\Omega)\in\mathbb Q\). If \(\mathcal C(G,\Omega)>0\), there exist two **conjugation-invariant, disjointly supported** probability laws \(P,Q\) with identical one-point marginals and \(P(e)-Q(e)=\mathcal C(G,\Omega)\). Hence for all sufficiently small \(\delta\ge0\),

\[
\nu_\delta=u_G+\delta(P-Q) \tag{92}
\]

is a probability law with exactly the same one-point marginals as \(u_G\) and

\[
\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta,\qquad
\nu_\delta(e)-u_G(e)=\mathcal C(G,\Omega)\delta. \tag{93}
\]

For an arbitrary probability law \(\nu\) whose marginals match \(u_G\), and any \(\sigma\in G\),

\[
\left|\nu(\sigma)-\frac1{|G|}\right|
\le\mathcal C(G,\Omega)\|\nu-u_G\|_{\mathrm{TV}}, \tag{94}
\]

with this constant optimal whenever it is positive. Left translation moves the sharp construction from \(e\) to any prescribed \(\sigma\).

**Proof.** First formulate a finite **unreduced** LP. Choose \(P,Q\) as nonnegative probability vectors indexed by \(G\), impose their equality of all one-point marginals, and maximize \(P(e)-Q(e)\). Call its optimum \(\gamma\).

For any feasible pair, \(v=P-Q\in\mathcal V\), \(\|v\|_{\mathrm{TV}}\le1\), so \(P(e)-Q(e)\le\mathcal C(G,\Omega)\). Conversely, for any nonzero \(v\in\mathcal V\), its Jordan parts \(v_+,v_-\) each have mass \(d=\|v\|_{\mathrm{TV}}>0\), and the probability measures \(P=v_+/d,\ Q=v_-/d\) have identical marginals. Exchanging them if necessary, they give objective \(|v(e)|/d\). Hence \(\gamma=\mathcal C(G,\Omega)\). If \(\mathcal V=\{0\}\), the two quantities are both zero.

The unreduced primal is a rational finite LP. Its dual has one unrestricted multiplier \(\lambda_{xy}\) for each marginal equality and two normalization multipliers \(a,b\). Write

\[
\phi(g)=\sum_{x,y\in\Omega}\lambda_{xy}\,\mathbf1_{\{g(x)=y\}}.
\]

Dual feasibility is exactly

\[
a\ge\mathbf1_{\{g=e\}}-\phi(g),\qquad
b\ge-\mathbf1_{\{g=e\}}+\phi(g)
\quad\text{for all }g\in G.
\]

Minimizing \(a+b\) for fixed \(\phi\) gives
\(\max_g(\mathbf1_{\{g=e\}}-\phi(g))-
\min_g(\mathbf1_{\{g=e\}}-\phi(g))\), its oscillation. The primal is feasible (take \(P=Q=u_G\)) and bounded, so **finite-dimensional LP strong duality** gives equality with the minimum oscillation. The LP has rational coefficients and a finite attained optimum; standard rational Gaussian elimination at a basic feasible optimum gives rational primal and dual certificates.

Next average an optimal primal pair under simultaneous conjugation by \(h\in G\): replace \(P,Q\) by the averages of their pushforwards under \(g\mapsto hgh^{-1}\). Equal one-point marginals remain equal because conjugating both pairs of image coordinates by \(h\) permutes the constraints. The identity atom and the objective are unchanged. Thus a conjugation-invariant optimal pair exists. Such pairs assign a constant probability density to each conjugacy class, and their equality of one-point marginals is equivalent to the reduced moment equation \(Mp=Mq\): for a central law, each entry \(\Pr(gx=y)\) is constant on the orbital containing \((x,y)\), and its orbital average is \(\mathbb EF_j/|\mathcal O_j|\). This proves the second line of (91).

Similarly, average any dual function \(\phi\) over conjugations. The indicator \(\mathbf1_{\{g=e\}}\) is conjugacy invariant, while oscillation is convex and invariant under conjugation; the average cannot increase oscillation. A conjugation-averaged linear combination of the image indicators has coefficients constant on their simultaneous \(G\)-orbits in \(\Omega\times\Omega\). Therefore it lies in \(\mathrm{span}\{F_j\}\). This proves the fourth line of (91). Evaluating the same oscillation on conjugacy classes gives the third line, whose entries are precisely (89).

When the optimum \(\gamma>0\), an optimal reduced pair \(P,Q\) must be **mutually singular**. Otherwise \(d=\|P-Q\|_{\mathrm{TV}}<1\), and its Jordan parts normalized by \(d\) would form an admissible pair with strictly larger objective \(\gamma/d>\gamma\), contradiction. Thus the supports of an optimal central \(P,Q\) are disjoint and (92) is a probability measure for every
\(0\le\delta\le(|G|\max_gQ(g))^{-1}\), with all the stated identities.

Finally, for any law \(\nu\) with the uniform law's one-point marginals, \(v=\nu-u_G\in\mathcal V\) and the defining norm bound gives (94) at the identity. Replacing \(\nu\) by its left translate by \(\sigma^{-1}\) preserves marginal equality with \(u_G\), total variation and atom excess, proving (94) for every \(\sigma\). The same translation transports the attained equality. QED.

**Consequences and scope.** Theorem 18 gives a fully finite **exact certificate interface** for *every* finite permutation group action: exhibit a central primal pair of matching orbital moments and a dual orbital linear combination whose oscillation equals the primal atom excess. It also explains Theorem 15 (rank-two orbital geometry and a single fixed-point statistic), Theorem 16 (rank-three geometry in degree ten), and Theorem 17 (a full parity-dependent family of exact rank-three optima). The theorem does **not** assert a similarly explicit symbolic formula for arbitrary higher-rank actions. Determining a closed analytic optimum for \(S_n\) acting on \(k\)-subsets with \(k\ge3\) is a natural next target; numerical LP output there must be converted to rational primal-dual certificates before any theorem claim.


## 19. A complete certified three-subset spectrum through degree 23

The general orbital principle of Theorem 18 also yields an exact finite classification in the **next Johnson rank**, namely \(S_n\) acting on its three-element subsets. In this case, ordered pairs of subsets have four orbitals, indexed by their intersection sizes \(0,1,2,3\). The optimal coefficient is no longer given by the simple parity formula of Theorem 17, but a complete fixed rational certificate has been constructed for **every degree \(3\le n\le23\)**.

Define \(C_n^{(3)}\) to be the optimal atom-vs-TV coefficient for \(S_n\) on \(\binom{[n]}3\) under marginal preservation, as in Theorem 18. For \(n=3\), the subset action is trivial and \(C_3^{(3)}=1\). For \(n=4\), the complement map identifies the action with the natural doubly transitive action of \(S_4\), so \(C_4^{(3)}=1/2\) by Theorem 15. For \(n=5\), complementation identifies the triple action with the pair action, giving \(C_5^{(3)}=C_5=1/3\) by Theorem 17.

**Theorem 19 (complete exact small-degree triple-action classification).** For every \(6\le n\le23\), the exact optimum is given in the following table. Together with the three elementary cases above, this determines **every degree \(3\le n\le23\)**.

| \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) |
|---:|---:|---:|---:|---:|---:|
|6|5/14|12|97/232|18|5656/11331|
|7|5/14|13|283/661|19|3859/7609|
|8|89/244|14|1328/2975|20|169/322|
|9|259/691|15|14311/31629|21|7411/13909|
|10|368/935|16|5579/11744|22|2485/4554|
|11|1027/2593|17|1679/3469|23|6219/11242|

The exact statement includes **attainment** of each bound by a sufficiently small marginal-preserving rational perturbation of the uniform law. No claim for every \(n>23\) or of an all-\(n\) closed formula is made.

### 19.1. Fixed primal-dual certificates

For each \(n=6,\ldots,23\), the public file

\[
\text{certificates/three\_subset\_n6\_23.json} \tag{95}
\]

contains **fixed exact fractions** specifying:

- two conjugation-invariant probability measures \(P_n,Q_n\), each as weights on explicit \(S_n\) conjugacy classes (cycle partitions);
- three rational dual coefficients \(\lambda_0,\lambda_1,\lambda_2\), associated with the three nonidentity-intersection orbital counts;
- two rational dual extrema \(\ell_n,u_n\);
- the proposed exact optimum \(c_n=u_n-\ell_n=P_n(e)-Q_n(e)\).

The supports are disjoint, and no entry is a decimal approximation.

For clarity, if \(g\in S_n\), set

\[
F_j(g)=\#\left\{E\in\binom{[n]}3:\ |E\cap g(E)|=j\right\},
\qquad j=0,1,2,3. \tag{96}
\]

Each \(F_j\) is constant on conjugacy classes. The certificate verifier independently checks for every \(n\) that

\[
\begin{aligned}
&\sum_{g}P_n(g)=\sum_{g}Q_n(g)=1,\qquad P_n,Q_n\ge0,\qquad
\operatorname{supp}P_n\cap\operatorname{supp}Q_n=\varnothing,\\
&\mathbb E_{P_n}F_j=\mathbb E_{Q_n}F_j\quad(0\le j\le3),\\
&\ell_n\le
\mathbf1_{\{g=e\}}-\sum_{j=0}^{2}\lambda_jF_j(g)
\le u_n\quad\text{for every conjugacy class }[g]\subseteq S_n,\\
&\left(\mathbf1_{\{g=e\}}-\sum_{j=0}^{2}\lambda_jF_j(g)\right)
=\begin{cases}u_n,&g\in\operatorname{supp}P_n,\\
\ell_n,&g\in\operatorname{supp}Q_n,
\end{cases}\\
&u_n-\ell_n=P_n(e)-Q_n(e)=c_n.
\end{aligned}\tag{97}
\]

Because the action on ordered pairs of triples has exactly the four intersection-size orbitals, equality of the four moments is **equivalent to equality of all one-point triple-image marginals** for the central measures \(P_n,Q_n\). The central dual function in (97) is a linear combination of the marginal indicators. Its oscillation bounds the atom defect of *any* marginal-preserving law, central or not. Conversely, for all sufficiently small \(\delta>0\),

\[
\nu_\delta=u_{S_n}+\delta(P_n-Q_n)
\]

is nonnegative, retains uniform triple-image marginals, has TV distance \(\delta\), and its identity atom increases by exactly \(c_n\delta\). Thus (97) supplies both the universal upper bound and an attaining lower bound for each degree.

### 19.2. Reproducible finite exhaustive proof

The fixed JSON certificate file and the **separate optimizer-free checker**

\[
\text{code/check\_three\_subset\_certificates.py} \tag{98}
\]

form the complete finite proof evidence. The checker uses only standard-library integer and \(\mathrm{fractions.Fraction}\) arithmetic, not SciPy, SymPy, a numerical optimizer, randomization, or floating-point values. It independently enumerates every integer partition of every \(n=6,\ldots,23\). Integer partitions parameterize **all** \(S_n\) conjugacy classes, so verifying (97) on one canonical cycle representative of each partition checks the dual inequality on **every permutation**. For each representative it enumerates every three-element subset, explicitly counts the four intersection orbitals, and evaluates all primal and dual assertions as rational equalities or inequalities. It additionally verifies the exact conjugacy-class cardinalities sum to \(n!\), positive perturbation margins, all certificate contact equalities and the values in the table.

The program verifies a **finite, fixed** mathematical assertion, not an infinite family inferred from sample data. Termination is manifest from the bounded partition/subset loops. A separate script, code/generate_three_subset_certificates.py, reconstructs the fixed fractions by rational Gaussian elimination on predetermined class supports. The **checker does not call or trust this generator** and accepts only the separately published fixed JSON data.

A fresh-copy Windows replay downloaded both the published JSON and the standalone checker into a new isolated directory, ran the checker, and returned

\[
\texttt{EIGHTEEN EXACT THREE-SUBSET CERTIFICATES REPLAYED}
\]

followed by a successful fresh-public-source completion marker. The full independent replay and its boundaries are recorded in VERIFICATION.md.

**Scope and open continuation.** Unlike Theorem 17, this is an **exact finite classification**, not a universal closed expression for \(C_n^{(3)}\). The increasingly varied conjugacy-class supports suggest phase changes in the rank-four orbital convex hull. Determining an all-\(n\) algebraic formula, stabilization ranges, or rigorous asymptotic expansion is the next natural theoretical step. Any conjecture about \(n>23\) must remain labelled computational until its own proof or independently verified certificates exist.


## 20. An exact three-cycle-statistic compression theorem

The rank-four orbital data for the natural \(S_n\)-action on its three-element subsets have a much simpler representation than full conjugacy-class partitions suggest. **Only the counts of cycles of lengths 1, 2 and 3 matter.** This fact gives a finite rational LP with \(O(n^3)\) candidate types and makes exact certificates for substantially larger degrees practical.

Let \(n\ge3\), \(\Omega=\binom{[n]}3\), and let \(g\in S_n\) have \(x\) fixed points, \(y\) two-cycles and \(z\) three-cycles. For \(j=0,1,2,3\), write

\[
F_j(g)=\#\{E\in\Omega:|E\cap g(E)|=j\},
\qquad N=\binom n3.
\]

**Theorem 20 (three-cycle compression).** Define

\[
\begin{aligned}
M_1(x)&=x\binom{n-1}{2}+(n-x)(n-2)
     =\frac{n-2}{2}\,[2n+(n-3)x],\\
M_2(x,y)&=(n-2)\binom x2+x(n-x)+(n-2)y+(n-x-2y)\\
        &=(n-2)\binom x2+(x+1)(n-x)+(n-4)y,\\
M_3(x,y,z)&=\binom x3+xy+z.
\end{aligned}\tag{99}
\]

Then

\[
\boxed{
\begin{aligned}
F_3&=M_3,\\
F_2&=M_2-3M_3,\\
F_1&=M_1-2M_2+3M_3,\\
F_0&=N-M_1+M_2-M_3.
\end{aligned}} \tag{100}
\]

In particular, all four orbital counts depend **only** on \((x,y,z)\), not on the remaining cycle structure.

Moreover, a triple of nonnegative integers \((x,y,z)\) occurs for some permutation in \(S_n\) **if and only if**

\[
r:=n-x-2y-3z\quad\text{equals \(0\) or is at least \(4\)}. \tag{101}
\]

Every feasible triple has the canonical representative with cycle type
\(1^x2^y3^z\), supplemented by one \(r\)-cycle if \(r\ge4\).
Consequently the *full* rational primal-dual LP of Theorem 18 can be compressed, **without changing its optimum**, to the finite set

\[
\mathcal T_n=
\{(x,y,z)\in\mathbb Z_{\ge0}^3:
n-x-2y-3z\in\{0\}\cup[4,\infty)\}. \tag{102}
\]

Here \(|\mathcal T_n|=O(n^3)\), instead of the partition number \(p(n)\) conjugacy classes. Each compressed primal variable represents a central probability mass distributed uniformly on its canonical conjugacy class. Group elements with the same \((x,y,z)\) have identical dual evaluations, so no constraint is lost.

**Proof.** Let \(K(E)=|E\cap g(E)|\) for \(E\in\Omega\). Binomial inversion on \(K\in\{0,1,2,3\}\) shows that the four \(F_j\) are determined by

\[
M_a=\sum_{E\in\Omega}\binom{K(E)}a,\qquad a=1,2,3,
\]

together with \(M_0=N\); solving this triangular system gives (100).

To count \(M_1\), fix a vertex \(v\). If \(g(v)=v\), then \(v\) lies in \(E\cap g(E)\) exactly when \(v\in E\), giving \(\binom{n-1}{2}\) triples. Otherwise, both \(v\) and its distinct preimage \(g^{-1}(v)\) must be in \(E\), giving \(n-2\) triples. Summing over the \(x\) fixed and \(n-x\) moved vertices gives the first formula in (99).

For \(M_2\), count unordered pairs \(\{v,w\}\subset E\cap g(E)\). There are four disjoint cases:

- Both are fixed: \(\binom x2\) possible vertex pairs, each in \(n-2\) triples.
- Exactly one is fixed: \(x(n-x)\) pairs, each determining its unique required third vertex \(g^{-1}(w)\) (or \(g^{-1}(v)\)).
- They are the two vertices of the same transposition: \(y\) pairs, each in \(n-2\) triples.
- They are consecutive in a cycle of length at least three: every such cycle contributes exactly its length many unordered adjacent pairs, so \(n-x-2y\) pairs overall; each has exactly one completing third vertex.

There are no other pairs for which the four vertices \(v,w,g^{-1}(v),g^{-1}(w)\) occupy at most three distinct positions. This establishes \(M_2\).

Finally, \(K(E)=3\) precisely when \(g(E)=E\). A three-point invariant set is a union of cycles of total size three, hence is either three fixed points, a fixed point plus a transposition, or one three-cycle. There are exactly \(\binom x3+xy+z\) such sets. This is \(M_3\).

Cycles of length at least four account for \(r\) vertices. Their total size is either zero or at least four; conversely one \(r\)-cycle realizes every \(r\ge4\). This proves (101). Theorem 18 already reduces the marginal-constrained optimization to conjugation-invariant probability distributions and conjugacy-invariant orbital dual functions. Since their orbital data factor through \((x,y,z)\), aggregating probabilities over classes with identical triples preserves all constraints and the distinguished identity atom; conversely each feasible triple has the displayed representative. Thus this aggregation preserves the optimum. QED.

**Note on complexity.** The theorem changes the *number of distinct constraints* from \(p(n)\) to \(O(n^3)\). It does not say that an optimizer is trustworthy by itself: any claimed optimum still requires exact primal weights and a dual function whose inequalities are checked for all types in (102).

## 21. Complete exact rank-four atom-modulus classification through degree 120

The compression theorem enables a substantial extension of Theorem 19 while retaining a short, **independent and optimizer-free** integer checker.

**Theorem 21 (finite exact triple-action classification).** The sharp coefficient \(C_n^{(3)}\) for \(S_n\) acting on \(\binom{[n]}3\), under preservation of all triple-image one-point marginals, is now determined **exactly for every \(3\le n\le120\)**.

Degrees \(3\le n\le23\) are covered by Theorems 15, 17 and 19 and their earlier fixed certificates. For each degree \(24\le n\le120\), the additional fixed public certificate file

\[
\texttt{certificates/three\_subset\_n24\_120.json} \tag{103}
\]

contains an explicit pair of *conjugation-invariant*, disjointly supported probability measures \(P_n,Q_n\), each described by rational masses on canonical cycle types of the form \((x,y,z,r)\), together with three rational coefficients \(\lambda_{0,n},\lambda_{1,n},\lambda_{2,n}\), dual extrema \(\ell_n,u_n\), and the exact fraction

\[
C_n^{(3)}=P_n(e)-Q_n(e)=u_n-\ell_n. \tag{104}
\]

For clarity, selected newly certified values are

| \(n\) | Exact \(C_n^{(3)}\) | \(n\) | Exact \(C_n^{(3)}\) |
|---:|:---|---:|:---|
|24|32461/57220|25|80848/140761|
|26|108592/185523|30|102746/165985|
|40|284639/416012|50|555884/760975|
|60|822469/1074757|70|4211614/5317095|
|80|18639283/22912384|90|38205728/45980475|
|100|3177111/3758198|120|53562383/61708904|

Every one of the other exact fractions for \(24\le n\le120\) appears in (103). No extrapolation beyond degree 120 is asserted.

**Proof by independently checkable finite rational certificates.** For each \(n=24,\ldots,120\), the fixed JSON file records three positive rational masses for \(P_n\) (one on the identity class) and two for \(Q_n\), summing to one on each side. The verifier checks that their canonical conjugacy-class supports are disjoint and that all four orbital moments match:

\[
\mathbb E_{P_n}F_j=\mathbb E_{Q_n}F_j\qquad(0\le j\le3). \tag{105}
\]

Since both are class-invariant, these four equalities imply equality of **every** triple-image marginal (Theorem 18). For the recorded dual data, define

\[
h_n(g)=\mathbf1_{\{g=e\}}-
\sum_{j=0}^2\lambda_{j,n}F_j(g). \tag{106}
\]

The public checker then verifies **for every** \((x,y,z)\in\mathcal T_n\),

\[
\ell_n\le h_n(x,y,z)\le u_n, \tag{107}
\]

and equality with \(u_n\) on all \(P_n\)-support classes and \(\ell_n\) on all \(Q_n\)-support classes. By Theorem 20, this is an exhaustive check over **all possible** \(S_n\) conjugacy classes, including those having many cycles of length at least four. No unexamined real or integer parameter remains in the stated finite degree range.

All dual denominators are cleared first, so (107) is verified by **integer comparisons**; the only fractions handled are the five primal weights and three dual coefficients per degree. The checker also verifies normalizations, all moment equations, positive class cardinalities and an explicit small rational \(\delta>0\) for which \(u_{S_n}+\delta(P_n-Q_n)\) is a probability law. Theorem 18 now proves the upper bound \(C_n^{(3)}\le u_n-\ell_n\), while this actual attaining perturbation proves the reverse inequality. The exact identity (104) is checked for each degree. Hence every advertised coefficient is rigorously established by a finite replayable certificate. QED.

**Computational trust boundary.** The published standalone program
\nolinkurl{code/check_three_subset_compressed_24_120.py}
uses **only Python 3 standard-library integers and fractions**. Its loops cover the 97 degrees and all \(\mathcal T_n\), amounting to exactly **1,489,083 compressed type evaluations** in the fixed range. It uses no optimizer, floating-point comparison, Sage, SciPy, SymPy or solver oracle. The original support discovery *did* use floating-point linear programming, followed by exact rational reconstruction; that discovery history is not used by the checker or as a logical premise of Theorem 21.

This is a **large but finite** exact classification. Neither the observed apparent support periodicity nor the numerical trend of \(C_n^{(3)}\) justifies claiming an all-degree formula or asymptotic expansion. The next frontier is to prove an infinite parameterized primal-dual family, ideally by factorization of the cubic polynomial (106) in the constrained cycle-count region (102).


## 22. Sharp universal first-order asymptotics for all three-subset actions

The exact finite classification through \(n=120\) does **not** by itself imply a uniform formula. Nevertheless, the orbital compression theorem permits a genuine **infinite-parameter asymptotic theorem** with a sharp leading constant.

**Theorem 22 (universal sharp first-order asymptotic).** For the sharp marginal-preserving single-atom total-variation coefficient \(C_n^{(3)}\) of the \(S_n\) action on three-element subsets,

\[
\boxed{\displaystyle
C_n^{(3)}=1-\frac{18}{n}+O(n^{-2}),
\qquad
\lim_{n\to\infty}n\bigl(1-C_n^{(3)}\bigr)=18.} \tag{108}
\]

The upper bound has the following **explicit** universal version: for every integer \(n\ge2048\),

\[
C_n^{(3)}\le
1-\frac{18}{n}+\frac{406304}{n^2}. \tag{109}
\]

The lower bound in (108) is supplied by explicit, exactly moment-matched positive rational probability measures for **every sufficiently large** \(n\), not by extrapolation from finite optimization.

### 22.1. A uniform analytic dual bound

For every \(n\ge3\), set

\[
\lambda_0=-\frac6{n^3}+\frac{18}{n^4},\qquad
\lambda_1=\frac{12}{n^3}-\frac{436}{n^4},\qquad
\lambda_2=-\frac{18}{n^3}+\frac{198}{n^4}
\tag{110}
\]

and define the central dual function

\[
h_n(g)=\mathbf1_{\{g=e\}}-\sum_{j=0}^2\lambda_jF_j(g),
\tag{111}
\]

where \(F_j\) are the exact triple-action orbital counts of Theorem 20. Evidently \(h_n(e)=1\), because \(F_0(e)=F_1(e)=F_2(e)=0\).

For nonidentity \(g\), let \(x,y,z\) count its 1-, 2- and 3-cycles, and introduce

\[
a=x/n,\qquad b=y/n,\qquad c=z/n.
\]

Then \(0\le a\le1-2/n\), \(0\le b\le(1-a)/2\), and \(0\le c\le1/3\). Substituting the **polynomial identities (99)–(100)** into (111), and collecting exact powers of \(1/n\), gives

\[
h_n(g)=H(a)+\frac{J(a,b)}n+\frac{R_2(a,b,c)}{n^2}
                   +\frac{R_3(a,b,c)}{n^3}, \tag{112}
\]

where

\[
\begin{aligned}
H(a)&=(1-a)(4a-1)^2
     =1-a(4a-3)^2,\\
J(a,b)&=320a^3-592a^2+296a-24+48b(1-2a),\\
R_2(a,b,c)&=1216a^2+1920ab-1765a-1280b-96c+549,\\
R_3(a,b,c)&=2(1001a+2176b+960c-1001).
\end{aligned} \tag{113}
\]

These are exact identities, not asymptotic fits. The sum of the absolute integer coefficients in \(R_2,R_3\) is \(6826+10276=17102\). Since \(0\le a,b,c\le1\),

\[
\left|\frac{R_2}{n^2}+\frac{R_3}{n^3}\right|
\le\frac{17102}{n^2}
\qquad(n\ge1). \tag{114}
\]

Put \(J_0(a)=J(a,0)\). Its derivative satisfies \(|J_0'(a)|\le2440\) on \([0,1]\), and

\[
J_0(1/4)=18,\qquad J_0(3/4)=0.
\tag{115}
\]

For any fixed \(a\), the coefficient of \(b\) in \(J\) is \(48(1-2a)\). Thus, using \(0\le b\le(1-a)/2\),

\[
\begin{array}{ll}
a\le1/2:&
J_0(a)\le J(a,b)\le J_0(a)+24(1-a)(1-2a)
=32a(1-a)(7-10a),\\[2pt]
a\ge1/2:&
32a(1-a)(7-10a)\le J(a,b)\le J_0(a).
\end{array} \tag{116}
\]

We now establish the fully uniform bounds

\[
\frac{18}{n}-\frac{203152}{n^2}
\le h_n(g)\le
1+\frac{203152}{n^2}
\quad\text{for every }g\ne e,\quad n\ge2048. \tag{117}
\]

**Upper bound.** When \(a\le1/2\), (116) gives \(J(a,b)\le224a\), while
\(1-H(a)=a(4a-3)^2\ge a\). Hence \(H+J/n\le1\) for \(n\ge224\).

When \(a\ge1/2\), (115)–(116) give
\(J(a,b)\le2440|a-3/4|\), while
\(1-H(a)=16a(a-3/4)^2\ge8(a-3/4)^2\). Completing the square,

\[
H(a)+J(a,b)/n\le
1+\frac{2440^2}{32n^2}
=1+\frac{186050}{n^2}.
\]

Combine with (114) to get the upper half of (117), with
\(186050+17102=203152\).

**Lower bound, \(a\le1/2\).** By (115)–(116),
\(J(a,b)\ge18-2440|a-1/4|\).
Also \(H(a)=16(1-a)(a-1/4)^2\ge8(a-1/4)^2\).
Another completion of the square yields
\(H+J/n\ge18/n-186050/n^2\); use (114).

**Lower bound, \(1/2\le a\le15/16\).**
Put \(s=1-a\in[1/16,1/2]\).
From (116), \(J(a,b)\ge-96s\).
Since \(H=s(3-4s)^2\ge s\),

\[
H+J/n\ge s(1-96/n)\ge\frac1{16}(1-96/n)
\ge\frac{18}{n}\quad(n\ge384).
\]

Again (114) suffices.

**Lower bound, \(15/16\le a<1\).**
Now \(2/n\le s=1-a\le1/16\), because a nonidentity permutation moves at least two vertices. Equations (113), (116) yield

\[
H+J/n\ge
(9-96/n)s-24s^2.
\]

The right side is a concave quadratic on \([2/n,1/16]\), so its minimum lies at an endpoint. At \(s=2/n\) it equals \(18/n-288/n^2\). At \(s=1/16\) it equals \(15/32-6/n\), which is at least \(18/n-288/n^2\) for \(n\ge2048\). Use (114) to complete (117).

Theorem 18 now bounds the sharp coefficient by the **oscillation** of any central orbital dual function. Since \(h_n(e)=1\), (117) gives the explicit upper bound (109).

### 22.2. Matching rational probability constructions in all four congruence classes

For the reverse bound, write \(n=4m+r\) with \(0\le r\le3\), and let \(m\) be sufficiently large. Consider the following **five concrete conjugacy classes** of \(S_n\):

| \(r\) | \(K\) | \(H\) | \(E\) |
|:---:|:---|:---|:---|
|0| \((m+2)1^{3m-2}\) | \(2^{2m}\) | \(3^{m+1}1^{m-3}\) |
|1| \((m+2)1^{3m-1}\) | \(3\,2^{2m-1}\) | \(3^{m+1}1^{m-2}\) |
|2| \((m+3)1^{3m-1}\) | \(2^{2m+1}\) | \(4\,3^m1^{m-2}\) |
|3| \((m+3)1^{3m}\) | \(3\,2^{2m}\) | \(5\,3^m1^{m-2}\) |

Together with \(I=1^n\) (identity) and \(T=2\,1^{n-2}\), define *unknown rational probability weights*
\(p_I,p_K,p_H,q_T,q_E\) uniquely by the five linear equations

\[
\begin{aligned}
p_I+p_K+p_H&=1,\qquad q_T+q_E=1,\\
p_I F_j(I)+p_KF_j(K)+p_HF_j(H)
&=q_TF_j(T)+q_EF_j(E),\quad j=0,1,2.
\end{aligned}\tag{118}
\]

The entries \(F_j\) are the explicit integer polynomials (99)–(100), so (118) is a **completely specified \(5\times5\) rational linear system**. It requires no optimization and determines exact rational numbers for every sufficiently large integer \(m\).

Elementary determinant expansion of (118), for *each* of the four residues \(r\), yields the same leading term

\[
\det A_r(m)=-192m^9+O(m^8), \tag{119}
\]

so the system is invertible for all sufficiently large \(m\). Cramer's rule, again applied to the displayed five columns, gives the uniform leading expansions

\[
\begin{aligned}
p_I&=1-\frac{9}{2m}+O(m^{-2}),\\
p_K&=\frac4m+O(m^{-2}),&
p_H&=\frac1{2m}+O(m^{-2}),\\
q_E&=\frac4{3m}+O(m^{-2}),&
q_T&=1-\frac4{3m}+O(m^{-2}).
\end{aligned}\tag{120}
\]

The determinant identities and every limit in (119)–(120) can be replayed by *exact symbolic arithmetic*; an independent script is given in
\nolinkurl{code/check_three_subset_asymptotic_algebra.py}.
The leading coefficients in (120) ensure **all five weights are strictly positive for all sufficiently large \(m\)**, and their exact normalizations and orbital moments are already built into (118).

Define conjugation-invariant probability measures

\[
P_n=p_I U_I+p_KU_K+p_HU_H,\qquad
Q_n=q_TU_T+q_EU_E, \tag{121}
\]

where \(U_\mathcal C\) denotes the uniform distribution on a conjugacy class. Their supports are disjoint for sufficiently large \(m\). Because the action on ordered pairs of three-element subsets has exactly the four orbitals determined by their intersection sizes, (118) implies that \(P_n,Q_n\) have the same **complete triple-image marginals**. Thus the exact signed perturbation
\(u_{S_n}+\delta(P_n-Q_n)\) is a probability law for every sufficiently small rational \(\delta>0\), with TV distance \(\delta\) and atom increase \(p_I\delta\).

The general orbital theorem therefore gives

\[
C_n^{(3)}\ge p_I
=1-\frac{9}{2m}+O(m^{-2})
=1-\frac{18}{n}+O(n^{-2}),
\tag{122}
\]

uniformly over all four residues modulo four.

### 22.3. Sharp asymptotic completion

Combine (122) with (109), valid for all \(n\ge2048\). The two bounds match at order \(1/n\), giving (108) with an error \(O(n^{-2})\) and the **exact first-order constant \(18\)**.

The asymptotic theorem is logically independent of the fixed \(n\le120\) table. Its proof consists of a universal orbital dual, an exact polynomial expansion and global real-variable inequalities, and four rational primal families with directly checkable full moment equations. It does **not** prove that those particular families are exactly optimal at every sufficiently large finite degree; proving eventual exact support stabilization and explicit parity-wise formulas remains open.


## 23. General \(k\)-subset orbital Bernstein limits and a Chebyshev research direction

The first-order constants \(2,8,18\) in the one-, two-, and three-subset actions have a common structure. The orbital basis of **every fixed subset rank** converges to the Bernstein polynomial basis, while the explicit duals in ranks \(1,2,3\) converge to *shifted Chebyshev polynomials*. The first observation is a rigorously proved general theorem. Its extension to a sharp all-\(k\) atom-TV asymptotic remains a conjecture.

Let \(1\le k\le n\), let \(\Omega_{n,k}=\binom{[n]}k\), and define

\[
F_j^{(k)}(g)
=\#\{E\in\Omega_{n,k}:|E\cap g(E)|=j\}
\quad(0\le j\le k).
\]

Write \(x(g)\) for the number of fixed vertices and \(a(g)=x(g)/n\). Define the Bernstein basis
\(B_{j,k}(a)=\binom kj a^j(1-a)^{k-j}\).

**Theorem 23 (uniform Bernstein orbital approximation).** For every \(n\ge\max(k,2)\), every permutation \(g\in S_n\), and every \(0\le j\le k\),

\[
\boxed{
\left|\frac{F_j^{(k)}(g)}{\binom nk}
       -B_{j,k}(a(g))\right|
\le\frac{k(k-1)}{n-1}+\frac{k(k-1)}{2n}.
} \tag{123}
\]

Indeed the **total variation distance between the entire two distributions** on \(j=0,\ldots,k\) satisfies the same bound. Consequently for every fixed \(k\), the \(k+1\) normalized orbital statistics converge uniformly over \(g\in S_n\), at rate \(O_k(n^{-1})\), to the Bernstein basis of polynomials of degree at most \(k\).

**Proof.** Choose a uniformly random \(k\)-subset \(E\), and let \(X=|E\cap g(E)|\). Let \(S\) be the fixed-vertex set of \(g\), with \(|S|=x\), and put \(Y=|E\cap S|\). Every fixed vertex in \(E\) also belongs to \(g(E)\), hence \(X\ge Y\). Any extra element \(v\in E\cap g(E)\setminus S\) requires the two **distinct** vertices \(v\) and \(g^{-1}(v)\) both to belong to \(E\). For each moved vertex \(v\), the probability of this pair event is exactly \(k(k-1)/(n(n-1))\). By the union bound,

\[
\mathbb P(X\ne Y)
\le (n-x)\frac{k(k-1)}{n(n-1)}
\le\frac{k(k-1)}{n-1}. \tag{124}
\]

The variable \(Y\) has the hypergeometric distribution of the number of successes in \(k\) draws without replacement from a population of \(n\) with \(x\) successes. Draw instead \(k\) vertices independently and uniformly with replacement, and let \(Z\sim\operatorname{Binomial}(k,x/n)\) count successes. The distribution of the ordered independent sample **conditioned on distinctness** is exactly that of ordered sampling without replacement. The probability of a collision is at most \(\binom k2/n=k(k-1)/(2n)\); thus the total variation distance between \(Y\) and \(Z\) is at most this probability. By the coupling characterization and the triangle inequality,

\[
d_{\mathrm{TV}}\bigl(\mathcal L(X),\mathcal L(Z)\bigr)
\le\mathbb P(X\ne Y)+
d_{\mathrm{TV}}\bigl(\mathcal L(Y),\mathcal L(Z)\bigr),
\]

which is (123) for the full distributions and hence for each coordinate. QED.

**Proposition 24 (Chebyshev limiting duals in ranks \(1,2,3\)).** Let \(T_k\) denote the Chebyshev polynomial of the first kind, \(T_k(\cos\theta)=\cos(k\theta)\). In each of the already proved ranks \(k=1,2,3\), the leading nonidentity orbital dual polynomial of the sharp or sharp-order certificates is

\[
\boxed{H_k(a)=\frac{1-T_k(2a-1)}2,}
\]

namely

\[
H_1(a)=1-a,\qquad
H_2(a)=4a(1-a),\qquad
H_3(a)=(1-a)(4a-1)^2.
\tag{125}
\]

All satisfy \(0\le H_k(a)\le1\) for \(0\le a\le1\), \(H_k(1)=0\), and the endpoint derivative identity

\[
-H_k'(1)=k^2. \tag{126}
\]

**Proof.** The polynomial identities follow by substituting \(T_1(t)=t\), \(T_2(t)=2t^2-1\), and \(T_3(t)=4t^3-3t\). For \(k=1\), the fixed-point dual \(h(g)=\mathbf1_{\{g=e\}}+(n-x(g))/n\) has nonidentity profile \(H_1(x/n)\) exactly. For \(k=2\), the exact duals (76) and (81) have the common leading nonidentity profile \(4a(1-a)\): substitute the leading terms of (68) with \(x=an\) and \(y=O(n)\). For \(k=3\), equation (113) provides the exact leading polynomial \(H_3\). The range and derivative statements follow from \(|T_k(t)|\le1\) on \([-1,1]\) and \(T_k'(1)=k^2\). QED.

This exhibits why the exact first-order constants are

\[
\begin{array}{c|c}
k & \displaystyle\lim_{n\to\infty}n(1-C_n^{(k)})\\ \hline
1&2\quad\text{(Theorem 15)},\\
2&8\quad\text{(Theorem 17)},\\
3&18\quad\text{(Theorem 22)}.
\end{array}
\tag{127}
\]

A nonidentity vertex permutation must move at least two vertices, so the closest possible fixed-point fraction to \(1\) is \(1-2/n\). For a shifted Chebyshev dual, the endpoint loss is therefore \(2k^2/n+O_k(n^{-2})\). This interpretation is exact for the three established ranks; it motivates but **does not prove** the following general question.

**Conjecture (higher-rank sharp atom modulus).** For every fixed \(k\ge4\), the optimal coefficient for \(S_n\) acting on its \(k\)-subsets satisfies

\[
C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2})
\qquad(n\to\infty). \tag{128}
\]

A viable proof must address **both sides**: construct a uniformly valid orbital dual with the appropriate subleading corrections, and match it by genuine nonnegative class measures with exactly equal \(k\)-subset image marginals. Theorem 23 alone proves only Bernstein convergence; it does not control the \(1/n\) coefficient or justify a Chebyshev optimizer. Numerical LP output at fixed degrees also cannot establish (128). The general theorem is left **explicitly open**.


## Part J: All-rank transfer, hierarchy and four-subset certificates

## J.1. Definitions

Let \(n\ge2\), \(1\le k\le n\), \(G=S_n\), \(\Omega=\binom{[n]}k\), and \(u\) the uniform probability on \(G\). Define \(\mathcal C_{n,k}\) as the least number such that all probability laws \(\nu\) on \(G\) with uniform image marginals

\[
\nu\{g:gE=H\}=1/\binom nk\qquad(E,H\in\Omega)
\]

satisfy

\[
|\nu(\sigma)-1/n!|\le\mathcal C_{n,k}\|\nu-u\|_{\rm TV}
\quad\text{for every }\sigma\in G.
\]

For \(g\in G\) let \(m_\ell(g)\) be its count of cycles of length \(\ell\), and put

\[
F_j(g)=\#\{E\in\Omega:|E\cap gE|=j\},\qquad 0\le j\le k.
\]

## J.2. All-k transfer identity

**Theorem J.A (short-cycle sufficiency).** In the formal power series ring \(\mathbb Q[t][[s]]\), let \(L_+\) and \(L_-\) be the two roots of

\[
L^2-(1+st)L+s(t-1)=0,\qquad
L_+=1+O(s),\quad L_-=O(s).
\]

Then for every \(g\in S_n\),

\[
\boxed{\displaystyle
\sum_{j=0}^k F_j(g)t^j
=[s^k]\,L_+^n\prod_{\ell=1}^k
\left(1+(L_-/L_+)^\ell\right)^{m_\ell(g)}.}
\tag{J.1}
\]

Therefore all \(k+1\) intersection-orbital displacement statistics depend solely on \(n\) and \(m_1(g),\ldots,m_k(g)\); longer-cycle data are irrelevant.

*Proof.* On a cycle \((v_1,\ldots,v_\ell)\), mark membership in a subset \(E\) by cyclic bits \(b_i\in\{0,1\}\). The transition \(b_i\) to \(b_{i+1}\) has weight \(s^{b_{i+1}}t^{b_ib_{i+1}}\). Thus for

\[
T=\begin{pmatrix}1&s\\1&st\end{pmatrix},
\qquad Z_\ell(s,t)=\operatorname{tr}(T^\ell),
\]

the trace enumerates all cyclic binary words with weight \(s^{|E\cap\text{cycle}|}t^{|E\cap gE\cap\text{cycle}|}\). Independence of cycles gives the exact polynomial identity

\[
\sum_{E\subseteq[n]}s^{|E|}t^{|E\cap gE|}
=\prod_{\ell\ge1}Z_\ell(s,t)^{m_\ell(g)}. \tag{J.2}
\]

The characteristic polynomial of \(T\) is the polynomial in the theorem. Its discriminant \(1+(4-2t)s+t^2s^2\) has constant term 1, so its formal square root, and hence the designated roots, exist uniquely. The root \(L_+\) is invertible while \(L_-/L_+\) is divisible by \(s\). The trace identity gives \(Z_\ell=L_+^\ell+L_-^\ell\). Extract \(L_+^{\sum\ell m_\ell}=L_+^n\) from (J.2). For every \(\ell>k\), the remaining factor is congruent to 1 modulo \(s^{k+1}\). Extract coefficient \(s^k\) to obtain (J.1). QED.

This is a transfer-matrix realization of a classical character-polynomial phenomenon. We do not claim that short-cycle dependence is historically unprecedented.

**Lemma J.B (complete feasible spectrum).** A nonnegative integer vector \(a=(a_1,\ldots,a_k)\) occurs as the list of short-cycle multiplicities of some \(g\in S_n\) if and only if

\[
r=n-\sum_{\ell=1}^k\ell a_\ell
\quad\text{is either }0\text{ or at least }k+1. \tag{J.3}
\]

*Proof.* Any unrecorded cycle has length at least \(k+1\). Conversely realize the specified cycles and, when \(r>0\), append one \(r\)-cycle. QED.

Write \(A_{n,k}\) for the feasible vectors. They number at most

\[
\prod_{\ell=1}^k(\lfloor n/\ell\rfloor+1)=O_k(n^k).
\tag{J.4}
\]

The [exact transfer evaluator](../../notes/johnson-short-cycle-spectrum/transfer.py) computes all moments for a vector \(a\) from the equivalent truncated expression

\[
[s^k]\,L_+^r\prod_{\ell=1}^kZ_\ell^{a_\ell}, \tag{J.5}
\]

using integer polynomial arithmetic alone.

## J.3. Universal polynomial-size rational optimization

**Theorem J.C.** Let \(e=(n,0,\ldots,0)\) denote the identity short-cycle type, and compute \(F_j(a)\) by (J.1). The sharp coefficient \(\mathcal C_{n,k}\) equals the rational linear-programming optimum

\[
\max_{p,q}(p_e-q_e),
\quad
p_a,q_a\ge0,\quad
\sum_a p_a=\sum_a q_a=1,\quad
\sum_a(p_a-q_a)F_j(a)=0\ (0\le j\le k).
\tag{J.6}
\]

The same number is the minimum oscillation, over \(a\in A_{n,k}\), of

\[
h(a)=\mathbf1_{\{a=e\}}-\sum_{j=0}^k\lambda_jF_j(a),
\tag{J.7}
\]

over rational \(\lambda_j\). The two optima are attained and rational. For fixed \(k\), (J.6) has \(O_k(n^k)\) variables and \(O(k)\) equations and is exactly solvable in time polynomial in \(n\), with polynomial-bit-length rational data. No polynomial-in-\(\log n\) assertion is intended.

*Proof.* For a signed measure \(v=\nu-u\) annihilating all image marginal indicators, its normalized Jordan parts are probabilities \(P,Q\) with equal image marginals. Conversely, a pair \(P,Q\) with equal image marginals yields such a signed perturbation, and its atom objective divided by total variation is at least \(P(e)-Q(e)\). Thus maximizing the latter over probability pairs gives the sharp local atom-to-TV coefficient. Simultaneous conjugation averaging keeps the identity atom fixed, preserves the marginal equalities, and cannot increase total variation, so central pairs suffice.

For central laws on \(S_n\), the diagonal action on ordered pairs of \(k\)-sets has orbitals indexed by \(j=|E\cap H|\). Each feasible orbital has \(\binom nk\binom kj\binom{n-k}{k-j}\) ordered pairs. The probability assigned to an individual ordered pair within orbital \(j\) is \(\mathbb E F_j\) divided by that cardinality. Consequently matching all the \(F_j\)-moments is exactly equivalent to matching *every* image marginal. Theorem J.A shows that classes sharing a short-cycle vector have identical moment columns, and Lemma J.B constructs an actual representative class for each vector. Moving central masses to these representative classes therefore loses no primal solution or objective value. This proves (J.6).

Subtracting any linear combination of the zero moment differences from the identity indicator bounds \(P(e)-Q(e)\) by the oscillation of (J.7). Conversely, finite LP strong duality with the two probability normalization equations yields the minimum-oscillation dual, including attainment and rationality. A positive optimal pair has disjoint support: otherwise normalizing its signed Jordan parts would strictly improve the objective. Thus \(u+\delta(P-Q)\) is a genuine marginal-preserving probability measure for sufficiently small positive rational \(\delta\), attaining equality. Left translation treats any prescribed atom. Finally (J.4)--(J.5) give polynomially many integer moment evaluations at fixed \(k\), with polynomial bit lengths; standard rational LP algorithms establish the complexity statement. QED.

This is an all-degree **exact algorithm**, not a closed formula for every \(\mathcal C_{n,k}\).

## J.4. New sharp rank-five coefficients for four-subsets

**Theorem J.D (certified degrees 11--25).** For \(S_n\) acting on four-element subsets, the exact sharp values are:

| \(n\) | \(\mathcal C_{n,4}\) | \(n\) | \(\mathcal C_{n,4}\) |
|---:|---:|---:|---:|
|11|1629/4549|19|445133/1091945|
|12|131/357|20|4147/9871|
|13|6817/18427|21|352459/826455|
|14|3106/8153|22|28029/64307|
|15|1345/3493|23|5926/13479|
|16|3591/9187|24|3441/7621|
|17|29846/75821|25|42843/94103|
|18|211/523|||

*Exact certificate proof.* The [standalone checker](../../notes/johnson-short-cycle-spectrum/check_k4.py) contains, for each degree, **five literal support vectors** of short-cycle multiplicities: two nonidentity positive supports, three negative supports, and the identity as the third positive support. The six resulting conjugacy classes are distinct and realizable by Lemma J.B. For each positive type \(a\) form the row

\[
(1,0,F_0(a),F_1(a),F_2(a),F_3(a)),
\]

and for each negative type form

\[
(0,1,-F_0(a),-F_1(a),-F_2(a),-F_3(a)).
\]

Let \(B\) be this six-by-six matrix, ordered with identity first. The checker solves both exact rational systems

\[
B^{\mathsf T}w=(1,1,0,0,0,0)^{\mathsf T},
\qquad
By=(1,0,0,0,0,0)^{\mathsf T}. \tag{J.8}
\]

It checks nonsingularity, strict positivity of the six primal weights, both probability normalizations, and equality of **all five** orbital moments (the fifth follows from their constant sum). It independently checks that \(w_0=y_0+y_1\) equals the claimed tabulated fraction. With

\[
h(a)=\mathbf1_{\{a=e\}}-\sum_{j=0}^3 y_{j+2}F_j(a),
\]

the checker verifies for **every** feasible \(a\in A_{n,4}\) that \(-y_1\le h(a)\le y_0\), with upper and lower contacts on all positive and negative support classes respectively. Because Theorem J.A includes every possible conjugacy class, no dual constraint is omitted.

Distribute each support's rational weight uniformly on its canonical conjugacy class. The checker computes exact positive class cardinalities \(n!/\prod_\ell\ell^{m_\ell}m_\ell!\), then verifies a positive rational perturbation scale \(\delta\) for which \(u+\delta(P-Q)\) is nonnegative and has the required marginals. The matching dual bound, primal attainment and Theorem J.C prove all 15 exact values. QED.

## J.5. Reproduction and trust boundaries

Run these two commands from the repository root:

~~~sh
python3 notes/johnson-short-cycle-spectrum/transfer.py
python3 notes/johnson-short-cycle-spectrum/check_k4.py
~~~

Only Python standard-library integer arithmetic and Fraction arithmetic are used; no optimizer, third-party solver, randomness or floating-point inequality appears on the proof path. The first script checks (J.5) against literal subset-image enumeration for **1,329** triples \((n,k,\text{conjugacy type})\) with \(3\le n\le12\) and \(1\le k\le\min(n,5)\). The second reconstructs exact rational primal/dual witnesses from the literal support vectors and exhausts every feasible reduced type in each degree 11--25. Its assertion-based verifier **rejects optimized Python mode (-O)** to avoid silent disabling of checks.

A numerical LP was used only in the discovery stage to identify compact supports; the published programs do not require or trust those solutions. Theorems A--C are mathematical proofs, not conclusions drawn from the finite test runs. Theorem J.D is a finite exact, independently replayable certificate argument conditional only on standard Python integer/Fraction semantics and the proven reduction. The full higher-k explicit classification and all-degree formulas remain open.

**Internal antecedent:** the [general orbital duality theorem](../../notes/sharp-robust-permanent/paper.md) and its separate exact three-subset \(n\le120\) certificates. That line of work was initially inspired by the OpenAI [four-row permanent and permutation moments](https://github.com/openai/math/tree/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026) manuscript; the fixed-k transfer calculation and rank-five certificates here are separate deductions.


## J.6. A universal hierarchy under increasing subset rank

**Theorem J.E (monotone atom moduli).** For every integer \(n\ge2\) and every \(1\le \ell\le k\le n-\ell\),

\[
\boxed{\mathcal C_{n,k}\le \mathcal C_{n,\ell}.}\tag{J.9}
\]

Furthermore \(\mathcal C_{n,k}=\mathcal C_{n,n-k}\), so in every fixed degree \(n\), the sequence of sharp moduli is nonincreasing as the subset size approaches \(\lfloor n/2\rfloor\):

\[
\mathcal C_{n,1}\ge\mathcal C_{n,2}\ge\cdots
\ge\mathcal C_{n,\lfloor n/2\rfloor}.
\tag{J.10}
\]

*Proof.* First establish an exact full-column-rank lemma for inclusion matrices over \(\mathbb R\). If \(0\le\ell\le k\le n-\ell\), let \(W_{\ell,k}\) send a function \(f\) on the \(\ell\)-subsets of \([n]\) to the function on \(k\)-subsets

\[
(W_{\ell,k}f)(E)=\sum_{\substack{S\subseteq E\\|S|=\ell}} f(S).
\]

We claim \(W_{\ell,k}\) is injective. Induct on \(\ell\). For \(\ell=0\), the statement is immediate. For \(\ell\ge1\), suppose \(W_{\ell,k}f=0\), and choose distinct vertices \(a,b\). Subtract the vanishing inclusion sums on \(T\cup\{a\}\) and \(T\cup\{b\}\), for each \((k-1)\)-subset \(T\subseteq[n]\setminus\{a,b\}\). The result is

\[
\sum_{\substack{U\subseteq T\\|U|=\ell-1}}
\bigl(f(U\cup\{a\})-f(U\cup\{b\})\bigr)=0.
\]

The induction hypothesis applies on \(n-2\) vertices with parameters \(\ell-1,k-1\), since \(\ell-1\le k-1\le(n-2)-(\ell-1)\). Hence \(f(U\cup\{a\})=f(U\cup\{b\})\) for every \((\ell-1)\)-subset \(U\) disjoint from \(a,b\). Every pair of adjacent vertices in the Johnson graph of \(\ell\)-sets therefore has equal \(f\)-value. That graph is connected, so \(f\) is constant. Because \(W_{\ell,k}f=0\) and \(\binom{k}{\ell}>0\), this constant is zero. The injectivity claim follows.

Now let \(V_j\) be the real permutation representation on \(j\)-subsets and \(\rho_j(g)\) its permutation matrix. By construction, inclusion intertwines the two actions:

\[
\rho_k(g)W_{\ell,k}=W_{\ell,k}\rho_\ell(g)\qquad(g\in S_n).
\]

If a law \(\nu\) has uniform \(k\)-subset image marginals, then the averaged action matrices satisfy
\(\sum_g\nu(g)\rho_k(g)=\sum_gu(g)\rho_k(g)\).
Right-multiply by \(W_{\ell,k}\), use intertwining, and invoke injectivity to get the analogous equality on \(V_\ell\). Hence every law with uniform \(k\)-set marginals also has uniform \(\ell\)-set marginals. The former class of probability laws is contained in the latter, and the definition of the sharp atom/TV coefficient gives (J.9).

Finally, complementation \(E\mapsto[n]\setminus E\) is an equivariant bijection between \(k\)-subsets and \((n-k)\)-subsets, so the corresponding marginal constraints and sharp constants are identical. This proves (J.10). QED.

The finite certified tables in the present note and the predecessor's three-subset note furnish strict instances of this inequality. Theorem J.E does **not** claim strictness for every degree or rank, and (J.10) is a structural comparison rather than a closed formula for the moduli.


## J.7. Complete certified four-subset continuation in degrees 26--50

**Theorem J.F.** For every integer \(26\le n\le50\), the exact sharp
coefficient for the \(S_n\) action on four-element subsets is the rational
number in the following table. Together with Theorem J.D, this determines
every degree \(11\le n\le50\). No exact all-degree four-subset formula or
higher-rank asymptotic is asserted.

**Proof.** The fixed file
[k4_n26_50.json](../../notes/johnson-short-cycle-spectrum/certificates/k4_n26_50.json)
specifies, at each of the 25 degrees, two nonidentity positive short-cycle
supports and three negative supports. Adding the identity gives the six
supports used by the rational linear systems in Theorem J.D. Each support
is realized by its prescribed cycles and a single remaining long cycle, as
in Lemma J.B. The separate
[optimizer-free checker](../../notes/johnson-short-cycle-spectrum/check_k4_26_50.py)
constructs the exact integer moment matrix using the proved transfer identity,
solves the primal and dual systems by rational Gaussian elimination, and
checks nonsingularity, strictly positive primal weights, both mass sums and
all orbital moment equalities. It enumerates every feasible short-cycle
vector and verifies both dual bounds and the support contacts. The moment
sum is constant, so the omitted redundant fifth moment also agrees.

The identity weight equals the table entry and the dual oscillation.
Theorem J.C therefore gives the upper bound and primal attainment. The
checker also computes actual conjugacy-class sizes and a positive rational
scale for which the signed perturbation of the uniform law is nonnegative;
thus these are genuine marginal-preserving probability witnesses, not merely
formal LP solutions. All 25 degrees and all feasible types in each degree are
covered by fixed literal input. The complete exhaustive replay is part of
the finite proof, with its output and source hashes supplied. No discovery
solver is needed. QED.

The table is transcribed from that fixed JSON, not rounded numerical output.


| Degree | Exact coefficient |
| ---: | ---: |
| 26 | 31178983/66734529 |
| 27 | 26088187/55219671 |
| 28 | 9453205/19608553 |
| 29 | 322763823/664532107 |
| 30 | 17347/34965 |
| 31 | 1357637/2711805 |
| 32 | 13419459/26302163 |
| 33 | 63151229/122751769 |
| 34 | 103729849/197908557 |
| 35 | 322089109/610631637 |
| 36 | 518431/968035 |
| 37 | 63992175/118545464 |
| 38 | 12069/22006 |
| 39 | 1994479855/3611361227 |
| 40 | 25257571/45082011 |
| 41 | 85610/151749 |
| 42 | 5675965/9942766 |
| 43 | 206491499/359673689 |
| 44 | 484007989/831880833 |
| 45 | 66083917/112885639 |
| 46 | 35548943/60064597 |
| 47 | 12483647731/20967181867 |
| 48 | 4261003/7081915 |
| 49 | 2304798951/3811510114 |
| 50 | 297240803/486850773 |


## Appendix P. Exact rational-polynomial certificate for the infinite primal families

The primal families in Section 22.2 can be verified without a computer algebra
system. Let \(A_r(m)\) be the displayed five-by-five matrix, with columns
\(I,K,H,-T,-E\) in its moment rows and the two probability rows as in (118).
Let \(D_r=\det A_r\), and let \(N_I,N_K,N_H,N_T,N_E\) be its five Cramer
numerators, replacing the respective column by \((1,1,0,0,0)^T\).
All are polynomials over \(\mathbb Q\). The exact identities are
\[
A_r(m)(N_I,N_K,N_H,N_T,N_E)^T
 =D_r(m)(1,1,0,0,0)^T,
\]
\[
N_I+N_K+N_H=D_r,
\qquad N_T+N_E=D_r.
\]
For every residue \(r=0,1,2,3\), \(D_r,N_I,N_T\) have degree nine with
leading coefficient \(-192\). Their next coefficients are:

| Residue \(r\) | \([m^8]D_r\) | \([m^8]N_I\) | \([m^8]N_T\) |
| ---: | ---: | ---: | ---: |
| 0 | -304 | 560 | -48 |
| 1 | -752 | 112 | -496 |
| 2 | -1200 | -336 | -944 |
| 3 | -1616 | -752 | -1360 |

The other three numerators have degree eight with leading coefficients
\[
[m^8]N_K=-768,\qquad [m^8]N_H=-96,\qquad [m^8]N_E=-256.
\]
In all four cases \([m^8](D_r-N_I)=-864\) and
\([m^8](D_r-N_T)=-256\). Dividing the numerator polynomials by \(D_r\)
therefore gives exactly the five expansions in (120). Positive leading ratios
give eventual positivity; the degree-nine nonzero denominator gives eventual
invertibility. With four fixed residue classes these conclusions are uniform.
The concrete support types are distinct and realizable for \(m\ge6\);
the certificate also checks their short-cycle counts and remaining long cycle.

The independent
[rational-polynomial checker](../../verification/finalization/check_cramer_polynomials.py)
stores a polynomial as its finite list of Fraction coefficients. It constructs
the moment matrix directly from (99)--(100), expands each determinant by all
120 terms in the Leibniz formula, and compares every coefficient in the five
Cramer identities and both normalization identities. It checks the displayed
degree and leading/next coefficients, and supplies every full polynomial in
its [recorded output](../../verification/finalization/results/cramer-polynomials.json).
Thus it verifies identities for all parameter values, rather than testing
several integers \(m\). The analytic passage to eventual positivity and the
global dual inequalities are still the written steps of Theorem 22.

```sh
python3 -B verification/finalization/check_cramer_polynomials.py
python3 -O -B verification/finalization/check_cramer_polynomials.py
```

Both executions must produce the same exact coefficient lists. This independent
checker uses only standard-library integer and rational arithmetic, with explicit
guards that cannot be stripped by `-O`. It complements the earlier SymPy
expansion replay and does not require or trust a discovery optimizer.
