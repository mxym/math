# Fixed-k Johnson orbital compression and exact four-subset moduli

Research note, 8 October 2026. This note extends the [orbital primal-dual method](../sharp-robust-permanent/paper.md) from particular permutation actions to all symmetric-group actions on fixed-size subsets, and certifies 40 exact sharp constants for the four-subset action through degree 50. The parent work already contains the independent three-subset classification through degree 120; the present four-subset computation is distinct. No novelty priority, outside peer review, or Lean formalization is asserted.

## Related rigorous continuations

- **Sharp all-rank/middle-rank 5/14 theorem.** The [complete proof](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md) establishes **exactly** \(C_n^{\rm all}=C_{n,\lfloor n/2\rfloor}=5/14\) for every \(n\ge6\), with a five-point rational dual verified on all 44,582 finite nontrivial cycle partitions and an analytic bound for every remaining permutation. The theorem extends as a universal sharp upper coefficient to faithful permutation subgroups, and classifies the possible equality-support cycle shapes and total class masses. [Independent integer and Fraction audit](VERIFICATION.md), including mutation controls. No historical priority or outside review is claimed.

- **All fixed ranks, sharp asymptotics.** The [separate all-k Chebyshev proof](ALL_K_CHEBYSHEV_ASYMPTOTICS.md) establishes \(C_{n,k}=1-2k^2/n+O_k(n^{-2})\) for every fixed \(k\) and an eventual strict gap \(C_{n,k}-C_{n,k+1}=(4k+2)/n+O_k(n^{-2})\). The same principal theorem was proved independently and **earlier** by a parallel task as [Theorem 25 in the parent manuscript](../sharp-robust-permanent/paper.md); our supplement gives an alternative rational-coefficient dual construction. The [separate k=4 explicit asymptotic note](ASYMPTOTIC_RANK_FIVE.md) supplies a quantitative upper bound and its independent symbolic checker.
- **Five-subset exact classification.** The [rank-six note](RANK_SIX_EXACT_11_40.md) gives **30 sharp rational constants for all \(n=11,\ldots,40\)**, including 26 new exact 7-class primal-dual certificates and 4 exceptional 4-class certificates.
- **Simultaneous all-rank structure.** The [trace-kernel theorem](ALL_RANK_TRACE_KERNEL.md) proves the entire span of all Johnson-action orbital class functions in degree \(n\) has rank precisely \(\lfloor n/2\rfloor+1\), and an exact four-class probability relation preserves **all** subset-image marginal matrices simultaneously.
- **Independent verification.** The [pinned replay report](VERIFICATION.md) contains source hashes, all exact finite checks and mutation controls; numerics were discovery-only.

## 1. Definitions

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

## 2. All-k transfer identity

**Theorem A (short-cycle sufficiency).** In the formal power series ring \(\mathbb Q[t][[s]]\), let \(L_+\) and \(L_-\) be the two roots of

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
\tag{1}
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
=\prod_{\ell\ge1}Z_\ell(s,t)^{m_\ell(g)}. \tag{2}
\]

The characteristic polynomial of \(T\) is the polynomial in the theorem. Its discriminant \(1+(4-2t)s+t^2s^2\) has constant term 1, so its formal square root, and hence the designated roots, exist uniquely. The root \(L_+\) is invertible while \(L_-/L_+\) is divisible by \(s\). The trace identity gives \(Z_\ell=L_+^\ell+L_-^\ell\). Extract \(L_+^{\sum\ell m_\ell}=L_+^n\) from (2). For every \(\ell>k\), the remaining factor is congruent to 1 modulo \(s^{k+1}\). Extract coefficient \(s^k\) to obtain (1). QED.

This is a transfer-matrix realization of a classical character-polynomial phenomenon. We do not claim that short-cycle dependence is historically unprecedented.

**Lemma B (complete feasible spectrum).** A nonnegative integer vector \(a=(a_1,\ldots,a_k)\) occurs as the list of short-cycle multiplicities of some \(g\in S_n\) if and only if

\[
r=n-\sum_{\ell=1}^k\ell a_\ell
\quad\text{is either }0\text{ or at least }k+1. \tag{3}
\]

*Proof.* Any unrecorded cycle has length at least \(k+1\). Conversely realize the specified cycles and, when \(r>0\), append one \(r\)-cycle. QED.

Write \(A_{n,k}\) for the feasible vectors. They number at most

\[
\prod_{\ell=1}^k(\lfloor n/\ell\rfloor+1)=O_k(n^k).
\tag{4}
\]

The [exact transfer evaluator](transfer.py) computes all moments for a vector \(a\) from the equivalent truncated expression

\[
[s^k]\,L_+^r\prod_{\ell=1}^kZ_\ell^{a_\ell}, \tag{5}
\]

using integer polynomial arithmetic alone.

## 3. Universal polynomial-size rational optimization

**Theorem C.** Let \(e=(n,0,\ldots,0)\) denote the identity short-cycle type, and compute \(F_j(a)\) by (1). The sharp coefficient \(\mathcal C_{n,k}\) equals the rational linear-programming optimum

\[
\max_{p,q}(p_e-q_e),
\quad
p_a,q_a\ge0,\quad
\sum_a p_a=\sum_a q_a=1,\quad
\sum_a(p_a-q_a)F_j(a)=0\ (0\le j\le k).
\tag{6}
\]

The same number is the minimum oscillation, over \(a\in A_{n,k}\), of

\[
h(a)=\mathbf1_{\{a=e\}}-\sum_{j=0}^k\lambda_jF_j(a),
\tag{7}
\]

over rational \(\lambda_j\). The two optima are attained and rational. For fixed \(k\), (6) has \(O_k(n^k)\) variables and \(O(k)\) equations and is exactly solvable in time polynomial in \(n\), with polynomial-bit-length rational data. No polynomial-in-\(\log n\) assertion is intended.

*Proof.* For a signed measure \(v=\nu-u\) annihilating all image marginal indicators, its normalized Jordan parts are probabilities \(P,Q\) with equal image marginals. Conversely, a pair \(P,Q\) with equal image marginals yields such a signed perturbation, and its atom objective divided by total variation is at least \(P(e)-Q(e)\). Thus maximizing the latter over probability pairs gives the sharp local atom-to-TV coefficient. Simultaneous conjugation averaging keeps the identity atom fixed, preserves the marginal equalities, and cannot increase total variation, so central pairs suffice.

For central laws on \(S_n\), the diagonal action on ordered pairs of \(k\)-sets has orbitals indexed by \(j=|E\cap H|\). Each feasible orbital has \(\binom nk\binom kj\binom{n-k}{k-j}\) ordered pairs. The probability assigned to an individual ordered pair within orbital \(j\) is \(\mathbb E F_j\) divided by that cardinality. Consequently matching all the \(F_j\)-moments is exactly equivalent to matching *every* image marginal. Theorem A shows that classes sharing a short-cycle vector have identical moment columns, and Lemma B constructs an actual representative class for each vector. Moving central masses to these representative classes therefore loses no primal solution or objective value. This proves (6).

Subtracting any linear combination of the zero moment differences from the identity indicator bounds \(P(e)-Q(e)\) by the oscillation of (7). Conversely, finite LP strong duality with the two probability normalization equations yields the minimum-oscillation dual, including attainment and rationality. A positive optimal pair has disjoint support: otherwise normalizing its signed Jordan parts would strictly improve the objective. Thus \(u+\delta(P-Q)\) is a genuine marginal-preserving probability measure for sufficiently small positive rational \(\delta\), attaining equality. Left translation treats any prescribed atom. Finally (4)--(5) give polynomially many integer moment evaluations at fixed \(k\), with polynomial bit lengths; standard rational LP algorithms establish the complexity statement. QED.

This is an all-degree **exact algorithm**, not a closed formula for every \(\mathcal C_{n,k}\).

## 4. New sharp rank-five coefficients for four-subsets

**Theorem D (certified degrees 11--25).** For \(S_n\) acting on four-element subsets, the exact sharp values are:

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

*Exact certificate proof.* The [standalone checker](check_k4.py) contains, for each degree, **five literal support vectors** of short-cycle multiplicities: two nonidentity positive supports, three negative supports, and the identity as the third positive support. The six resulting conjugacy classes are distinct and realizable by Lemma B. For each positive type \(a\) form the row

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
By=(1,0,0,0,0,0)^{\mathsf T}. \tag{8}
\]

It checks nonsingularity, strict positivity of the six primal weights, both probability normalizations, and equality of **all five** orbital moments (the fifth follows from their constant sum). It independently checks that \(w_0=y_0+y_1\) equals the claimed tabulated fraction. With

\[
h(a)=\mathbf1_{\{a=e\}}-\sum_{j=0}^3 y_{j+2}F_j(a),
\]

the checker verifies for **every** feasible \(a\in A_{n,4}\) that \(-y_1\le h(a)\le y_0\), with upper and lower contacts on all positive and negative support classes respectively. Because Theorem A includes every possible conjugacy class, no dual constraint is omitted.

Distribute each support's rational weight uniformly on its canonical conjugacy class. The checker computes exact positive class cardinalities \(n!/\prod_\ell\ell^{m_\ell}m_\ell!\), then verifies a positive rational perturbation scale \(\delta\) for which \(u+\delta(P-Q)\) is nonnegative and has the required marginals. The matching dual bound, primal attainment and Theorem C prove all 15 exact values. QED.

## 5. Reproduction and trust boundaries

Run these two commands from the repository root:

~~~sh
python3 notes/johnson-short-cycle-spectrum/transfer.py
python3 notes/johnson-short-cycle-spectrum/check_k4.py
~~~

Only Python standard-library integer arithmetic and Fraction arithmetic are used; no optimizer, third-party solver, randomness or floating-point inequality appears on the proof path. The first script checks (5) against literal subset-image enumeration for **1,329** triples \((n,k,\text{conjugacy type})\) with \(3\le n\le12\) and \(1\le k\le\min(n,5)\). The second reconstructs exact rational primal/dual witnesses from the literal support vectors and exhausts every feasible reduced type in each degree 11--25. Its assertion-based verifier **rejects optimized Python mode (-O)** to avoid silent disabling of checks.

A numerical LP was used only in the discovery stage to identify compact supports; the published programs do not require or trust those solutions. Theorems A--C are mathematical proofs, not conclusions drawn from the finite test runs. Theorem D is a finite exact, independently replayable certificate argument conditional only on standard Python integer/Fraction semantics and the proven reduction. The full higher-k explicit classification and all-degree formulas remain open.

**Internal antecedent:** the [general orbital duality theorem](../sharp-robust-permanent/paper.md) and its separate exact three-subset \(n\le120\) certificates. That line of work was initially inspired by the OpenAI [four-row permanent and permutation moments](https://github.com/openai/math/tree/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026) manuscript; the fixed-k transfer calculation and rank-five certificates here are separate deductions.


## 6. A universal hierarchy under increasing subset rank

**Theorem E (monotone atom moduli).** For every integer \(n\ge2\) and every \(1\le \ell\le k\le n-\ell\),

\[
\boxed{\mathcal C_{n,k}\le \mathcal C_{n,\ell}.}\tag{9}
\]

Furthermore \(\mathcal C_{n,k}=\mathcal C_{n,n-k}\), so in every fixed degree \(n\), the sequence of sharp moduli is nonincreasing as the subset size approaches \(\lfloor n/2\rfloor\):

\[
\mathcal C_{n,1}\ge\mathcal C_{n,2}\ge\cdots
\ge\mathcal C_{n,\lfloor n/2\rfloor}.
\tag{10}
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
Right-multiply by \(W_{\ell,k}\), use intertwining, and invoke injectivity to get the analogous equality on \(V_\ell\). Hence every law with uniform \(k\)-set marginals also has uniform \(\ell\)-set marginals. The former class of probability laws is contained in the latter, and the definition of the sharp atom/TV coefficient gives (9).

Finally, complementation \(E\mapsto[n]\setminus E\) is an equivariant bijection between \(k\)-subsets and \((n-k)\)-subsets, so the corresponding marginal constraints and sharp constants are identical. This proves (10). QED.

The finite certified tables in the present note and the predecessor's three-subset note furnish strict instances of this inequality. Theorem E does **not** claim strictness for every degree or rank, and (10) is a structural comparison rather than a closed formula for the moduli.


## 7. Complete exact four-subset continuation through degree 50

**Theorem F (25 additional exact sharp coefficients).** The finite classification in Theorem D extends without gaps: for each \(26\le n\le50\), the exact sharp four-subset coefficient \(\mathcal C_{n,4}\) is as follows.

| \(n\) | \(\mathcal C_{n,4}\) | \(n\) | \(\mathcal C_{n,4}\) |
|---:|---:|---:|---:|
|26|31178983/66734529|39|1994479855/3611361227|
|27|26088187/55219671|40|25257571/45082011|
|28|9453205/19608553|41|85610/151749|
|29|322763823/664532107|42|5675965/9942766|
|30|17347/34965|43|206491499/359673689|
|31|1357637/2711805|44|484007989/831880833|
|32|13419459/26302163|45|66083917/112885639|
|33|63151229/122751769|46|35548943/60064597|
|34|103729849/197908557|47|12483647731/20967181867|
|35|322089109/610631637|48|4261003/7081915|
|36|518431/968035|49|2304798951/3811510114|
|37|63992175/118545464|50|297240803/486850773|
|38|12069/22006|||

Combined with Theorem D, this proves the **complete exact classification for \(11\le n\le50\)**, with rational attainment at every degree. The all-degree transfer and hierarchy theorems are independent of this finite cutoff.

*Exact proof and certificate contract.* The immutable support data are published in [certificates/k4_n26_50.json](certificates/k4_n26_50.json). Each degree specifies **exactly five nonidentity cycle-type vectors**: two positive and three negative support classes, encoded by the numbers of 1-, 2-, 3-, and 4-cycles, supplemented by a residual long cycle as in Lemma B. The identity provides the sixth basis column.

The separate [optimizer-free exact checker](check_k4_26_50.py) constructs the six-by-six integer basis matrix from orbital statistics independently computed by [transfer.py](transfer.py), as in equation (8). It solves both the normalized primal and supporting dual systems using rational Gaussian elimination and verifies strict positivity, normalizations, all five matching moment equations, contact equality at all six support classes, and equality of the rational primal identity weight, dual oscillation and printed target value. Crucially, it verifies the dual bound **on every feasible vector in \(A_{n,4}\)**, not only those selected by a solver. Each support vector is realized by an actual conjugacy class; the checker validates the positive rational scale for perturbing the uniform law, establishing sharpness.

The 25 checks collectively cover **129,523 feasible short-cycle vectors** using integer and rational comparisons; in a fresh pinned-source replay, every degree passed. No optimizer or floating-point comparison is involved in this proof. The numerical linear program used to *discover* supports is excluded from the checker and from the logical proof premises. The existing Theorem C then transforms these exact primal-dual equalities into rigorous sharp constants for all laws, not just central laws.

To reproduce from the repository root:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_k4_26_50.py
~~~

The checker rejects Python -O optimized mode, and an independent mutation test confirmed that modifying the n=26 target fraction is detected. The replay hash, logs and trust boundary are in [VERIFICATION.md](VERIFICATION.md). This finite classification does not give an exact closed formula for every \(n>50\). The **sharp k=4 asymptotic constant**, however, is rigorously proved in the separate [rank-five asymptotic note](ASYMPTOTIC_RANK_FIVE.md) and generalized to all fixed ranks in the [all-k supplement](ALL_K_CHEBYSHEV_ASYMPTOTICS.md). No historical priority or external review is claimed.
