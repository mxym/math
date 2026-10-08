# Fixed-k Johnson orbital compression and exact four-subset moduli

Research note, 8 October 2026. This note extends the [orbital primal-dual method](../sharp-robust-permanent/paper.md) from particular permutation actions to all symmetric-group actions on fixed-size subsets, and certifies 15 exact sharp constants for the four-subset action. The parent work already contains the independent three-subset classification through degree 120; the present four-subset computation is distinct. No novelty priority, outside peer review, or Lean formalization is asserted.

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
