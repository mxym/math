# Exact sharp five-subset (rank-six Johnson) atom moduli through degree 40

**Certified finite classification — 8 October 2026.** This note computes and proves the sharp atom-to-total-variation coefficient for the action of \(S_n\) on its **five-element subsets** for **every \(11\le n\le40\)**. It continues the proven all-fixed-rank asymptotic law in the [all-k manuscript](ALL_K_CHEBYSHEV_ASYMPTOTICS.md), but is an **exact rational finite-degree classification**, not an asymptotic estimate. The separate [four-subset classification](README.md) covers \(11\le n\le50\). All the present finite certificates were freshly replayed from public fixed-commit files with integer and rational arithmetic and no optimizer. No priority or independent human peer review is asserted.

## 1. The sharp finite result

Let \(\Omega_n=\binom{[n]}5\). For every probability law \(\nu\) on \(S_n\) with uniform image marginals

\[
\nu\{g:gE=H\}=\binom n5^{-1}
\quad(E,H\in\Omega_n),
\]

define \(C_{n,5}\) to be the optimal constant in

\[
|\nu(\sigma)-1/n!|\le C_{n,5}\|\nu-u_n\|_{\rm TV}
\quad(\sigma\in S_n),
\]

where \(u_n\) denotes uniform measure on \(S_n\).

**Theorem 1 (sharp exact rank-six classification through degree 40).** For every integer \(n\) with \(11\le n\le40\), the sharp constant is the following **exact rational number**:

| \(n\) | \(C_{n,5}\) | \(n\) | \(C_{n,5}\) |
|---:|---:|---:|---:|
| 11 | 5/14 | 26 | 23437756/59239479 |
| 12 | 5/14 | 27 | 5448913/13684587 |
| 13 | 5/14 | 28 | 142207/352870 |
| 14 | 5/14 | 29 | 14274943/35026441 |
| 15 | 29275/81761 | 30 | 1977286/4761523 |
| 16 | 472381/1306248 | 31 | 10984565/26210343 |
| 17 | 780403/2146875 | 32 | 193666153/454927556 |
| 18 | 1145017/3113241 | 33 | 303836297/707034407 |
| 19 | 1281055/3453933 | 34 | 2463156/5660405 |
| 20 | 606991/1613686 | 35 | 527535651419/1202219764785 |
| 21 | 397109/1048673 | 36 | 1905547/4288180 |
| 22 | 1653601/4318479 | 37 | 86902824303/194221444604 |
| 23 | 1050248/2723139 | 38 | 55173574363/121333163791 |
| 24 | 16136219/41432528 | 39 | 32986802215/71792986437 |
| 25 | 906216277/2314325373 | 40 | 6198650425199/13306819837380 |

For every entry, there exist two central probability laws, supported on at most seven disjoint genuine conjugacy classes, with **exactly equal full five-set image marginal matrices** and identity-atom gap equal to the tabulated value. A rational orbital dual on *every* conjugacy class proves that no larger gap is possible.

## 2. Reduction from all conjugacy classes to exact finite rational data

For each permutation \(g\in S_n\), define its intersection counts

\[
F_j(g)=\#\{E\subseteq[n]:|E|=5,\ |E\cap gE|=j\},
\quad j=0,\ldots,5.
\]

The [transfer-matrix theorem](README.md) proves that the tuple \(F_0(g),\ldots,F_5(g)\) depends **only** on the integer counts

\[
a=(m_1(g),m_2(g),m_3(g),m_4(g),m_5(g)).
\]

Such a vector is realizable exactly when the remainder \(r=n-\sum_{\ell=1}^5\ell a_\ell\) is either zero or at least six. If \(r>0\), take a single \(r\)-cycle besides the specified short cycles. Therefore testing one representative of **every** feasible \(a\) exactly tests the dual bound against **all** conjugacy classes, with no approximate comparison or neglected large-cycle type.

For central probabilities \(P,Q\), equal \(F_j\)-expectations for \(j=0,\ldots,5\) are equivalent to equal five-set image marginal matrices (each orbital consists of pairs with fixed \(|E\cap H|=j\)). Their identity atom gap is a lower bound for \(C_{n,5}\) after an arbitrarily small positive rational perturbation of uniform measure. A dual function of the form

\[
h(g)=\mathbf1_{\{g=e\}}-\sum_{j=0}^{4}y_{j+2}F_j(g)
\tag{1}
\]

with oscillation \(U-L\) bounds *every* marginal-preserving atom-to-TV ratio from above by \(U-L\). The moment \(F_5\) is redundant because \(\sum_jF_j=\binom n5\).

## 3. Four degenerate degrees: an especially short exact proof

**Lemma 2 (universal positive orbital relation).** For every integer \(n\ge6\) and every subset rank \(k\), the four conjugacy classes \(I=1^n\), \(K=4\,1^{n-4}\), \(T=2\,1^{n-2}\), \(E=3^2\,1^{n-6}\) obey

\[
5F_{k,j}(I)+9F_{k,j}(K)
=12F_{k,j}(T)+2F_{k,j}(E)
\quad(0\le j\le k\le n).
\tag{2}
\]

*Proof.* The class cycle polynomials satisfy the elementary identity

\[
5(1+z)^6+9(1+z)^2(1+z^4)
=12(1+z)^4(1+z^2)+2(1+z^3)^2.
\]

Both sides have coefficient vector \((14,48,84,100,84,48,14)\). Multiply by \((1+z)^{n-6}\) and apply the exact transfer identity for every subset rank to obtain (2). Full details are in the independent [all-rank kernel note](ALL_RANK_TRACE_KERNEL.md). QED.

Thus, for **every \(n\ge6\)**, the positive class measures

\[
P=\frac5{14}U_I+\frac9{14}U_K,\qquad
Q=\frac67U_T+\frac17U_E
\tag{3}
\]

have exactly equal full marginal matrices **simultaneously for every subset rank**, and their identity-atom gap is \(5/14\). Therefore \(C_{n,5}\ge5/14\) whenever defined.

For each of the **four degrees \(11,12,13,14\)**, the [pure-rational checker](check_k5_11_14.py) supplies a seven-entry dual vector \(\eta=(\eta_0,\ldots,\eta_6)\) with

\[
\eta_0=-1,\quad\eta_1=9/14,\qquad
h_n(g)=\mathbf1_{\{g=e\}}+
\sum_{j=0}^4\eta_{j+2}\frac{F_j(g)}{\binom n5}.
\tag{4}
\]

For self-contained reconstruction, the five remaining coefficients are:

| \(n\) | \(\eta_2,\eta_3,\eta_4,\eta_5,\eta_6\) |
|---:|---|
| 11 | \(0,\ 121/300,\ 671/700,\ 33/70,\ 33/28\) |
| 12 | \(957/1330,\ 34551/93100,\ 24651/23275,\ 99/245,\ 297/245\) |
| 13 | \(-2587/6272,\ 11609/18816,\ 169/140,\ 78/245,\ 351/280\) |
| 14 | \(13/1080,\ 3133/7560,\ 481/336,\ 13/60,\ 13/10\) |

The checker verifies, by exact rational arithmetic on **every feasible short-cycle vector** in each degree, that \(9/14\le h_n(g)\le1\), with upper contacts at \(I,K\) and lower contacts at \(T,E\). Equation (3) gives the matching primal atom gap. Hence \(C_{n,5}=5/14\) **exactly for every \(11\le n\le14\)**. No numerical LP output is used as a proof premise.

## 4. The remaining 26 degrees: optimizer-independent primal–dual certificates

For each \(15\le n\le40\), [certificates/k5_n15_40.json](certificates/k5_n15_40.json) gives a literal finite list of **six nonidentity support cycle-count vectors**: three positive and three negative supports. The identity is an additional fourth positive support. Thus there are precisely seven candidate conjugacy classes for each degree, and the entire certificate is reconstructible from only these integer support vectors and the displayed target fraction.

The separate [exact verifier](check_k5_15_40.py) builds the following \(7\times7\) integer matrix \(B\), one row per support class:

\[
B_i=
\begin{cases}
(1,0,F_0,\ldots,F_4),&i\ \text{on the positive side},\\
(0,1,-F_0,\ldots,-F_4),&i\ \text{on the negative side}.
\end{cases}
\tag{5}
\]

With the identity placed first, it independently solves **both**

\[
B^\mathsf T w=(1,1,0,0,0,0,0)^\mathsf T,
\qquad
By=(1,0,0,0,0,0,0)^\mathsf T
\tag{6}
\]

using exact rational Gaussian elimination. It verifies all 7 primal weights are **strictly positive**, each probability law has total mass 1, all six orbital expectations coincide exactly, the dual range

\[
-y_1\le
\mathbf1_{\{g=e\}}-\sum_{j=0}^4y_{j+2}F_j(g)
\le y_0
\tag{7}
\]

holds for **every** reduced feasible cycle-count vector, and contacts hold at each prescribed support class. Finally it checks

\[
w_{\rm identity}=y_0+y_1=C_{n,5}
\]

exactly as a rational fraction, and constructs a strictly positive rational perturbation scale making \(u_n+\delta(P-Q)\) a genuine nonnegative probability distribution. The two bounds coincide, establishing Theorem 1 in every one of these 26 degrees.

The clean VPS replay from fixed public-source commits independently reproduced all 26 results and checked **82,377 distinct reduced dual types** for \(15\le n\le40\). Combined with the 361 types in the four exceptional degrees, the classification covers **82,738 exact reduced dual constraints** across 30 degrees. Neither verifier imports a numerical solver or performs any floating-point inequality comparison; heuristic LP was used only to *discover* compact candidate supports.

## 5. Reproduction and proof boundary

From the repository root, run these three commands in ordinary (nonoptimized) Python:

~~~sh
python3 notes/johnson-short-cycle-spectrum/transfer.py
python3 notes/johnson-short-cycle-spectrum/check_k5_11_14.py
python3 notes/johnson-short-cycle-spectrum/check_k5_15_40.py
~~~

All the finite proof scripts require **only Python standard-library integers and Fraction arithmetic**. They explicitly reject Python's optimized mode (-O), in which assertions otherwise would be skipped. The exact oracle-free source hashes, success logs and negative controls are documented in [VERIFICATION.md](VERIFICATION.md). Mutation tests that modify a stated exact target or a boundary dual coefficient are rejected; they cannot silently pass.

The exact transfer/compression theorem has a complete general mathematical proof, not merely the finite 1,329 small-rank regression checks. The finite tables here rely on reproducible exhaustive reduced dual inequalities, rational primal and dual systems and explicit conjugacy-class realizability. No classification for \(n>40\), no exact formula valid for all finite \(n\), no novel-priority claim and no external human peer review are asserted. The independent [all-fixed-rank asymptotic law](ALL_K_CHEBYSHEV_ASYMPTOTICS.md) remains valid at rank \(k=5\) as \(n\to\infty\), but it is not used to infer any finite table entry.
