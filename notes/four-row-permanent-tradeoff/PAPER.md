# Sharp four-row permanent–determinant tradeoff and parity tensor norms

**Research note, 8 October 2026.** Repository account mxym; prepared with AI assistance. A written proof with exact polynomial certificates, not external peer review or whole-paper Lean formalization.

## 1. Main theorem

For A in C^(4x4), write per A and det A for its permanent and determinant. All row norms are Euclidean.

**Theorem 1.** For every complex 4x4 matrix A and every real c >= 0,
\[
\boxed{
|\operatorname{per}A|+c|\det A|
\le M(c)\prod_{i=1}^4\|A_{i,*}\|_2,\qquad
M(c)=\max\{3/2,\,1+c\}.
}\ \tag{1}
\]
Both branches are sharp. If all rows are nonzero, equality occurs precisely as follows:

- For 0 <= c < 1/2, A is rank one, with a common column vector whose four entries have equal nonzero modulus.
- For c = 1/2, A is either such a rank-one matrix or a complex monomial matrix.
- For c > 1/2, A is monomial.

A zero row produces trivial equality for every c. The all-1/2 matrix has unit row norms, permanent 3/2 and determinant zero. Every permutation matrix has unit row norms, permanent 1 and absolute determinant 1. These prove sharpness.

**Corollary 2 (complete real-coefficient pencil norm).**
For every real t,
\[
\boxed{\sup_{A:\,\prod_i\|A_{i,*}\|_2>0}
\frac{|\operatorname{per}A+t\det A|}
{\prod_i\|A_{i,*}\|_2}
=\max\{3/2,\,1+|t|\}.}\tag{2}
\]
The upper bound comes from (1); an even or odd permutation matrix, chosen according to the sign of t, realizes the second branch. The all-1/2 matrix realizes the first. The analogous exact norm for nonreal t in four rows is **not** claimed.

## 2. An infinite family of exact rectangular two-row inequalities

For n >= 2 and a,b in C^n, define
\[
S_n(a,b)=\sum_{j<k}|a_jb_k+a_kb_j|^2,\qquad
W_n(a,b)=\sum_{j<k}|a_jb_k-a_kb_j|^2.\tag{3}
\]
Put U=||a||², V=||b||², E=|<a,b>|², and T=sum_j |a_j|²|b_j|², with <a,b>=sum_j a_j conjugate(b_j). Expanding the squares yields
\[
\boxed{S_n=UV+E-2T,\qquad W_n=UV-E.}\tag{4}
\]
These are identities over complex numbers, not inequalities.

**Theorem 3 (sharp rectangular symmetric–alternating spectrum).**
For every n >= 2, c >= 0 and a,b in C^n,
\[
\boxed{
S_n(a,b)+cW_n(a,b)
\le\max\{2-2/n,\,1+c\}\|a\|_2^2\|b\|_2^2.
}\tag{5}
\]
Both branches are achieved: normalized identical flat rows give 2-2/n; the disjoint coordinate rows e1,e2 give 1+c.

**Proof.** If a or b vanishes, there is nothing to prove. Otherwise normalize both to norm one. Define
\[
\eta=|\langle a,b\rangle|^2\in[0,1],\quad
\tau=\sum_j|a_j|^2|b_j|^2,\quad
\Delta_n=\tau-\eta/n\ge0,\quad c_n=1-2/n.
\]
The inequality Delta_n >= 0 is ordinary Cauchy–Schwarz on the n complex numbers a_j conjugate(b_j). Combining (4) gives the **exact identity**
\[
\boxed{
S_n+cW_n=1+c+(c_n-c)\eta-2\Delta_n.
}\tag{6}
\]
Because eta is between 0 and 1, the right side is at most max(1+c,2-2/n), proving (5) even for c > 1.

The complete nonzero-row equality criteria are:
\[
\begin{array}{c|l}
c<c_n& a,b \text{ proportional and equimodular on all n coordinates}\\
c=c_n& a_j\overline{b_j}\text{ is independent of }j\\
c>c_n& a,b \text{ have disjoint coordinate supports}.
\end{array}\tag{7}
\]
Indeed, below c_n equality needs eta=1 and Delta_n=0; above it, eta=Delta_n=0; at the transition only Delta_n=0. Equality in the Cauchy inequality defining Delta_n means the products a_j conjugate(b_j) are all the same. This proves every case. QED.

This provides an exact all-n family rather than a finite verification table. The four-column instance is especially effective because the four-row Laplace decomposition splits into equal two-column pieces.

## 3. Two-row Laplace method for the four-row inequality

Normalize A's four nonzero rows and call them a,b,d,e. For each two-column subset J={j,k} with j<k define
\[
p_{ab}(J)=a_jb_k+a_kb_j,\qquad
w_{ab}(J)=a_jb_k-a_kb_j.
\]
Let J^c denote the complementary two columns. The standard permanent and determinant Laplace expansions are, exactly,
\[
\operatorname{per}A=\sum_{|J|=2}p_{ab}(J)p_{de}(J^c),\qquad
\det A=\sum_{|J|=2}\varepsilon_J w_{ab}(J)w_{de}(J^c),
\tag{8}
\]
where epsilon_J is the sign of the column shuffle (J,J^c). The complement map permutes the six two-column subsets. Cauchy–Schwarz gives
\[
|\operatorname{per}A|\le\sqrt{S_4(a,b)S_4(d,e)},\qquad
|\det A|\le\sqrt{W_4(a,b)W_4(d,e)}.\tag{9}
\]
Applying two-dimensional Cauchy–Schwarz to the last two bounds,
\[
\begin{aligned}
|\operatorname{per}A|+c|\det A|
&\le\sqrt{S_4(a,b)S_4(d,e)}
+c\sqrt{W_4(a,b)W_4(d,e)}\\
&\le\sqrt{F_c(a,b)F_c(d,e)},\qquad
F_c(x,y):=S_4(x,y)+cW_4(x,y).
\end{aligned}\tag{10}
\]
Theorem 3 with n=4 bounds each F_c by M(c). Scaling the rows back proves (1). The explicit sharpness matrices in Section 1 prove the constant cannot decrease. QED.

## 4. Quantitative rigidity and all equality matrices

**Theorem 4 (explicit pairwise deficit).**
For a complex 4x4 matrix with four nonzero rows, normalize its rows to unit length. For each row pair i<j set
\[
\eta_{ij}=|\langle a_i,a_j\rangle|^2,\qquad
\Delta_{ij}=\sum_{k=1}^{4}|a_{ik}|^2|a_{jk}|^2-\eta_{ij}/4\ge0.
\]
Define
\[
\delta_{ij}(c)=
\begin{cases}
(1/2-c)(1-\eta_{ij})+2\Delta_{ij},&0\le c\le1/2,\\
(c-1/2)\eta_{ij}+2\Delta_{ij},&c\ge1/2.
\end{cases}\tag{11}
\]
Then
\[
\boxed{
M(c)-\frac{|\operatorname{per}A|+c|\det A|}
{\prod_i\|A_{i,*}\|_2}
\ge\frac16\sum_{1\le i<j\le4}\delta_{ij}(c).
}\tag{12}
\]
For any specific pairing {i,j} disjoint union {k,l} of all four row labels, the right side may be replaced by (delta_ij+delta_kl)/2.

**Proof.** By (6) with n=4, F_c(a_i,a_j)=M(c)-delta_ij(c). Apply (10) after permuting rows into the selected pairing:
\[
\frac{|\operatorname{per}A|+c|\det A|}{\prod_i\|A_{i,*}\|_2}
\le\sqrt{(M-\delta_{ij})(M-\delta_{kl})}
\le M-\frac{\delta_{ij}+\delta_{kl}}2,
\]
where the last step is AM–GM. Average the inequalities for the three perfect matchings of four row labels; each unordered pair occurs once. QED.

**Proof of the equality classification in Theorem 1.**
Equality forces all six nonnegative deltas in (12) to vanish.

When c<1/2, all row-pair inner products have modulus one, so every pair of unit rows is proportional. The vanishing of Delta for any pair then forces all four coordinate moduli equal to 1/2. The matrix is rank one with a common equimodular column vector.

When c>1/2, all eta_ij=Delta_ij=0. Equality in the underlying Cauchy inequality then says each product a_{ik} conjugate(a_{jk}) vanishes. The supports of the four nonzero rows are pairwise disjoint subsets of four columns; hence each is a distinct singleton. This is precisely the monomial class.

When c=1/2, all Delta_ij=0. Therefore for every distinct pair of rows i,j the product
\[
a_{ik}\overline{a_{jk}}=z_{ij}\tag{13}
\]
is independent of column k. If no pair of row supports intersects, the rows are monomial. Otherwise some z_ij is nonzero, forcing both corresponding rows to have full column support. Every other nonzero row intersects one of these full-support rows, hence also has full support. All z_ij are then nonzero. For any three distinct rows i,j,h and any column k,
\[
|a_{ik}|^2=\frac{|z_{ij}|\,|z_{ih}|}{|z_{jh}|},\tag{14}
\]
which is independent of k. Every normalized row is therefore equimodular (modulus 1/2). Equation (13) relative to any fixed reference row now forces every row to be a scalar multiple of that row; the matrix is rank one. The two classes listed in Theorem 1 really attain equality at c=1/2, completing the proof. QED.

Inequality (12) is a quantitative near-extremizer statement without asserting an optimal global distance modulus. Below c=1/2 it forces almost parallel/equimodular row pairs; above c=1/2 it forces nearly disjoint coordinate supports.

**An exact interpolation and quadratic deficit.** Let \(J_4\) be the
all-ones matrix and set \(B_t=(1-t)I_4+tJ_4\) for \(0\le t\le1\).
Every row has squared norm \(1+3t^2\), and direct expansion gives
\[
\operatorname{per}B_t=1+6t^2+8t^3+9t^4,\qquad
\det B_t=(1-t)^3(1+3t)=1-6t^2+8t^3-3t^4.
\]
Both are nonnegative on this interval. At the critical weight \(c=1/2\)
the normalized deficit has the exact form
\[
\boxed{
\frac32-
\frac{|\operatorname{per}B_t|+\frac12|\det B_t|}
{(1+3t^2)^2}
=\frac{6t^2(1-t)^2}{(1+3t^2)^2}.}\tag{14a}
\]
Thus the gap vanishes at the monomial and rank-one endpoints
and is strictly positive in between, quadratically near either
endpoint. The polynomial identity in (14a) is also checked by the
formal exact checker. This example does not by itself prove a
universal optimal distance-to-extremizers modulus.

## 5. Exact parity-biased S4 norm and tensorization

Let u be uniform on the symmetric group S4. For real t with |t| <= 1/24 define
\[
\nu_t(\pi)=1/24+t\,\operatorname{sgn}(\pi).\tag{15}
\]
There are twelve permutations of each parity; for every fixed i,j exactly three even and three odd permutations send i to j. Thus nu_t has **uniform one-point marginals**, and
\[
\|\nu_t-u\|_{\rm TV}=12|t|.\tag{16}
\]
This is a one-parameter parity subfamily, not the space of all uniform-marginal S4 laws.

For complex f on {1,2,3,4}, let
\(\|f\|_{2,u_4}=(\frac14\sum_j|f(j)|^2)^{1/2}\).

**Corollary 5 (sharp parity-law norm).** For every |t| <= 1/24,
\[
\boxed{
\sup_{f_1,\dots,f_4\ne0}
\frac{\left|\mathbb E_{\pi\sim\nu_t}\prod_{i=1}^4 f_i(\pi(i))\right|}
{\prod_i\|f_i\|_{2,u_4}}
=\kappa(t):=\max\{1,\tfrac23(1+24|t|)\}.
}\tag{17}
\]
Consequently the normalized complex L2 inequality with constant one holds throughout this parity family **if and only if**
\[
\boxed{\|\nu_t-u\|_{\rm TV}\le1/4.}\tag{18}
\]
The boundary is included; beyond it the exact optimal amplification factor grows linearly and reaches 4/3 at |t|=1/24.

**Proof.** For A_ij=f_i(j), one has
\(24\mathbb E_{\nu_t}\prod_i f_i(\pi(i))=\operatorname{per}A+24t\det A\).
Each normalized row L2 norm is half its Euclidean norm, so their product is 1/16 of the Euclidean product. Corollary 2 with the **real** coefficient 24t gives the exact norm
\((16/24)M(|24t|)=\kappa(t)\).
Constant rows realize the first branch. For the second branch, take indicator rows selecting a permutation of the more likely parity: its probability is 1/24+|t|, and the normalized product of row norms is 1/16. Equation (16) gives the iff radius (18). QED.

**Corollary 6 (exact nonidentical-column tensor norm).**
For any N>=1 let independent permutations \(\pi_\ell\sim\nu_{t_\ell}\) with arbitrary |t_l|<=1/24. For arbitrary complex functions \(F_i:\{1,2,3,4\}^N\to\mathbb C\) use normalized counting L2 norms. Then
\[
\boxed{
\sup_{F_1,\dots,F_4\ne0}
\frac{\left|\mathbb E\prod_{i=1}^4
F_i(\pi_1(i),\dots,\pi_N(i))\right|}
{\prod_{i=1}^4\|F_i\|_{2,u_4^{\otimes N}}}
=\prod_{\ell=1}^N\kappa(t_\ell).
}\tag{19}
\]
**Proof.** Induct on N. Condition on the first N-1 permutations and apply (17) to the final column, obtaining the product of the nonnegative conditional L2 functions
\(G_i(x)=(\frac14\sum_j|F_i(x,j)|^2)^{1/2}\).
Take the modulus before averaging the outer permutations; apply the induction hypothesis to the nonnegative G_i. Their normalized squared L2 norms telescope to those of F_i.

For sharpness, at each column choose constant row functions or four permutation-indicator row functions, according to the maximizing branch of kappa(t_l). Take products across columns for each row. Independence factors both the expectation and the normalized norms; the resulting ratio is exactly the right side of (19). QED.

## 6. Scope, exact checking, and prior work

The [exact certificate](check.py) verifies (4) for n=4 as a universal integer-polynomial identity treating the formal conjugates as independent variables. It also verifies both Laplace identities (8) as universal polynomial equalities in all sixteen matrix entries. This is coefficient comparison, not evaluating a random finite grid. Rational arithmetic checks the flat/monomial witnesses, parity counts, exact TV formula and seven rational t instances. The all-n rectangular theorem is proved algebraically in Section 2, not inferred from finite cases.

Reproduce with standard-library Python:
~~~sh
python3 -B notes/four-row-permanent-tradeoff/check.py
python3 -B -O notes/four-row-permanent-tradeoff/check.py
~~~
The reports must match each other and [the frozen replay](results/replay.txt). The analytic Cauchy–Schwarz, stability and tensor arguments are contained in this paper; they are not replaced by the finite checker.

The classical sharp permanent-only complex row-norm bound of Carlen, Lieb and Loss, *An inequality of Hadamard type for permanents* (2006), [arXiv:math/0508096](https://arxiv.org/abs/math/0508096), has constant n!/n^(n/2), equal to 3/2 at n=4. The present elementary argument recovers its four-row case while retaining the **sharp determinant term** and complete equality/deficit information. The earlier [three-row complex pencil norm](../complex-permanent-determinant/PAPER.md) treats three rows by a different Hermitian method. The four-row setting is related to [OpenAI/math's strict four-row permanent and permutation moment manuscript](https://github.com/openai/math/blob/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/02-permanent.tex), but no improvement in the full Thorp-shuffle mixing time is claimed.

The exact **nonreal** four-row pencil norm remains unclassified. The tradeoff (1) is not claimed for five or more rows. The radius (18) applies **only** to parity-mixture S4 laws, not arbitrary uniform-one-point-marginal measures on S4. No novelty/priority certification, human referee review or full proof-assistant formalization is asserted.