# A sharp four-projection case of Duchi’s expected-norm inequality

## Statement

Let \(A_1,\dots,A_4\) be operators on a common finite-dimensional real or complex Hilbert space, and put
\[
R=\frac{1}{4^4}\sum_{i,j,k,l=1}^4\|A_iA_jA_kA_l\|_{\mathrm{op}},\qquad
S=\frac{1}{24}\sum_{i,j,k,l\,\mathrm{distinct}}\|A_iA_jA_kA_l\|_{\mathrm{op}},\qquad
D=\frac14\sum_{i=1}^4\|A_i^4\|_{\mathrm{op}}.
\]
Suppose \(A_i=TP_i\), where \(T\) is a *common* positive semidefinite operator, each \(P_i\) is an orthogonal projection, and \(T\) commutes with every \(P_i\). No commutativity among the \(P_i\), no common rank, and no permutation symmetry is assumed. Then
\[
\boxed{\quad R-S\ \ge\ \frac{D-S}{64}\ \ge\ 0.\quad}
\tag{1}
\]
The coefficient \(1/64\) is optimal. The case \(T=I\) gives all quadruples of orthogonal projections. Equivalently, the class in (1) consists of direct sums of projection quadruples with a possibly different **common scalar within each block**. It includes block diagonal constructions whether or not their blocks are permutation-related. It does not include arbitrary label-dependent weights in a block, nor arbitrary PSD matrices.

Equality \(R=S\) holds precisely when all the matrices are zero, or when the four matrices have the same positive operator norm \(M\) and a common unit eigenvector of eigenvalue \(M\).

## The repeated-word categories

Write \(\mathbb E\) for uniform ordered distinct indices of the indicated tuple length. On each eigenspace \(h\) of \(T\), write \(\lambda_h\ge0\) for its eigenvalue and \(P_i^{(h)}\) for the restricted projection. For two indices define
\[
U_j(i,k)=\max_h\lambda_h^4\,\|P_i^{(h)}P_k^{(h)}\|_{\mathrm{op}}^j,\qquad
Q_j=\mathbb E_{i,k} U_j(i,k)\quad (j=1,2,3).
\]
Define \(L,H,J\) to be the average four-factor norms of words of patterns \(0012,0102,0120\), respectively, with uniformly distinct labels assigned in order of first occurrence. Products of pattern \(0112\) or \(0122\) have the same norm as pattern \(0012\) on the same ordered triple: blockwise a repeated projection collapses, leaving \(\lambda_h^4\) times a three-projection product in each case. The other backtracking pattern \(0121\) has average \(H\) by reversal and relabeling. The complete word identity is
\[
256R=4D+36Q_1+36Q_2+12Q_3+72L+48H+24J+24S.
\tag{2}
\]
Indeed, in two-label words the seven patterns have one transition (\(0001,0011,0111\)), two (\(0010,0100,0110\)), or three (\(0101\)). If \(q=\|PQ\|_{\mathrm{op}}\), the corresponding projection norms are \(q,q^2,q^3\): \(PQP=(PQ)(PQ)^*\), while \(PQPQ=(PQ)((PQ)^*(PQ))\) has cubed singular values. Each pattern with two labels has 12 assignments, each with three labels has 24, and the one- and four-label counts are 4 and 24.

## Three contractions along an optimizing direction

Fix an ordered distinct quadruple and denote its four projections on a block attaining the product norm by \(A,B,C,E\), to distinguish them from the full matrices \(A_i\). In the following unscaled formulas the chosen block has scalar \(\lambda\). When the full distinct product norm is zero, use \(\lambda=0\) and \(a=b=c=0\) for just the estimates below; all its contributions to their right sides are then zero. Otherwise choose a unit right singular vector \(x\) of \(ABCE\) with \(x\in\operatorname{Ran}E\). Set
\[
c=\|Cx\|,\quad v=Cx/c,\qquad b=\|Bv\|,\quad w=Bv/b,\qquad a=\|Aw\|.
\]
Then \(0<a,b,c\le1\), and the full distinct norm is \(\lambda^4abc\). The two pairs at the edges of the word have projection norms at least \(a\) and \(c\). The right triple \(BCE\) has projection norm at least \(bc\). The backtrack \(BABC\) has projection norm at least \(a^2b\), because it maps \(v\in\operatorname{Ran}C\) to \(bBAw\), and \(\|BAw\|\ge|\langle w,BAw\rangle|=\|Aw\|^2=a^2\).

We also need the triangle bound, for any three orthogonal projections \(P,Q,V\):
\[
\|PQVP\|_{\mathrm{op}}\ \ge\ h(\|PQV\|_{\mathrm{op}}),\qquad h(t)=t(2t-1)_+.
\tag{3}
\]
Set \(t=\|PQV\|\); if \(t=0\) there is nothing to prove. Let \(v_0\in\operatorname{Ran}V\) be a unit right singular vector, \(u_0=PQVv_0/t\in\operatorname{Ran}P\) the corresponding unit left vector, and \(w_0=Qv_0/\|Qv_0\|\). The overlaps of \(w_0\) with \(v_0,u_0\) are nonnegative real numbers \(y=\|Qv_0\|\) and \(z=t/y\). Decomposing both vectors along \(w_0\) and its orthogonal complement gives
\[
|\langle u_0,v_0\rangle|\ge yz-\sqrt{(1-y^2)(1-z^2)}\ge 2t-1.
\]
The second inequality follows from \((1-y^2)(1-z^2)\le(1-yz)^2\). Finally \(\|PQVP\|=\|P(PQV)^*\|\ge t\|Pv_0\|\ge t|\langle u_0,v_0\rangle|\). This argument works over both fields. The function \(h\) is nondecreasing and \(h(t)\ge2t^2-t\) on \([0,1]\). The triangle on the right triple \(BCEB\) thus has projection norm at least \(2b^2c^2-bc\).

Now average over the 24 ordered distinct quadruples, choosing and using a maximizing block separately for each. Both edge pairs marginalize to uniform ordered distinct pairs, and all the selected ordered triples marginalize to uniform ordered distinct triples. Every full repeated-word norm is at least its value on the corresponding chosen block, even if some *other* block maximizes that repeated word. Therefore
\[
Q_j\ge \mathbb E\,\lambda^4(a^j+c^j)/2,\qquad
L\ge \mathbb E\,\lambda^4bc,\qquad
H\ge \mathbb E\,\lambda^4 a^2b,\qquad
J\ge \mathbb E\,\lambda^4(2b^2c^2-bc),\qquad
S=\mathbb E\,\lambda^4abc.
\tag{4}
\]
For the first inequality it is enough that the two edge products each have the correct norm lower bound; they need not be equal as random variables. In the second and fourth inequalities the embedded triple is the right triple. In the third it is the left triple with the middle label repeated. Uniformity of the marginals is what permits different triples to be used.

## Exact polynomial certificate

Combining (2)–(4), it suffices to prove the following inequality for three independent numbers in \([0,1]\):
\[
\mathcal B(a,b,c)=F(a)+F(c)+48bc+48a^2b+48b^2c^2-228abc\ge0,\qquad
F(t)=18t+18t^2+6t^3.
\tag{5}
\]
Use the tensor Bernstein basis of degrees \((4,2,3)\). The coefficient of \(t^r\) at index \(i\) in degree \(d\) is \(\binom ir/\binom dr\) (zero if \(i<r\)). Consequently the coefficients of \(2\mathcal B\) are the integers
\[
u_i+v_k+16jk+8j\binom i2
   +32\mathbf1_{\{j=2\}}\binom k2-19ijk,\qquad
u=(0,9,24,48,84),\quad v=(0,12,36,84).
\]
These are the full tables (rows \(i=0,\ldots,4\), columns \(k=0,\ldots,3\)):
~~~
j=0                 j=1                 j=2
 0  12  36  84       0  28  68 132       0  44 132 276
 9  21  45  93       9  18  39  84       9  15  65 171
24  36  60 108      32  22  24  50      40   8  20  88
48  60  84 132      72  43  26  33      96  26   0  30
84  96 120 168     132  84  48  36     180  72   8   0
~~~
All basis functions are nonnegative on the whole closed cube. This certifies (5), including boundaries, without any sampling or floating-point optimization. In particular the repeated terms other than \(4D\) in (2) sum to at least \(228S\). Thus \(256R\ge4D+252S\), which is (1).

By submultiplicativity and scalar AM–GM, \(S\le\prod_i\|A_i\|\le D\). If \(R=S\), (1) forces equality in both. Unless all matrices vanish, scalar equality forces their four operator norms to be the same \(M>0\), and a maximizing distinct word has norm \(M^4\). Equality at each multiplication step along a unit maximizing vector then forces each step’s input into the top eigenspace of its PSD factor. Such a factor acts by \(M\) on that input, so the direction never changes: the vector belongs to all four top eigenspaces. Conversely a common such vector gives norm \(M^4\) for every word. Finally take four nonzero pairwise orthogonal projections (four coordinate lines suffice). Here \(D=1\), \(S=0\), and only the four all-identical words have positive norm; \(R=1/64\). This proves sharpness.

## Scope and prior work

This is the norm **inside** the expectation, as in [Duchi, COLT 2012, equations (2)–(3)](https://proceedings.mlr.press/v23/duchi12/duchi12.pdf), not the different norm-of-average inequality. [Israel–Krahmer–Ward](https://arxiv.org/abs/1411.0333) prove the former through product length three for arbitrary PSD matrices. [De Sa, supplemental §2.3](https://proceedings.neurips.cc/paper_files/paper/2020/file/42299f06ee419aa5d9d07798b56779e2-Supplemental.pdf) gives a length-six counterexample built from direct sums of rank-one projections. [Liu, §§4–6](https://arxiv.org/html/2611.07649v1) uses a path-supported Gram matrix and related projection direct sums. The earlier [four-factor construction in this repository](https://github.com/mxym/math/tree/research/duchi-four-factor-sampling) gives strict failures for every population \(n\ge5\) using different **label-dependent** weights in its local blocks. Its \(n=4\) case is expressly not settled; neither is the general \(n=4\) PSD case in the present note. A targeted search through the cited primary works and subsequent expected-norm literature did not locate (1); that search does not establish priority. This is an AI-assisted research note, not peer reviewed or Lean-verified. The accompanying verifier independently expands the Bernstein certificate and checks the full word averages in exact rational examples.
