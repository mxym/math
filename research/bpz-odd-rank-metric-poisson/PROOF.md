# A critical-window Poisson limit and large odd-degree intersecting codes

Let \(q\) be fixed. For \(K=\mathbb F_{q^m}\), the rank weight \(w(v)\) of \(v\in K^D\) is the dimension over \(\mathbb F_q\) of the span of its coordinate values. It is unchanged when \(v\) is multiplied by an element of \(K^*\); it therefore defines the rank weight of a one-dimensional \(K\)-subspace. Such subspaces are called projective lines in the vector space below (i.e. projective *points* in \(\mathrm{PG}(D-1,K)\), not two-dimensional \(K\)-subspaces).

**Theorem 1 (critical-window law).** Fix integers \(k\geq t\geq 2\) and \(c\). Let \(m\to\infty\) through any sequence for which
\[
tD-(k+1-t)m=c \tag{1}
\]
has a positive integer solution \(D\). Let \(H\) be uniform in \(K^{k\times D}\). Let \(X_m\) be the number of one-dimensional \(K\)-subspaces of \(\ker H\) with rank weight at most \(t\). Then
\[
X_m\ \xrightarrow{\ d\ }\ \operatorname{Poisson}(\mu),
\qquad \mu=\frac{q^c}{\prod_{i=0}^{t-1}(q^t-q^i)}.
\]

**Theorem 2 (Borello–Polverino–Zullo large-degree range).** For every fixed \(q\), there is a scattered \(\mathbb F_q\)-subspace of \(\mathbb F_{q^m}^3\) of dimension \(m+3\), and hence a nondegenerate \([2m-3,3,m-1]_{q^m/q}\) rank-metric intersecting code, for every
\[
m\geq 100(24q^2+2)^2.
\]
In particular this includes all sufficiently large odd \(m\). The probability that the image of a uniform \(3\)-by-\((m+3)\) matrix on \(\mathbb F_q^{m+3}\) has dimension \(m+3\) and is scattered tends to \(\exp(-\mu_q)\), for \(\mu_q=q^6/((q^2-1)(q^2-q))\). The bound is not asserted sharp. Exact binary examples exist in the smaller odd degrees \(7,9,11\).

## 1. Support, value space, and regular families

Write \(Q=q^m\) and \(a=(k+1-t)/t>0\), so \(D=am+c/t\). For \(v\in K^D\), expand its coordinates in any fixed \(\mathbb F_q\)-basis of \(K\). Define its **support** \(S(v)\subseteq\mathbb F_q^D\) to be the \(\mathbb F_q\)-row space of the resulting \(m\)-by-\(D\) matrix. It has dimension \(w(v)\). It is invariant under multiplying by a nonzero scalar in \(K\), and is the unique smallest \(\mathbb F_q\)-subspace \(S\) such that \(v\in KS\), where \(KS\) denotes the \(K\)-linear span in \(K^D\). These assertions follow by expanding the coefficients in the chosen basis. They are independent of the basis because any change of basis, and multiplication by a nonzero scalar, induces an invertible row operation over \(\mathbb F_q\).

Write \(E(v)\subseteq K\) for the \(\mathbb F_q\)-span of the coordinate values of \(v\). Two such value spaces are *scalar equivalent* if one is a \(K^*\)-multiple of the other. Its equivalence class depends only on the projective line \(Kv\). An invertible change of the \(D\) coordinate positions over \(\mathbb F_q\) also preserves \(E(v)\).

Fix a support \(S\) of dimension \(i\) and an ordered \(\mathbb F_q\)-basis of it. A representative with support exactly \(S\) has \(i\) coefficients linearly independent over \(\mathbb F_q\). Its first coefficient is nonzero and may be normalized to 1. There are therefore
\[
P_i(Q)=\prod_{j=1}^{i-1}(Q-q^j)
\tag{2}
\]
projective lines of rank weight \(i\) on this support, for \(m\geq i\). Its value space is exactly the span of those \(i\) coefficients: it is contained in that span, and both have dimension \(i\). For a fixed scalar-equivalence class of \(t\)-dimensional value spaces, the number of normalized coefficient vectors of rank \(t\) on any one support is bounded in terms of \(q,t\) only. Indeed if \(E_0\) represents the class, \(uE_0\) contains 1 only if \(u^{-1}\in E_0\setminus\{0\}\), at most \(q^t-1\) choices. The other \(t-1\) normalized coefficients have at most \(q^{t(t-1)}\) ordered choices per space.

A family of distinct projective lines of rank weight at most \(t\) is **regular** if all supports have dimension \(t\), their sum is direct over \(\mathbb F_q\), and their value spaces are pairwise inequivalent under scalar multiplication. The lines are then \(K\)-independent: extend the union of support bases to an \(\mathbb F_q\)-basis of \(\mathbb F_q^D\), which also gives a \(K\)-basis of \(K^D\). In these coordinate blocks, each basis vector of a projective line is nonzero on its own block only, where its values span a space of dimension \(t\). In a linear combination with two or more nonzero \(K\)-coefficients, the coordinate span contains the two corresponding scaled value spaces. For the resulting rank weight to be at most \(t\), these \(t\)-dimensional spaces would have to equal one another. That contradicts scalar inequivalence. Consequently

> In the \(K\)-span of a regular family the only projective lines of rank weight at most \(t\) are precisely the members of that family.

## 2. Rare irregular independent families

For any \(d\) fixed \(K\)-independent projective lines, the probability that they all lie in \(\ker H\) is \(Q^{-kd}\). Indeed the \(d\) corresponding linear constraints on one uniform row of \(H\) are independent, and the \(k\) rows are independent.

For fixed \(d\), we show that the expected number of **irregular but \(K\)-independent** \(d\)-element families of rank weight at most \(t\) in \(\ker H\) tends to zero. Let \(s\leq td\) be the dimension of their total support. The Gaussian binomial count \({D\brack s}_q\) is \(O(q^{sD})\) for fixed \(q,s\), and within a fixed total support there are \(O(Q^{t-1})\) possible low-rank projective lines by (2) and a bounded number of smaller support choices. For \(s<td\), even counting ordered families gives expectation bounded by
\[
O\big(q^{sD}Q^{(t-1)d}Q^{-kd}\big)
 =O\big(q^{a(s-td)m}\big)=o(1).
\]
When \(s=td\), all supports must be of dimension \(t\) and direct, so irregularity means two equivalent value spaces. After choosing the total support and the individual supports inside it (a bounded number of choices for the latter), selecting the lines then costs only \(O(Q^{(t-1)(d-1)})\): pick the repeated-class pair, choose all but one line freely, and use the bounded number of normalized choices in its prescribed class for that line. The expectation is \(O(Q^{-(t-1)})=o(1)\). The second case is empty for \(d=1\). This proves the claimed rarity.

## 3. Main counts and truncated inclusion-exclusion

The number of rank-\(t\) projective lines in \(K^D\) is
\[
M_m={D\brack t}_q P_t(Q),\qquad
M_mQ^{-k}\longrightarrow \mu
\tag{3}
\]
by (1)–(2). The proportion of ordered \(r\)-tuples of rank-\(t\) lines that are regular tends to 1 for each fixed \(r\). To see this, sample with replacement. The supports are independent uniform \(t\)-spaces. For the next support to meet the span of the earlier ones nontrivially, it must contain one of the bounded number of one-dimensional \(\mathbb F_q\)-subspaces in that span. The inclusion probability of any fixed such line in a uniform \(t\)-space is \((q^t-1)/(q^D-1)\), by double counting. Thus directness fails with probability tending to zero. Independently of any support configuration, pairwise scalar-equivalence of value spaces has probability \(O(P_t(Q)^{-1})\) for any fixed pair, by the bound following (2). A union bound over pairs completes the claim. Regularity implies distinctness. If \(A_{r,m}\) counts regular \(r\)-element subsets of low-rank projective lines in the kernel, using their \(K\)-independence and (3) now gives
\[
\mathbb E A_{r,m}=\frac{M_m^rQ^{-kr}}{r!}(1-o(1))\longrightarrow \frac{\mu^r}{r!}.
\tag{4}
\]

Here irregular families cannot simply be omitted from untruncated factorial moments: a rare kernel may contain many dependent low-rank lines. Fix \(L\), let \(B_L\) be the event that the kernel contains some irregular \(K\)-independent family of size at most \(L\), and let \(Y_m=X_m\) on its complement and \(Y_m=0\) on \(B_L\). The probability of \(B_L\) tends to zero by §2. For \(1\leq r\leq L\), on the complement of \(B_L\) every \(r\)-element family of low-rank lines in the kernel is regular. In fact, extract a \(K\)-basis from that family. The extracted subfamily has size at most \(L\), so is regular; the rigidity assertion in §1 then forces the original family to consist of the basis lines alone.

We also control the contribution of regular sets on \(B_L\). Fix a regular \(r\)-element subset \(R\) in such a kernel, and an irregular independent family \(T\) of size at most \(L\) in that kernel. Extend \(R\) to a \(K\)-basis \(F\) of \(\langle R\cup T\rangle_K\) by taking further lines from \(T\). This is possible since \(R\) is independent. Then \(F\) is irregular; otherwise the rigidity assertion would give \(T\subseteq F\), and every subfamily of a regular family is regular. Moreover \(|F|\leq r+L\). Thus the number of possible \(R\)'s counted by \(A_{r,m}\mathbf 1_{B_L}\) is at most the number of pairs consisting of such an irregular independent \(F\) and an \(r\)-element subset of \(F\). Each \(F\) permits at most \({|F|\choose r}\) choices and §2 bounds the expectation of the number of these \(F\)'s for each size. Hence \(\mathbb E[A_{r,m}\mathbf 1_{B_L}]=o(1)\). This gives
\[
\mathbb E{Y_m\choose r}\longrightarrow\mu^r/r!,\qquad 0\leq r\leq L.
\tag{5}
\]

For completeness, fix a nonnegative integer \(j\). For any integer \(y\geq j\),
\[
\sum_{i=0}^s(-1)^i{j+i\choose j}{y\choose j+i}
={y\choose j}\sum_{i=0}^s(-1)^i {y-j\choose i}.
\]
If \(y=j\) this is 1, and if \(y>j\) the rightmost sum is \((-1)^s{y-j-1\choose s}\), with out-of-range binomials zero. The left hand side is zero when \(y<j\). Odd partial sums thus bound \(\mathbf 1_{y=j}\) below and even partial sums bound it above. Apply this to \(Y_m\) with \(L\ge j+s\), take the expectation and use (5). The probabilities \(\Pr(Y_m=j)\) and \(\Pr(X_m=j)\) differ by at most \(\Pr(B_L)=o(1)\) for this fixed \(L\). As odd and even \(s\) grow, their limiting bounds both tend to \(e^{-\mu}\mu^j/j!\), by the exponential series. This proves Theorem 1.

## 4. The scattered subspace and its trace-dual code

Set \(k=3,t=2,D=m+3\); then \(c=6\) in (1). Put \(U=H(\mathbb F_q^D)\subseteq K^3\). If \(\ker H\) contains a nonzero rank-one vector, \(H\) is not injective on \(\mathbb F_q^D\). Conversely a rank-one vector is a scalar multiple of a vector over \(\mathbb F_q\), so these conditions are equivalent. If \(H\) is injective on \(\mathbb F_q^D\), a rank-two kernel vector can be expressed as \(a u+b v\) with \(u,v\) independent over \(\mathbb F_q\) in \(\mathbb F_q^D\) and \(a,b\) independent over \(\mathbb F_q\) in \(K\). Thus \(H(u)\) and \(H(v)\) are proportional over \(K\), while remaining independent over \(\mathbb F_q\). Conversely a pair of distinct \(\mathbb F_q\)-directions in \(U\) on a single \(K\)-line gives such a rank-two kernel vector. Therefore \(X_m=0\) holds exactly when \(U\) is scattered and has dimension \(D\); here “scattered” means each \(K\)-line has intersection of \(\mathbb F_q\)-dimension at most one. Theorem 1 gives the stated probability.

We give the coding consequence directly. Define
\[
V=U^{\perp'}=\{v\in K^3:\operatorname{Tr}_{K/\mathbb F_q}(v\cdot u)=0\ \forall u\in U\}.
\]
The trace pairing is nondegenerate, so \(n=\dim_{\mathbb F_q}V=3m-(m+3)=2m-3\). Let \(G\) be the \(3\)-by-\(n\) matrix whose columns are an \(\mathbb F_q\)-basis of \(V\). For any \(a\in K^3\setminus\{0\}\), set \(I=\{a\cdot v:v\in V\}\subseteq K\). The weight of \(aG\) is \(\dim_{\mathbb F_q}I\). The trace annihilator of \(I\) is \(\{\lambda\in K:\lambda a\in U\}\), of dimension at most 1 by scatteredness. The rank weight is therefore at least \(m-1\), with equality when \(a\in U\setminus\{0\}\). In particular \(G\) has full row rank and nondegenerate columns. The rank support of a codeword is the row space over \(\mathbb F_q\) of its expanded \(m\)-by-\(n\) coordinate matrix. Its dimension equals the rank weight. Since \(2(m-1)>2m-3=n\), any two nonzero codeword supports intersect nontrivially. This proves the coding assertion and agrees with Borello–Polverino–Zullo, Corollary 3.5.

## 5. An effective (coarse) bound

For this section use \(t=2,k=3,D=m+3\) and \(m\geq2\). The Gaussian binomial estimate
\[
{D\brack s}_q\leq4q^{s(D-s)}
\tag{6}
\]
holds uniformly: the denominator product \(\prod_{i\geq1}(1-q^{-i})\) is at least \((1-1/2)(1-1/4)(1-\sum_{i\geq3}2^{-i})=9/32>1/4\). When \(s>D\) the left side is zero. The number of low-rank lines in a fixed total support of dimension \(s\) is \({s\brack1}_q +(Q-q){s\brack2}_q\leq q^{2s+3}Q\). With (6), the expected number of independent irregular families of size \(d\) having total support \(s<2d\), summed over \(s\), is at most
\[
\sum_{s=1}^{2d-1}4q^{(s-2d)m+3s+(2s+3)d}
\leq 8d\,q^{4d^2+9d-m}.
\]
We counted ordered lines for an upper bound. For \(s=2d\), choose the total support in at most \(4q^{2dm+6d}\) ways and its ordered two-dimensional supports in at most \({2d\brack2}_q^d\leq q^{4d^2}\) ways. Once one rank-two value space is fixed, scalar equivalence for a space normalized as \(\langle1,\alpha\rangle_{\mathbb F_q}\) allows at most \(q^3\) choices of \(\alpha\): a basis change in \(\operatorname{GL}_2(q)\) shows that the allowed values lie in the fractional-linear orbit, of size at most \(|\operatorname{PGL}_2(q)|=q(q^2-1)\). There are at most \(d^2\) choices of the marked equivalent pair. Thus this part of the expectation is at most \(4d^2q^{4d^2+6d+3-m}\). Summing both bounds, the expected number \(I_d\) of irregular independent \(d\)-element sets has
\[
I_d\leq q^{4d^2+15d+10-m}.
\tag{7}
\]
For example, \(8d+4d^2\leq 12d^2\leq q^{6d+10}\), and \(6d+3\leq 9d\), so (7) follows.

For any \(1\leq r\leq L\), the upper bound for the cutoff moment loss in §3 is \(\sum_{d\leq2L}{d\choose r}I_d\), at most
\[
q^{16L^2+36L+12-m}.
\tag{8}
\]
The same bound applies to \(\Pr(B_L)\) by (7). To quantify (4), the proportion of nonregular ordered rank-two \(r\)-tuples is at most
\[
\frac{2r q^{2r+2}}{Q}+\frac{r^2q^3}{Q}.
\]
The first term counts failures of directness by testing each line in the previous span; the second uses the orbit bound and \(Q-q\geq Q/2\). Also
\[
\frac{M_m}{Q^3}=\mu_q(1-q^{-D})(1-q^{1-D})(1-q/Q).
\]
The difference of the product on the right from 1 is at most \(2q/Q\), and raising it to power \(r\) multiplies this bound by at most \(r\). Since \(\mu_q\leq3q^2\leq q^4\), these bounds together give
\[
\left|\mathbb E A_{r,m}-\frac{\mu_q^r}{r!}\right|
\leq \frac{\mu_q^r}{r!}\bigl(2rq+2rq^{2r+2}+r^2q^3\bigr)q^{-m}
\leq q^{10r+12-m}.
\tag{9}
\]
The loose final bound follows from \(r\leq2^r\leq q^r\) and \(q\geq2\).

Choose \(L=24q^2+1\), which is odd and at least \(8\mu_q\). The lower Bonferroni bound at \(j=0,s=L\), using (8)–(9), differs from the numerical sum \(\sum_{r=0}^L(-1)^r\mu_q^r/r!\) by at most
\[
(L+1)q^{16L^2+36L+13-m}.
\]
This upper bound on the loss includes the probability difference from replacing \(X_m\) by \(Y_m\). For \(m\geq100(L+1)^2\) it is at most \(q^{-L}\leq2^{-L}<e^{-\mu_q}/4\). Here \(\mu_q\geq1\), \(L\geq8\mu_q\) and \(\log2>1/2\). Taylor's remainder for the exponential bounds the difference between the numerical sum and \(e^{-\mu_q}\) by \(\mu_q^{L+1}/(L+1)!\leq(e/8)^{L+1}<e^{-\mu_q}/4\), where \(e\) in \(e/8\) is the base of natural logarithms. Consequently \(\Pr(X_m=0)>e^{-\mu_q}/2>0\) throughout this range, proving the effective assertion.

## 6. Independent finite checks

[WITNESSES.txt](WITNESSES.txt) stores the three binary scattered bases, using binary coefficient masks in polynomial bases. Both programs establish that the indicated moduli define fields by checking that the residue of \(Z\) has order \(2^m-1\). The Python check verifies that all \(2^{m+3}-1\) nonzero binary combinations give nonzero distinct normalized projective points; duplicate basis directions are rejected as a negative control. It also forms a trace-dual system for \(m=7\) and directly verifies the ranks of all projective codeword directions. The independent C++ check uses carryless multiplication and binary rank instead: for every \(\lambda\in K\setminus\mathbb F_2\), the two lists of basis vectors for \(U\) and \(\lambda U\) together have rank \(2(m+3)\). This is equivalent to \(U\cap\lambda U=0\) and hence to scatteredness. A separate \(\mathbb F_{16}\) direct-block regression enumerates the projective mixtures of all 196 ordered pairs of rank-two normalized blocks; it includes cases where equivalent value spaces really do yield extra low-rank lines. These checks are illustrative and independent from the proof of the limiting law.
