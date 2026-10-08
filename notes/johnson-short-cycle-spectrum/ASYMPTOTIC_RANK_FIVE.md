# Sharp asymptotics of the four-subset marginal-preserving atom modulus

**Research supplement, 8 October 2026.** This note proves the first higher-rank case of the Chebyshev asymptotic problem raised in Section 23 of the [permutation-action manuscript](../sharp-robust-permanent/paper.md). It concerns the \(S_n\) action on its four-element subsets. The [fixed-rank transfer theorem](README.md) and orbital primal--dual theorem supply the general setting. Both the upper and lower bounds below hold for **all sufficiently large degrees**, with no extrapolation from finite optimizations. We make no claim of historical priority or external referee certification.

## 1. Main theorem

Let \(u_n\) be the uniform probability measure on \(S_n\). Let \(C_{n,4}\) be the best constant in

\[
\left|\nu(\sigma)-\frac1{n!}\right|
\le C_{n,4}\|\nu-u_n\|_{\rm TV}
\qquad(\sigma\in S_n)
\]

for all probability laws \(\nu\) on \(S_n\) having uniform image marginals on **each** four-element subset:

\[
\nu\{g:gE=H\}=\binom n4^{-1}
\quad\text{for all }E,H\in\binom{[n]}4.
\]

**Theorem 1 (sharp rank-five asymptotic law).** As \(n\to\infty\),

\[
\boxed{\displaystyle
C_{n,4}=1-\frac{32}{n}+O(n^{-2}),\qquad
\lim_{n\to\infty}n(1-C_{n,4})=32.}
\tag{1}
\]

In addition, there is an **explicit uniform dual bound**: for every integer \(n\ge4096\),

\[
\boxed{\displaystyle C_{n,4}
\le1-\frac{32}{n}+\frac{35\,000\,000}{n^2}.}
\tag{2}
\]

For the matching lower bound, we construct for every sufficiently large integer \(n\) two **positive rational conjugation-invariant probability measures** with identical complete four-subset image marginals and identity-atom gap \(1-32/n+O(n^{-2})\). Their supports are given by six explicit cycle types.

The leading coefficient \(32=2\cdot4^2\) settles the \(k=4\) case of the higher-rank asymptotic conjecture in the predecessor manuscript. No assertion is made for \(k\ge5\) or for the exact finite-\(n\) optimizer beyond the separately certified range \(11\le n\le50\).

## 2. A dual certificate and its exact polynomial expansion

For a permutation \(g\in S_n\), put

\[
F_j(g)=\#\{E\in\binom{[n]}4:|E\cap gE|=j\},
\qquad 0\le j\le4.
\]

These are integer linear combinations of the four-subset image marginal indicators; hence every signed marginal-preserving perturbation annihilates each \(F_j\). For \(j=0,1,2,3\), define the integer coefficient arrays

\[
A=(0,-96,128,-96),\qquad
B=(-1536,4320,-6784,2016),
\tag{3}
\]

and the rational dual function

\[
h_n(g)=\mathbf1_{\{g=e\}}
-\frac1{n^5}\sum_{j=0}^3(nA_j+B_j)F_j(g).
\tag{4}
\]

At the identity \(F_0(e)=\cdots=F_3(e)=0\), so \(h_n(e)=1\).

Let \(x,y,z,w\) denote the counts of cycles of lengths \(1,2,3,4\) in \(g\), respectively. Set

\[
a=x/n,\quad b=y/n,\quad c=z/n,\quad d=w/n.
\]

For \(g\ne e\), we have

\[
0\le a\le1-\frac2n,\qquad
0\le b\le\frac{1-a}{2},\qquad
0\le c,d\le1.
\tag{5}
\]

**Lemma 2 (exact—not asymptotic—dual identity).** For every \(g\ne e\),

\[
h_n(g)=H(a)+\frac{J(a,b)}n
+\frac{R_3(a,b,c)}{n^2}
+\frac{R_2(a,b,c,d)}{n^3}
+\frac{R_1(a,b,c,d)}{n^4},
\tag{6}
\]

where

\[
\begin{aligned}
H(a)&=16a(1-a)(2a-1)^2
     =1-(8a^2-8a+1)^2,\\
J(a,b)&=16(176a^4-408a^3-48a^2b+310a^2
                   +48ab-85a-10b+7),\\
R_3(a,b,c)&=16(1248a^3+2112a^2b-2481a^2
 -2544ab-96ac+1485a-48b^2+668b+48c-252),\\
R_2(a,b,c,d)&=16(4932a^2+11712ab+4224ac-7637a
 +2112b^2-7418b-2592c-96d+2705),\\
R_1(a,b,c,d)&=64(2049a+4426b+3456c+1056d-2049).
\end{aligned}\tag{7}
\]

Moreover, for all \(n\ge1\),

\[
\left|\frac{R_3}{n^2}+\frac{R_2}{n^3}
              +\frac{R_1}{n^4}\right|
\le\frac{1\,704\,864}{n^2}.
\tag{8}
\]

*Proof.* Use the exact transfer identity for the subset action,

\[
\sum_{j=0}^4F_j(g)t^j
=[s^4]L_+^n\prod_{\ell=1}^4
(1+(L_-/L_+)^\ell)^{m_\ell(g)},
\tag{9}
\]

where \(L_\pm\) solve
\(L^2-(1+st)L+s(t-1)=0\) and are characterized by
\(L_+=1+O(s)\), \(L_-=O(s)\).
The first four terms of the first root are

\[
L_+=1+s+(t-1)s^2+(t-1)(t-2)s^3
+(t-1)(t^2-5t+5)s^4+O(s^5).
\tag{10}
\]

Take formal logarithms of the factors of (9). If the resulting exponent truncated at order \(s^4\) is \(\sum_{i=1}^4U_i s^i\), then its \(s^4\)-coefficient is the **finite exact expression**

\[
U_4+U_1U_3+\tfrac12U_2^2
+\tfrac12U_1^2U_2+\tfrac1{24}U_1^4.
\tag{11}
\]

Each \(U_i\) is a polynomial in \(t\), with rational coefficients linear in \(n,x,y,z,w\). Consequently every \(F_j\) is a rational polynomial of total degree at most four in those five integer parameters. Extract the coefficients of \(t^0,\ldots,t^3\), substitute (3) into (4), and replace \(x,y,z,w\) by \(na,nb,nc,nd\). Collecting powers of \(n\) yields **exactly** (6)--(7), without a dropped remainder term. The public [symbolic checker](check_k4_asymptotic_algebra.py) independently reconstructs (9)--(11) using exact rational polynomial arithmetic and checks every coefficient of (6)--(7).

Finally \(a,b,c,d\in[0,1]\). The sums of absolute monomial coefficients of \(R_3,R_2,R_1\) are, respectively, \(175712\), \(694848\), and \(834304\). Since \(n^{-3},n^{-4}\le n^{-2}\) for \(n\ge1\), their sum \(1704864\) proves (8). These coefficient sums are themselves checked exactly by the same replayable script. QED.

## 3. Global dual control: proof of the upper bound

Put

\[
P(a)=8a^2-8a+1,\qquad
Q(a)=16(a-1)(22a-7).
\]

The polynomial identities (7) simplify to

\[
H(a)=1-P(a)^2,\qquad
J(a,b)=P(a)Q(a)+b(-64-96P(a)).
\tag{12}
\]

On \(0\le a\le1\), one has \(-1\le P(a)\le1\) and
\(|Q(a)|\le240\). If the coefficient \(-64-96P(a)\) is positive, then \(P(a)<-2/3\) and

\[
0\le b(-64-96P(a))\le16\le36P(a)^2;
\]

otherwise the term is nonpositive. Consequently

\[
J(a,b)\le240|P(a)|+36P(a)^2.
\tag{13}
\]

For \(n\ge72\), completion of the square gives

\[
H+\frac Jn
\le1-\frac12P^2+\frac{240|P|}n
\le1+\frac{28800}{n^2}.
\tag{14}
\]

We next establish the **uniform lower bound** for all nonidentity types, for \(n\ge4096\):

\[
H(a)+\frac{J(a,b)}n
\ge\frac{32}{n}-\frac{43280^2}{60n^2}.
\tag{15}
\]

We partition the allowed \(a\)-range into four intervals.

**Near zero, \(0\le a\le1/8\).** Since \(b\le1/2\),

\[
J(0,b)=112-160b\ge32.
\]

Direct differentiation of (7) gives
\(|\partial_aJ(a,b)|\le3408\) on this rectangle. Also

\[
H(a)\ge\frac{63}{8}a.
\]

Therefore \(H+J/n\ge32/n+a(63/8-3408/n)\ge32/n\) for \(n\ge4096\).

**Near the middle zero, \(3/8\le a\le5/8\).** We have

\[
J(1/2,b)=32+32b\ge32,\qquad
|\partial_aJ(a,b)|\le43280
\]

throughout the ambient rectangle \(0\le a\le1\), \(0\le b\le1/2\). Also \(H(a)\ge15(a-1/2)^2\). With \(u=|a-1/2|\), completing the square yields

\[
H+J/n\ge32/n+15u^2-43280u/n
\ge32/n-\frac{43280^2}{60n^2}.
\tag{16}
\]

**Near one, \(7/8\le a\le1-2/n\).** Put \(s=1-a\). Then \(2/n\le s\le1/8\), \(b\le s/2\), and (12) gives \(|J(a,b)|\le320s\). Moreover

\[
H(1-s)=16s(1-s)(1-2s)^2,\qquad
\frac d{ds}H(1-s)
=16(1-2s)(1-8s+8s^2)\ge\frac32
\]

on \([0,1/8]\). Hence for \(n\ge4096\), the function \(H(1-s)-320s/n\) increases with \(s\) and is minimized at \(s=2/n\). Direct substitution gives

\[
H+J/n\ge H(1-2/n)-640/n^2
\ge32/n-960/n^2.
\tag{17}
\]

**Away from the zeros, \(1/8\le a\le3/8\) or \(5/8\le a\le7/8\).** In these intervals,

\[
H(a)\ge\frac7{64},\qquad |J(a,b)|\le320.
\]

Thus for \(n\ge4096\),

\[
H+J/n\ge7/64-320/n\ge32/n.
\tag{18}
\]

The four intervals cover every \(g\ne e\), so (15) follows. Combine (8), (14) and (15):

\[
\frac{32}{n}
-\frac{43280^2/60+1704864}{n^2}
\le h_n(g)
\le1+\frac{28800+1704864}{n^2}
\qquad(g\ne e).
\tag{19}
\]

At the identity \(h_n(e)=1\), so the oscillation over **all** permutations is at most

\[
1-\frac{32}{n}
+\frac{43280^2/60+28800+2(1704864)}{n^2}
<1-\frac{32}{n}+\frac{35000000}{n^2}.
\tag{20}
\]

For any signed marginal-preserving perturbation \(v=\nu-u_n\), its positive and negative parts have equal mass \(\|v\|_{\rm TV}\), while the \(F_j\)-terms in (4) have zero integral against \(v\). Therefore \(|v(e)|\) is bounded by the oscillation of \(h_n\) times \(\|v\|_{\rm TV}\). Left translation proves the same for every prescribed atom \(\sigma\). This establishes the **explicit upper bound (2)**, not just a pointwise asymptotic estimate. QED.

## 4. Rational probability measures attaining the first-order coefficient

Put

\[
\alpha_-=\frac{2-\sqrt2}{4},\qquad
\alpha_+=\frac{2+\sqrt2}{4}.
\tag{21}
\]

For each sufficiently large integer \(n\) set

\[
l_n=\lfloor n\alpha_-\rfloor,\quad
h_n^*=\lfloor n\alpha_+\rfloor,\quad
m_n=\lfloor n/2\rfloor.
\tag{22}
\]

We use six explicit conjugacy classes of \(S_n\), labelled \(I,L,H,Z,M,T\):

| Class | Cycle type |
|---|---|
| \(I\) | \(1^n\), identity |
| \(L\) | \((n-l_n)\,1^{l_n}\) |
| \(H\) | \((n-h_n^*)\,1^{h_n^*}\) |
| \(Z\) | one \(n\)-cycle |
| \(M\) | \((n-m_n)\,1^{m_n}\) |
| \(T\) | \(2\,1^{n-2}\), a transposition |

For sufficiently large \(n\), all long cycles have length at least five, and the six classes are pairwise distinct. Here each row denotes the uniform probability measure on that conjugacy class whenever used in a probability combination.

Let \(N=\binom n4\), and write

\[
v_n(C)=N^{-1}(F_0(C),F_1(C),F_2(C),F_3(C))
\in\mathbb Q^4.
\]

Define the **four rational unknowns** \(A_L(n),A_H(n),B_Z(n),B_M(n)\) by the exact four-by-four linear system

\[
\begin{aligned}
&A_L\bigl(v_n(L)-v_n(I)\bigr)
+A_H\bigl(v_n(H)-v_n(I)\bigr)\\
&\qquad-B_Z\bigl(v_n(Z)-v_n(T)\bigr)
-B_M\bigl(v_n(M)-v_n(T)\bigr)
=n\bigl(v_n(T)-v_n(I)\bigr).
\end{aligned}
\tag{23}
\]

All its entries are exact integers divided by \(N\). We now prove it is uniquely solvable with **strictly positive rational weights** for all sufficiently large \(n\), and identify their limits.

**Lemma 3 (uniform Bernstein limit).** For fixed \(k=4\) and any \(g\in S_n\) having \(x\) fixed vertices,

\[
\frac{F_j(g)}{\binom n4}
=\binom4j(x/n)^j(1-x/n)^{4-j}+O(n^{-1}),
\quad 0\le j\le4,
\tag{24}
\]

where the \(O(n^{-1})\) is uniform in all permutations \(g\).

*Proof.* If \(E\) is a random four-subset and \(Y\) is the number of its fixed vertices, then \(|E\cap gE|\) differs from \(Y\) only when \(E\) contains both endpoints of an image edge \(v\mapsto g(v)\) with \(v\) moved. A union bound gives probability at most \(12/(n-1)\). The fixed-vertex count \(Y\) is hypergeometric; coupling four draws without replacement to four independent draws with replacement yields total variation distance at most \(\binom42/n=6/n\) to the binomial law. Adding these errors proves (24), uniformly. QED.

By (24), for each of \(L,H,Z,M\), the moment vectors \(v_n(C)\) converge at rate \(O(n^{-1})\) to the **Bernstein vector**

\[
\beta(t)=\bigl(\binom40(1-t)^4,
\binom41t(1-t)^3,
\binom42t^2(1-t)^2,
\binom43t^3(1-t)\bigr)
\]

at \(t=\alpha_-,\alpha_+,0,1/2\), respectively. The identity has \(v_n(I)=\beta(1)=(0,0,0,0)\). For a transposition, a random four-set intersects its image in precisely three points if and only if it contains one of the two exchanged vertices. Therefore

\[
F_3(T)/N=\frac{8(n-4)}{n(n-1)},\qquad
F_0(T)=F_1(T)=F_2(T)=0,
\]

and hence \(n(v_n(T)-v_n(I))\to(0,0,0,8)\).

To compute the limit of (23), apply it to polynomials \(f(t)=t^r\), \(r=1,2,3,4\), expressed uniquely in the degree-four Bernstein basis. The resulting limiting coefficient matrix, with columns ordered \(A_L,A_H,B_Z,B_M\), is

\[
V_\infty=
\begin{pmatrix}
\alpha_--1 &\alpha_+-1&1&1-2^{-1}\\
\alpha_-^2-1&\alpha_+^2-1&1&1-2^{-2}\\
\alpha_-^3-1&\alpha_+^3-1&1&1-2^{-3}\\
\alpha_-^4-1&\alpha_+^4-1&1&1-2^{-4}
\end{pmatrix}.
\tag{25}
\]

The limiting right side in these coordinates is
\((-2,-4,-6,-8)^\top\): a transposition has an \(8/n+O(n^{-2})\) probability of reducing a four-set intersection from four to three, and the derivative at \(1\) of \(t^r\) equals \(r\). Direct exact calculation in \(\mathbb Q(\sqrt2)\) gives

\[
\det V_\infty=-\frac{\sqrt2}{4096}\ne0,
\qquad
V_\infty
\begin{pmatrix}
16-8\sqrt2\\16+8\sqrt2\\2\\8
\end{pmatrix}
=
\begin{pmatrix}-2\\-4\\-6\\-8\end{pmatrix}.
\tag{26}
\]

The exact symbolic checker verifies these identities, including the radical simplification. Since the matrices and right sides in (23) converge at rate \(O(n^{-1})\) and the limiting matrix is nonsingular, (23) is invertible for all sufficiently large \(n\), its rational solution satisfies

\[
\begin{aligned}
A_L(n)&=16-8\sqrt2+O(n^{-1})>0,\\
A_H(n)&=16+8\sqrt2+O(n^{-1})>0,\\
B_Z(n)&=2+O(n^{-1})>0,\\
B_M(n)&=8+O(n^{-1})>0.
\end{aligned}
\tag{27}
\]

All strict inequalities hold once \(n\) is sufficiently large.

Define the conjugation-invariant probability measures

\[
\begin{aligned}
P_n={}&
\left(1-\frac{A_L+A_H}{n}\right)U_I
+\frac{A_L}{n}U_L+\frac{A_H}{n}U_H,\\
Q_n={}&
\left(1-\frac{B_Z+B_M}{n}\right)U_T
+\frac{B_Z}{n}U_Z+\frac{B_M}{n}U_M.
\end{aligned}
\tag{28}
\]

By (27), their weights are strictly positive and normalized for all sufficiently large \(n\). Equation (23) makes their four coordinates \(F_0,\ldots,F_3\) **exactly equal**, not asymptotically equal. The remaining \(F_4\) moments agree too, because \(\sum_{j=0}^4F_j=N\). For central laws, the orbital moments determine **every** four-subset image marginal: the ordered-pair orbitals correspond to intersection sizes \(0,\ldots,4\), and centrality makes the marginal probability constant within each orbital. Thus \(P_n\) and \(Q_n\) have exactly the same full image marginal matrices.

The measures have disjoint supports. For any sufficiently small positive rational \(\delta\), the measure \(\nu=u_n+\delta(P_n-Q_n)\) is nonnegative, has unit mass and the same image marginals as uniform. Its total variation distance from \(u_n\) is \(\delta\), and its identity atom exceeds uniform by

\[
\delta P_n(I)=
\delta\left(1-\frac{A_L(n)+A_H(n)}n\right).
\]

Therefore the **sharp** constant satisfies

\[
C_{n,4}\ge 1-\frac{A_L(n)+A_H(n)}n
=1-\frac{32}{n}+O(n^{-2}).
\tag{29}
\]

The floor choices in (22) require no floating-point comparisons: with \(u=\lfloor\sqrt{2n^2}\rfloor\), they are exactly
\(l_n=(2n-u-1)//4\) and \(h_n^*=(2n+u)//4\) in integer arithmetic. A separate [pure-rational checker](check_k4_asymptotic_primal.py) independently constructs the measures and verifies positivity and full marginal matching in nine representative degrees, including \(n=2000\). These finite tests supplement, but do not replace, the all-large-\(n\) continuity and positivity argument. QED.

## 5. Proof completion, reproduction and scope

The explicit global dual inequality (2) proves

\[
C_{n,4}\le1-\frac{32}{n}+O(n^{-2}).
\]

The full-support primal construction (28)--(29), valid for every sufficiently large integer \(n\), proves the matching reverse inequality. This establishes Theorem 1, with the **sharp** first-order constant \(32\) and an explicit—though deliberately conservative—dual error bound.

Replay from the root of the public repository:

~~~sh
# Optional exact symbolic algebra regression (requires SymPy):
python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_algebra.py

# Independent rational primal-family regression (standard library only):
python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_primal.py

# Finite sharp constants, also pure integer/rational:
python3 notes/johnson-short-cycle-spectrum/check_k4.py
python3 notes/johnson-short-cycle-spectrum/check_k4_26_50.py
~~~

The symbolic checker is a transparent exact expansion/replay of identities whose full statements and analytic proofs are given above. In particular, **neither the large-degree upper inequality nor eventual positivity of the primal family is inferred from testing finitely many values**. No numerical optimizer or heuristic computation enters the theorem's proof. The parent manuscript already established the corresponding coefficient \(18\) in subset rank three; our result resolves the **next rank** \(k=4\). Higher ranks \(k\ge5\), finite-\(n\) optimizer classification beyond degree fifty, external peer review and novelty priority remain outside this theorem.
