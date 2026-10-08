# Exact four-branch classification of symmetric-group three-subset atom moduli

**Research note — 2026-10-08.** Complete analytic primal–dual reduction with independently replayable integer/rational polynomial positivity certificates. No external human peer review or full Lean formalization is claimed.

## Abstract

Let \(S_n\) act on its three-element subsets. For probability laws on \(S_n\) that send every specified triple uniformly among all triples, consider the sharp constant comparing the deviation of one permutation atom from uniform with total variation. We determine its **exact value for every degree \(n\ge3\)**. For all \(n\ge48\) the answer is one of **four explicit rational functions of \(m=\lfloor n/4\rfloor\)**, selected by \(n\bmod4\); the remaining 45 degrees are determined by previously published fixed rational primal–dual certificates and are tabulated here. The all-degree formula is proved by positive, exactly marginal-matched conjugacy-class measures and a dual that is valid simultaneously on every realizable short-cycle type. The latter infinite constraint is reduced analytically to a finite list of one-variable polynomial sign comparisons, each proved by a frozen exact coefficient certificate. An immediate consequence is the sharp third-order asymptotic expansion, whose first arithmetic-periodic term occurs at order \(n^{-3}\). This removes the combinatorial maximum over all maximal minors from the previously established universal determinant formula **in the complete \(k=3\) family**.

## 1. Definitions and the complete answer

Put \(\Omega_n=\binom{[n]}3\), \(N=\binom n3\), and let \(u_n\) be uniform on \(S_n\). A probability law \(\nu\) on \(S_n\) is admissible if

\[
\nu\{g:g(E)=H\}=\frac1N
\qquad(E,H\in\Omega_n).
\]

The sharp single-atom/TV modulus is

\[
C_n^{(3)}
=\sup_{\substack{\nu\ne u_n\\\nu\ \mathrm{admissible}}}
\frac{|\nu(\mathrm{id})-1/n!|}{\|\nu-u_n\|_{\mathrm{TV}}}.
\tag{1}
\]

Left translation gives the same constant for any other chosen permutation atom.

Introduce

\[
\begin{aligned}
P_0(m)&=18m^4+33m^3-48m^2-19m-4,\\
P_1(m)&=72m^4+246m^3-103m^2-336m+37,\\
P_{2a}(m)&=3m^2+5m-4,\qquad
P_{2b}(m)=6m^2+11m+2,\\
P_3(m)&=12m^5+65m^4+78m^3-42m^2-70m-10.
\end{aligned}
\tag{2}
\]

**Theorem 1 (complete exact three-subset spectrum).** For every \(n=4m+r\ge48\) with \(r\in\{0,1,2,3\}\), the exact optimum in (1) is

\[
\boxed{
C_{4m+r}^{(3)}=
\begin{cases}
\dfrac{(2m-1)(18m^4-3m^3+30m^2-19m-38)}
      {2(m+2)P_0(m)}, &r=0,\\[7pt]
\dfrac{72m^5+66m^4+11m^3-2m^2-149m-34}
      {(m+2)P_1(m)}, &r=1,\\[7pt]
\dfrac{2m(18m^5+45m^4+82m^3+37m^2-22m-16)}
      {(m+3)(2m+1)P_{2a}(m)P_{2b}(m)}, &r=2,\\[7pt]
\dfrac{12m^6+47m^5+75m^4+24m^3-68m^2-68m-10}
      {(m+3)P_3(m)}, &r=3.
\end{cases}}
\tag{3}
\]

Every value is attained by a genuinely nonnegative probability distribution with exactly uniform triple-image marginals for all sufficiently small positive perturbation amplitudes. More sharply, the four branches are certified already for \(m\ge6\) when \(r=0,2\), and for \(m\ge12\) when \(r=1,3\).

The remaining degrees \(3\le n<48\) have the following **fixed exact values**, previously established by independent integer/rational primal–dual certificates. The cases \(n=3,4,5\) follow directly from trivial action and subset complementation; degrees \(6,\ldots,47\) have published exact machine-replayable certificates.

| \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) |
|---:|:---|---:|:---|---:|:---|
| 3 | 1 | 18 | 5656/11331 | 33 | 87797/137207 |
| 4 | 1/2 | 19 | 3859/7609 | 34 | 545536/842061 |
| 5 | 1/3 | 20 | 169/322 | 35 | 182539/279521 |
| 6 | 5/14 | 21 | 7411/13909 | 36 | 502061/759506 |
| 7 | 5/14 | 22 | 2485/4554 | 37 | 1172759/1761089 |
| 8 | 89/244 | 23 | 6219/11242 | 38 | 532758/791863 |
| 9 | 259/691 | 24 | 32461/57220 | 39 | 2414009/3563619 |
| 10 | 368/935 | 25 | 80848/140761 | 40 | 284639/416012 |
| 11 | 1027/2593 | 26 | 108592/185523 | 41 | 218591/317459 |
| 12 | 97/232 | 27 | 264407/446661 | 42 | 973110/1401127 |
| 13 | 283/661 | 28 | 1963/3253 | 43 | 582217/833339 |
| 14 | 1328/2975 | 29 | 1587/2603 | 44 | 115031/163280 |
| 15 | 14311/31629 | 30 | 102746/165985 | 45 | 261973/369811 |
| 16 | 5579/11744 | 31 | 1224263/1959245 | 46 | 6730394/9431541 |
| 17 | 1679/3469 | 32 | 36961/58264 | 47 | 14974581/20875631 |

Thus (3) plus this complete finite table determines **every integer \(n\ge3\)**. No minimization, maximization, numerical LP, or implicit optimization parameter remains in the answer.

## 2. Exact polynomial orbitals for the action on triples

A permutation \(g\in S_n\) is summarized by \((x,y,z)\), the numbers of its fixed points, 2-cycles, and 3-cycles. The remaining vertices belong to cycles of length at least four; therefore

\[
R=n-x-2y-3z\in\{0\}\cup\{4,5,6,\ldots\}.
\tag{4}
\]

Conversely every triple of nonnegative integers satisfying (4) is realizable by a permutation, taking one residual \(R\)-cycle when \(R>0\).

For \(j=0,1,2,3\) let

\[
F_j(g)=\#\{E\in\Omega_n:|E\cap g(E)|=j\}.
\]

Use the three exact binomial moments

\[
\begin{aligned}
M_1&=\frac{n-2}{2}\bigl(2n+(n-3)x\bigr),\\
M_2&=\frac{n-2}{2}x(x-1)+(x+1)(n-x)+(n-4)y,\\
M_3&=\frac{x(x-1)(x-2)}6+xy+z.
\end{aligned}
\tag{5}
\]

Then binomial inversion gives the **integer polynomial identities**

\[
\boxed{
F_0=N-M_1+M_2-M_3,\quad
F_1=M_1-2M_2+3M_3,\quad
F_2=M_2-3M_3,\quad
F_3=M_3.
}
\tag{6}
\]

For completeness, \(M_j=\sum_E\binom{|E\cap g(E)|}{j}\). The formula for \(M_1\) follows by counting a selected fixed vertex and a selected moved vertex with its preimage. For \(M_2\), count whether a selected predecessor pair has zero, one, or two internal predecessor edges: these are respectively \((n-2)\binom x2\), \((x+1)(n-x)+(n-4)y\) after simplification. Finally \(M_3\) counts invariant triples, which can only consist of three fixed vertices, a transposition plus one fixed point, or a 3-cycle. Solving the binomial-moment identities yields (6). These formulas are also independently implied by the earlier exact two-state cycle-index transfer theorem.

## 3. Five explicit supporting conjugacy classes

For \(n=4m+r\) consider the following **five realizable and distinct** short-cycle profiles, in the order \(I,K,H,T,E\). Each profile represents a uniform probability law on one actual conjugacy class; any residual vertices form one long cycle.

| \(r\) | \(I\) | \(K\) | \(H\) | \(T\) | \(E\) |
|---:|:---|:---|:---|:---|:---|
| 0 | \((4m,0,0)\) | \((3m-2,0,0)\) | \((0,2m,0)\) | \((4m-2,1,0)\) | \((m-3,0,m+1)\) |
| 1 | \((4m+1,0,0)\) | \((3m-1,0,0)\) | \((0,2m-1,1)\) | \((4m-1,1,0)\) | \((m-2,0,m+1)\) |
| 2 | \((4m+2,0,0)\) | \((3m-1,0,0)\) | \((0,2m+1,0)\) | \((4m,1,0)\) | \((m-2,0,m)\) |
| 3 | \((4m+3,0,0)\) | \((3m,0,0)\) | \((0,2m,1)\) | \((4m+1,1,0)\) | \((m-2,0,m)\) |

The residual lengths for \(E\) are \(0,0,4,5\), respectively. Write \(\mathbf f(X)=(F_0(X),F_1(X),F_2(X))\) for the polynomial count vector (6).

Define rational weights \(p_I,p_K,p_H,q_T,q_E\) as the solution of the **entirely explicit \(5\times5\) linear system**

\[
\begin{cases}
p_I+p_K+p_H=1,\\
q_T+q_E=1,\\
p_I F_j(I)+p_K F_j(K)+p_H F_j(H)
=q_T F_j(T)+q_E F_j(E),\quad j=0,1,2.
\end{cases}
\tag{7}
\]

This is a rational linear system whose coefficients are the integer polynomials (5)–(6) evaluated at the table entries. It has a unique solution for every \(m\ge12\), and **all five entries are strictly positive**. Its first entry is exactly the respective rational expression in (3).

Consequently the central probability measures

\[
P=p_IU_I+p_KU_K+p_HU_H,\qquad
Q=q_TU_T+q_EU_E
\tag{8}
\]

are nonnegative, normalized, and disjointly supported. Since the action on ordered triples has exactly four orbitals indexed by intersection cardinality, equality of the three \(F_0,F_1,F_2\) moments plus total mass in (7) implies equality of **every** individual triple-image marginal for \(P,Q\). For sufficiently small rational \(\varepsilon>0\),

\[
\nu_\varepsilon=u_n+\varepsilon(P-Q)
\]

is a genuine admissible probability law with total variation \(\varepsilon\) and identity atom increase \(p_I\varepsilon\). Thus

\[
C_n^{(3)}\ge p_I.
\tag{9}
\]

The rest of the proof constructs a matching universal dual certificate.

## 4. Exact dual and a finite symbolic positivity lemma

Define rational coefficients \(\lambda_0,\lambda_1,\lambda_2,U,L\) by the equally explicit contact system

\[
\begin{cases}
\lambda\cdot\mathbf f(X)+U=\mathbf1_{\{X=I\}},
&X\in\{I,K,H\},\\
\lambda\cdot\mathbf f(X)+L=0,
&X\in\{T,E\}.
\end{cases}
\tag{10}
\]

Its contact matrix consists of rows
\((F_0(X),F_1(X),F_2(X),1,0)\) on the first three types and
\((F_0(X),F_1(X),F_2(X),0,1)\) on the last two. Exact inversion gives

\[
U=1,\qquad L=1-p_I.
\tag{11}
\]

The primal and dual \(5\times5\) determinants are negatives of one another. The dual determinant is explicitly:

\[
\begin{array}{c|l}
r&\det B_r(m)\\\hline
0&\frac43m(m-1)(m+2)(2m-1)(4m-3)P_0(m)\\
1&\frac1{12}m(m+2)(2m-1)(4m-3)(4m-1)P_1(m)\\
2&\frac23m(m+3)(2m-1)(2m+1)(4m-1)P_{2a}(m)P_{2b}(m)\\
3&m(m+3)(4m-1)(4m+1)P_3(m)
\end{array}
\tag{12}
\]

All these determinants are positive for \(m\ge12\), as can be checked directly by expanding the remaining factors in \(q=m-12\), so both systems are nondegenerate.

For arbitrary \(g\), define the central dual function

\[
h(g)=\mathbf1_{\{g=I\}}-\sum_{j=0}^2\lambda_jF_j(g).
\tag{13}
\]

The essential statement is

\[
\boxed{L\le h(g)\le1\quad\text{for every }g\in S_n.}
\tag{14}
\]

We give an explicit **all-parameter finite positivity reduction** proving (14), rather than asking a solver to check infinitely many parameter choices.

For a nonidentity permutation with short-cycle counts \((x,y,z)\), write

\[
h(g)=\frac{A_r(m,x,y,z)}{D_r(m)},\qquad D_r(m)>0.
\tag{15}
\]

Here \(A_r\) is the polynomial obtained by inserting (6) and the unique rational contact solution (10) into (13) and clearing its positive denominator \(D_r\). To eliminate ambiguity, the four reduced denominators are fixed as

\[
\begin{array}{c|l}
r&D_r(m)\\\hline
0&4m(m+2)P_0(m)\\
1&m(m+2)P_1(m)\\
2&2(m+3)(2m+1)P_{2a}(m)P_{2b}(m)\\
3&2(m+3)P_3(m).
\end{array}
\tag{16}
\]

The exact rational checker independently reconstructs every coefficient of \(A_r\) from (5), (6), (10) and (16), without any numerical optimization. It also checks that \(A_r\) is affine in \(y\) and \(z\), that its \(z\)-coefficient \(A_z\) is a negative polynomial depending only on \(m\), and that \(A_y(x)\) is affine and strictly decreasing in \(x\).

**Lemma 2 (universal upper and lower dual bounds).** For the contact laws (10), equation (14) holds for every \(n=4m+r\) with \(m\ge12\). In fact the same exact proof works for \(r=0,2\) already at \(m\ge6\).

**Proof.** For the two relevant integer cutoffs \(a_r,b_r\) and the lower contact location \(e_r\), use

| \(r\) | upper cutoff \(a_r\) | lower cutoff \(b_r\) | \(e_r\) | residual minima at \(x=e_r,e_r+1\) when \(y=0\) |
|---:|:---|:---|:---|:---|
| 0 | \(2m-4\) | \(2m-3\) | \(m-3\) | \(0,5\) |
| 1 | \(2m-3\) | \(2m-3\) | \(m-2\) | \(0,5\) |
| 2 | \(2m-3\) | \(2m-2\) | \(m-2\) | \(4,0\) |
| 3 | \(2m-2\) | \(2m-2\) | \(m-2\) | \(5,4\) |

Let \(a=n-2\). A nonidentity permutation always satisfies \(0\le x\le a\); and the remaining cycle constraints imply \(y,z\ge0\) and \(2y+3z\le n-x\).

The following **finite sign facts** are exact identities and rational polynomial inequalities, not numerical approximations. In the frozen certificate referenced below, each is normalized into a rational polynomial in the variable \(q=m-m_0\), with \(m_0=6\) for \(r=0,2\) and \(m_0=12\) for \(r=1,3\), and both its numerator and denominator have **nonnegative integer coefficients** with the denominator positive at \(q=0\). The list of these sign facts is generated explicitly from (5)–(16) and can be checked by coefficient multiplication.

**Upper bound.** The coefficients \(A_z<0\) and \(A_y(x)\) are respectively constant and decreasing in \(x\). The sign facts give \(A_y(a_r)\ge0\) and \(A_y(a_r+1)\le0\). Hence, if \(x\le a_r\),

\[
A_r(m,x,y,z)\le A_r\bigl(m,x,(n-x)/2,0\bigr).
\tag{17}
\]

Set
\[
V(x)=D_r-A_r\bigl(m,x,(n-x)/2,0\bigr)
=V(0)+xQ_{\mathrm{up}}(x).
\]
The polynomial \(Q_{\mathrm{up}}\) is an upward quadratic with
\(Q_{\mathrm{up}}'(a_r)\le0\) and
\(Q_{\mathrm{up}}(a_r)+V(0)>0\).
For even \(r\), \(V(0)=0\), proving \(V(x)\ge0\) for all \(0\le x\le a_r\). For odd \(r\), \(V(0)<0\); for every integer \(1\le x\le a_r\), the same inequalities imply
\[
V(x)\ge V(0)+xQ_{\mathrm{up}}(a_r)
\ge V(0)+Q_{\mathrm{up}}(a_r)>0.
\]

The remaining odd-residue case \(x=0\) uses feasibility, not a false continuous relaxation: because \(n\) is odd and \(x=0\), the maximum feasible number of 2-cycles is \((n-3)/2\). At that value a 3-cycle is compulsory, and it is exactly the upper contact profile \(H=(0,(n-3)/2,1)\), with \(h(H)=1\). For all smaller \(y\le(n-5)/2\), the signed coefficient \(A_y(0)>0\) and \(A_z<0\) give
\(A_r(0,y,z)\le A_r(0,(n-5)/2,0)\le D_r\).
The last inequality is another frozen integer-polynomial sign fact. Thus the upper bound holds in the entire early range.

If \(x\ge a_r+1\), the negative sign of \(A_y\) gives
\(A_r(x,y,z)\le A_r(x,0,0)\).
Let \(K\) denote the fixed-point count of the class \(K\) in Section 3, and put \(t=x-K\). The contact equation forces the exact factorization

\[
D_r-A_r(m,K+t,0,0)=tQ_{\mathrm{late}}(t),
\tag{18}
\]

where \(Q_{\mathrm{late}}\) is an upward quadratic with positive quadratic and linear coefficients. The integer \(t\) ranges from \(-m-1\) to a nonnegative upper endpoint. The sign facts give
\[
Q_{\mathrm{late}}(1)>0,\qquad
Q_{\mathrm{late}}(-1)<0,\qquad
Q_{\mathrm{late}}(-m-1)<0.
\]
For \(t\ge1\), positivity of the derivative on \(t\ge0\) yields \(Q_{\mathrm{late}}(t)>0\). For negative integer \(t\), convexity and the two endpoint inequalities yield \(Q_{\mathrm{late}}(t)<0\) throughout \([-m-1,-1]\). Since \(tQ_{\mathrm{late}}(t)\ge0\) in either case, and it vanishes at \(t=0\), the upper bound is complete.

**Lower bound.** Because \(A_z<0\) and \(z\le(n-x-2y)/3\),

\[
A_r(m,x,y,z)
\ge A_r\bigl(m,x,0,(n-x)/3\bigr)
+\bigl(A_y(x)-2A_z/3\bigr)y.
\tag{19}
\]

Write \(B(x)=A_y(x)-2A_z/3\). It is affine and strictly decreasing. The sign facts give \(B(b_r)\ge0\) and \(B(b_r+1)\le0\).

For \(x\le b_r\), inequality (19) is minimized at \(y=0\) under the continuous relaxation. Put \(t=x-e_r\), and let \(L\) be the lower dual contact constant. The exact cubic factorization is

\[
A_r\bigl(m,e_r+t,0,(n-e_r-t)/3\bigr)-D_rL
=Z_r+tQ_{\mathrm{early}}(t),
\tag{20}
\]

where \(Z_r\le0\), and \(Q_{\mathrm{early}}(t)\) is a concave quadratic: its \(t^2\)-coefficient is negative and its \(t\)-coefficient positive. When \(r=0,1\), \(Z_r=0\); when \(r=2,3\), \(Z_r<0\).

For integer \(t\le-1\), the cubic in (20) is positive. In residues \(0,2,3\), all its derivative terms are strictly negative for \(t\le-1\), and the value at \(-1\) is positive. In residue \(1\), \(Z_r=0\), the constant term of \(Q_{\mathrm{early}}\) is positive, and the quadratic increases with \(t\) on \(t\le-1\); the checked positivity of the cubic at \(-1\) implies \(Q_{\mathrm{early}}(t)<0\), so its product with \(t<0\) is positive.

For integer \(2\le t\le b_r-e_r\), concavity gives
\[
Q_{\mathrm{early}}(t)\ge
\min\{Q_{\mathrm{early}}(2),Q_{\mathrm{early}}(b_r-e_r)\}.
\]
Both exact sign inequalities
\[
Z_r+2Q_{\mathrm{early}}(2)>0,\qquad
Z_r+2Q_{\mathrm{early}}(b_r-e_r)>0
\]
are included in the frozen polynomial certificate. As \(Z_r\le0\), this yields \(Z_r+tQ_{\mathrm{early}}(t)>0\) for all such \(t\).

Only \(t=0,1\) require an integer-feasibility correction. If \(y\ge1\), inequality (19) improves by at least \(B(e_r+t)>0\), and the checked expressions
\[
Z_r+tQ_{\mathrm{early}}(t)+B(e_r+t)\ge0
\qquad(t=0,1)
\tag{21}
\]
close those two cases.

If \(y=0\), then the residual
\(R=n-x-3z\) must be **zero or at least four**. For \(x=e_r+t\), \(t=0,1\), let \(\rho_{r,t}\in\{0,4,5\}\) denote the smallest admissible residual congruent to \(n-x\pmod3\); these eight explicit values are the final column of the cutoff table. Hence
\(z\le(n-e_r-t-\rho_{r,t})/3\).
Because \(A_z<0\), the corresponding lower deficit is at least
\[
Z_r+tQ_{\mathrm{early}}(t)-\rho_{r,t}A_z/3\ge0.
\tag{22}
\]
These eight inequalities are part of the same frozen exact polynomial certificate. Equality in (22) at \(t=0\) is precisely the designated lower contact \(E\).

For \(x\ge b_r+1\), the coefficient \(B(x)\le0\), so (19), together with \(y\le(n-x)/2\), gives
\[
A_r(m,x,y,z)\ge A_r\bigl(m,x,(n-x)/2,0\bigr).
\]
Write \(t=(n-2)-x\), an integer in
\(0\le t\le(n-2)-(b_r+1)\). The lower contact \(T\) forces the factorization

\[
A_r\bigl(m,n-2-t,1+t/2,0\bigr)-D_rL
=tQ_{\mathrm{right}}(t).
\tag{23}
\]
The quadratic \(Q_{\mathrm{right}}\) has positive leading coefficient, nonpositive derivative at the right endpoint of the interval, and **strictly positive value there**. Therefore it is decreasing on the whole interval and positive everywhere, giving \(tQ_{\mathrm{right}}(t)\ge0\). The lower bound is proved.

Together with the identity case \(h(I)=1\), these arguments establish (14) for every feasible integer \((x,y,z)\) in every degree of the stated parameter range. QED.

### Exact verification of the finite sign lemma

This proof reduces an **infinite family of polynomial inequalities** to exactly **40, 42, 41, 43** named rational-polynomial sign conditions, in residues \(0,1,2,3\) respectively. These include the signs, endpoints and derivatives explicitly used above, both \(5\times5\) determinant signs, positivity of every primal weight, and nonvanishing denominators of the contact solution.

The complete **frozen polynomial coefficient certificate** is published as

- certificates/three_subset_eventual_4branch_signs.json.

Each record contains a named algebraic expression, the coefficient arrays of its reduced numerator and denominator after \(q=m-m_0\) substitution, the exact five supporting types, and all rational primal and dual parameters. The arrays are all coefficientwise nonnegative, the denominator is strictly positive at \(q=0\), and, apart from the four exact lower-contact equalities, the sign conditions have positive constant term. Therefore they certify the required inequalities for **every real \(q\ge0\)**, a fortiori every integer \(m\ge m_0\).

The standalone checker

- code/check_rank3_eventual_formula.py

reconstructs all \(F_j\) from the polynomial identities (5)–(6), solves both specified \(5\times5\) systems with exact rational symbolic arithmetic, verifies all five primal contacts and moment equations, recomputes each named sign expression, expands its numerator/denominator in \(q\), and requires exact agreement with the frozen certificate arrays. It does not call a numerical LP, search over finite \(n\), or assume the conjectured answer. Thus the algebraic identities and polynomial coefficient signs are **independently inspectable and replayable**; the mathematical reduction above explains why those finite coefficient inequalities prove the infinite theorem.

## 5. Matching upper and lower bounds

From Lemma 2, the dual function (13) satisfies \(L\le h(g)\le1\) for every permutation. For an arbitrary admissible law \(\nu\), the signed measure \(\nu-u_n\) has zero total mass and vanishing orbital averages \(F_0,F_1,F_2\); hence

\[
\nu(I)-1/n!=\sum_{g\in S_n}(\nu(g)-u_n(g))h(g).
\]

Any signed zero-total-mass measure of total variation \(\delta\) paired with a function of oscillation at most \(1-L\) has absolute integral at most \((1-L)\delta\). Therefore

\[
C_n^{(3)}\le1-L.
\]

The positive class-mixture construction in Section 3 gives \(C_n^{(3)}\ge p_I\); the algebraic contact identity (11) gives \(1-L=p_I\). Thus

\[
C_n^{(3)}=p_I,
\]

with the four explicit rational expressions (3). This proves the infinite part of Theorem 1. The finite table for \(n<48\) is independently established by the fixed exact primal–dual certificates already published for degrees \(6\le n\le23\) and \(24\le n\le120\), together with the elementary complement cases \(3,4,5\). Hence the entire theorem is proved. QED.

## 6. New sharp arithmetic asymptotics

**Corollary 3 (second- and third-order structure).** For all \(n\to\infty\), with \(r=n\bmod4\),

\[
\boxed{
C_n^{(3)}
=1-\frac{18}{n}+\frac{288}{n^2}
-\frac{\gamma_r}{n^3}+O(n^{-4}),
}
\tag{24}
\]

where

\[
(\gamma_0,\gamma_1,\gamma_2,\gamma_3)
=(3840,4000,3840,3968).
\]

**Proof.** Expand each rational expression in (3) at \(m=\infty\), substitute \(m=(n-r)/4\), and collect powers of \(1/n\). The calculations are exact formal rational-function expansions. The first two coefficients are independent of the residue, while the cubic coefficient depends on \(r\), as stated. QED.

Thus the first arithmetic-periodic correction appears precisely at \(n^{-3}\), sharpening the previous general bound
\(C_n^{(3)}=1-18/n+O(n^{-2})\) by two orders. The entire formula is exact for each \(n\ge48\), not merely an asymptotic expansion.

## 7. Independent integer replay, scope, and provenance

A **second checker**, code/check_rank3_eventual_integer_replay.py, uses only Python standard-library integers and fractions. It reconstructs the primal and dual by its own \(5\times5\) Fraction Gaussian elimination and, for selected degrees between 48 and 204, enumerates **every realizable triple** \((x,y,z)\) satisfying (4), checking every dual inequality exactly. It also compares the four formulas against **all 73 published fixed exact coefficients** for \(48\le n\le120\). In its initial isolated run, it checked 1,803,943 distinct cycle types over 23 full-degree tests (including degrees 121–124, 161–164, and 201–204), with zero failures.

These finite tests are **not** used to extrapolate the infinite theorem. The global proof is the exact polynomial sign certificate and the analytic case reduction in Section 4, plus the explicit matching primal construction. The original numerical LP experiments were used only to discover possible contact classes; the published proof uses the fixed symbolic contact systems and exact arithmetic alone.

The mathematical tools of orbital averaging, integer cycle counts, rational matrix inversion, and polynomial coefficient positivity are classical. The present manuscript claims the proved four-branch formula and its consequences, not worldwide first priority, external peer review, or Lean kernel verification. The formula settles the **entire \(k=3\) rank**; the analogous elementary branch classification for arbitrary variable \(k\) remains open, despite the previously published general exact maximal-minor algorithm.
