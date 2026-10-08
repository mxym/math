# Exact 5/14 law for simultaneous Johnson subset-image marginals

**Research note, 8 October 2026.** For every symmetric group of degree at least six, we establish the **exact sharp constant 5/14** relating the deviation of one permutation atom to total variation, among probability laws preserving uniform image marginals on *all* subset actions. Equivalently, the same constant is sharp when only the middle-size subset action is constrained. The proof gives an explicit rational dual with five evaluations of the cycle polynomial, a complete exact 44,582-partition integer certificate, an analytic bound for every larger cycle type, and a matching rational four-class primal construction. It does not use numerical optimization as a logical premise. The two proof checkers have been replayed independently from fixed public source snapshots. This work has not received independent human peer review, a Lean formalization, or a historical novelty determination.

## 1. Exact extremal statement

For each integer \(n\ge1\), let \(G=S_n\) and \(u\) be its uniform probability law. Denote by \(\Omega_k\) the \(k\)-element subsets of \([n]\). A probability law \(\nu\) on \(G\) has **uniform rank-\(k\) subset-image marginals** when

\[
\nu\{g:gE=H\}=\binom nk^{-1}
\quad\text{for every }E,H\in\Omega_k.
\tag{1}
\]

Write \(\|\nu-u\|_{\rm TV}=\tfrac12\sum_g|\nu(g)-1/n!|\). Let \(C_n^{\rm all}\) be the least \(C\) such that every law \(\nu\) satisfying (1) *simultaneously at every rank \(k=0,\ldots,n\)* obeys

\[
|\nu(\sigma)-1/n!|\le C\|\nu-u\|_{\rm TV}
\quad(\sigma\in S_n).
\tag{2}
\]

Let \(C_{n,k}\) denote the analogous sharp coefficient when only rank \(k\) is constrained.

**Theorem 1 (sharp simultaneous-rank and middle-rank law).** For every integer \(n\ge6\),

\[
\boxed{C_n^{\rm all}=C_{n,\lfloor n/2\rfloor}=\frac5{14}.}
\tag{3}
\]

The lower bound is attained, for every \(n\ge6\), by arbitrarily small positive rational perturbations of uniform measure. The upper bound applies to **all** laws \(\nu\), whether conjugation-invariant or not.

## 2. Linear dual functions from cycle polynomials

For \(g\in S_n\), write \(m_\ell(g)\) for its number of cycles of length \(\ell\). The **invariant-subset polynomial** is

\[
Q_g(z)=\prod_{\ell=1}^n(1+z^\ell)^{m_\ell(g)}
=\sum_{r=0}^n A_r(g)z^r.
\tag{4}
\]

A subset is invariant under \(g\) precisely when it is a union of full cycles, so

\[
A_r(g)=\sum_{|E|=r}\mathbf1_{\{gE=E\}}.
\tag{5}
\]

For rational \(0<q<1\), define

\[
U_q(g)=(1-q)^n Q_g(q/(1-q))
=\prod_{\ell\ge1}\bigl(q^\ell+(1-q)^\ell\bigr)^{m_\ell(g)}
=\sum_{r=0}^nq^r(1-q)^{n-r}A_r(g).
\tag{6}
\]

Thus, if \(v=\nu-u\) and \(\nu\) has all the subset-image marginals (1), then

\[
\sum_gv(g)=0,\qquad \sum_gv(g)U_q(g)=0
\tag{7}
\]

for every rational \(q\), because every diagonal image indicator in (5) has its prescribed uniform expectation. Moreover, **one-cycles contribute the factor 1 to (6)**; hence \(U_q(g)\) depends only on the lengths of nontrivial cycles.

For rational numbers \(\alpha_i\) and \(q_i\in(0,1)\), put

\[
\Phi(g)=\sum_i\alpha_i(1-U_{q_i}(g)),\qquad
h(g)=\mathbf1_{\{g=e\}}+\Phi(g).
\tag{8}
\]

Then \(\Phi(e)=0\), \(h(e)=1\), and \(\sum_gv(g)\Phi(g)=0\). If \(a\le\Phi(g)\le1\) for every \(g\ne e\), with \(0\le a\le1\), the function \(h\) has range inside \([a,1]\). The positive and negative Jordan parts of \(v\) each have mass \(\|v\|_{\rm TV}\), so

\[
|v(e)|=\left|\sum_gv(g)h(g)\right|
\le(1-a)\|v\|_{\rm TV}.
\tag{9}
\]

This argument uses no centrality of \(\nu\). Left translation by \(\sigma^{-1}\) preserves (1), since \(gE=H\) is replaced by \(gE=\sigma H\), and preserves total variation. Hence (9) extends to **every atom** \(\sigma\in S_n\).

The remaining task for the upper bound is to exhibit an explicit \(\Phi\) satisfying \(9/14\le\Phi(g)\le1\) **simultaneously for every nonidentity permutation in every degree**.

## 3. The explicit five-evaluation dual

Choose the five fixed rational parameters

\[
(q_1,q_2,q_3,q_4,q_5)
=\left(\frac12,\frac38,\frac14,\frac15,\frac16\right)
\tag{10}
\]

and the integer denominator and weight vector

\[
D=7\,840\,000\,000,
\]

\[
\begin{aligned}
(\beta_1,\beta_2,\beta_3,\beta_4,\beta_5)=(&
 1\,673\,869\,342\,439,\;-2\,703\,443\,680\,000,\\
&2\,219\,279\,598\,768,\;-1\,614\,169\,760\,000,\;
430\,736\,498\,793).
\end{aligned}
\tag{11}
\]

Define \(\alpha_i=\beta_i/D\) and \(\Phi\) by (8). All proof data are **literal rational integers**, not rounded solver output. Substitution gives the four exact contact identities

\[
\boxed{
\sum_i\alpha_i=\frac45,\quad
\Phi((2))=\Phi((3,3))=\frac9{14},\quad
\Phi((4))=1.}
\tag{12}
\]

The notation \((2),(3,3),(4)\) records the **nontrivial cycle lengths**, with arbitrarily many additional fixed points allowed. For a cycle of length \(\ell\), use \(U_q((\ell))=q^\ell+(1-q)^\ell\); for \((3,3)\), square the 3-cycle factor. The identities (12) reduce to fixed equalities of fractions and are checked independently by both programs.

**Lemma 2 (universal dual certificate).** For every nonidentity \(g\in S_n\), with **any integer \(n\ge2\)**,

\[
\boxed{\frac9{14}\le\Phi(g)\le1.}
\tag{13}
\]

*Proof, finite part.* Let \(M\) be the number of moved vertices. The nontrivial cycle lengths form a unique nonincreasing integer partition \(\lambda=(\lambda_1,\ldots,\lambda_s)\) of \(M\), with \(\lambda_j\ge2\). Every such partition occurs in every degree \(n\ge M\) by appending fixed points, and fixed points do not affect \(\Phi\).

For \(2\le M\le41\), an exact, exhaustive finite certificate verifies (13) for **all such partitions**. Here are the integer comparisons it performs. Write \(q_i=r_i/s_i\) in lowest terms, set \(S=\mathrm{lcm}(s_i)=120\), and define

\[
N_i(\lambda)=\prod_{\ell\in\lambda}
\bigl(r_i^\ell+(s_i-r_i)^\ell\bigr)\in\mathbb Z.
\tag{14}
\]

Since \(U_{q_i}(\lambda)=N_i(\lambda)/s_i^M\), put

\[
T(\lambda)=\sum_{i=1}^{5}\beta_i
\left(S^M-N_i(\lambda)(S/s_i)^M\right)\in\mathbb Z.
\tag{15}
\]

Then **exactly**, with no loss or approximation, (13) is equivalent to

\[
\boxed{
9D S^M\le14T(\lambda)\le14D S^M.}
\tag{16}
\]

The [primary integer checker](check_allrank_sharp_five_fourteenths.py) generates all integer partitions of each \(M=2,\ldots,41\) whose parts are at least two, by the recursion that appends parts no larger than the preceding part. This recursion is complete by induction on the remaining total and produces no duplicate partition. There are exactly

\[
\sum_{M=2}^{41}\bigl(p(M)-p(M-1)\bigr)
=p(41)-1=\boxed{44\,582}
\tag{17}
\]

cases, because removing a 1 is a bijection between partitions of \(M\) containing a 1 and partitions of \(M-1\). For **every** case it checks both integer inequalities (16) with arbitrary-precision integer arithmetic. It also checks the contact identities (12) and that the exact finite minimum and maximum are \(9/14\) and 1.

For independent verification, the [second checker](check_allrank_sharp_five_fourteenths_independent.py) does **not** import the first program. It reconstructs three of the five \(\alpha_i\) by solving the rational contact equations, uses a separate partition enumeration, and evaluates every \(\Phi(\lambda)\) by direct Fraction products rather than cleared-denominator arithmetic. It independently confirms the same 44,582 cases, the same weights, and the same extreme values. These are independently reproducible **finite integer/rational certificates**, with a stated complete enumeration and no floating-point comparisons or external solver premise. This closes every permutation with \(M\le41\).

*Proof, unbounded part.* For every \(0<q<1\), put \(\rho_q=q^2+(1-q)^2\). For each integer \(\ell\ge2\),

\[
q^\ell+(1-q)^\ell\le\rho_q^{\ell/2}.
\tag{18}
\]

Indeed, let \(x=q^2/\rho_q\) and \(y=(1-q)^2/\rho_q\), so \(x,y\ge0\), \(x+y=1\); since \(\ell/2\ge1\), one has \(x^{\ell/2}+y^{\ell/2}\le x+y=1\). Multiplying over all nontrivial cycles whose lengths sum to \(M\) proves

\[
0\le U_q(g)\le\rho_q^{M/2}.
\tag{19}
\]

The five values are

\[
(\rho_{q_i})=
\left(\frac12,\frac{17}{32},\frac58,\frac{17}{25},
\frac{13}{18}\right).
\]

The fixed rational weights (11) satisfy the **single exact rational inequality**

\[
\boxed{\sum_{i=1}^{5}\frac{|\beta_i|}{D}
\rho_{q_i}^{21}<\frac7{50}.}
\tag{20}
\]

Both checkers verify (20) by exact rational arithmetic, not by decimal approximation. For **every \(M\ge42\)**, (19)--(20) and \(\sum_i\alpha_i=4/5\) give

\[
\left|\Phi(g)-\frac45\right|
=\left|\sum_i\alpha_i U_{q_i}(g)\right|
\le\sum_i|\alpha_i|\rho_{q_i}^{21}
<\frac7{50}.
\]

Thus every such permutation satisfies the **stronger** interval

\[
\boxed{\frac{33}{50}<\Phi(g)<\frac{47}{50}.}
\tag{21}
\]

Since \(33/50>9/14\) and \(47/50<1\), this proves (13) also for every \(M\ge42\). The finite and unbounded parts cover **all nonidentity permutations in all degrees**. QED.

Now (9) applied with \(a=9/14\) proves

\[
C_n^{\rm all}\le1-\frac9{14}=\frac5{14}.
\tag{22}
\]

## 4. An explicit primal pair achieving 5/14

Fix \(n\ge6\). Let \(I,T,K,E\) be respectively the conjugacy classes of types

\[
I=1^n,\quad T=2\,1^{n-2},\quad
K=4\,1^{n-4},\quad E=3^2\,1^{n-6}.
\]

Denote by \(U_C\) uniform probability on a class \(C\). Set

\[
\boxed{
P=\frac5{14}U_I+\frac9{14}U_K,\qquad
Q=\frac67U_T+\frac17U_E.}
\tag{23}
\]

The four supports are disjoint, both laws are central and rational, and \(P(e)-Q(e)=5/14\).

**Lemma 3 (all-rank marginal identity).** The laws \(P\) and \(Q\) have **identical individual subset-image marginals in every rank**.

*Proof.* First verify the elementary polynomial identity

\[
5(1+z)^6+9(1+z)^2(1+z^4)
=12(1+z)^4(1+z^2)+2(1+z^3)^2.
\tag{24}
\]

Multiplying by \((1+z)^{n-6}\) and using (4) gives

\[
5Q_I(z)+9Q_K(z)=12Q_T(z)+2Q_E(z).
\tag{25}
\]

We check explicitly that the entire cycle polynomial determines **every subset-intersection orbital count**, not merely the invariant-subset counts. Let

\[
F_{k,j}(g)=\#\{S\subseteq[n]: |S|=k,\ |S\cap gS|=j\}.
\]

For the \(2\times2\) transfer matrix \(B(s,t)=\left(\begin{smallmatrix}1&s\\1&st\end{smallmatrix}\right)\), summation over binary cyclic words gives

\[
\sum_{k,j}F_{k,j}(g)s^kt^j
=\prod_{\ell\ge1}\mathrm{tr}(B(s,t)^\ell)^{m_\ell(g)}.
\tag{26}
\]

Let its formal characteristic roots be \(L_+=1+O(s)\) and \(L_-=O(s)\); then \(\mathrm{tr}(B^\ell)=L_+^\ell+L_-^\ell\), so (26) becomes the **linear transform**

\[
L_+^n Q_g(L_-/L_+).
\tag{27}
\]

Consequently equality (25) implies **for every \(k,j\)**

\[
5F_{k,j}(I)+9F_{k,j}(K)
=12F_{k,j}(T)+2F_{k,j}(E).
\tag{28}
\]

For central \(\mu\), the number \(\Pr_\mu(gS=H)\) is constant across all ordered pairs \((S,H)\) with the same intersection size \(j\), since simultaneous relabeling acts transitively on each such orbital. Summing these probabilities over an orbital gives \(\mathbb E_\mu F_{k,j}\); hence equality of all orbital expectations for two central laws implies equality of **every individual image marginal**. By (28), the two measures (23) have precisely this property. QED.

Because \(P\) and \(Q\) have disjoint support, \(\|P-Q\|_{\rm TV}=1\). For every sufficiently small **positive rational** \(\delta\), the perturbed law

\[
\nu_\delta=u+\delta(P-Q)
\]

is nonnegative (choose \(0<\delta\le[2n!\max_gQ(g)]^{-1}\)), has all the uniform marginals, and satisfies

\[
\|\nu_\delta-u\|_{\rm TV}=\delta,\qquad
\nu_\delta(e)-1/n!=\frac5{14}\delta.
\tag{29}
\]

Thus \(C_n^{\rm all}\ge5/14\). Together with (22), this proves **Theorem 1 for every \(n\ge6\)**, including exact sharpness. QED.

## 5. One middle subset rank suffices

We give the noncentral reduction underlying the second equality in (3). Let \(d=\lfloor n/2\rfloor\), and let \(V_r\) be the real permutation module of functions on \(r\)-subsets. For \(0\le r\le d\), the incidence map

\[
(W_{r,d}f)(S)=\sum_{\substack{E\subseteq S\\|E|=r}}f(E)
\tag{30}
\]

is **injective** whenever \(r\le d\le n-r\). To prove this, induct on \(r\): the case \(r=0\) is immediate. If \(W_{r,d}f=0\), subtract its values on \(T\cup\{a\}\) and \(T\cup\{b\}\), where \(a\ne b\) and \(|T|=d-1\) excludes both vertices. The difference is the \((r-1,d-1)\)-incidence transform of \(U\mapsto f(U\cup\{a\})-f(U\cup\{b\})\) on \(n-2\) vertices. The induction hypothesis forces it to vanish pointwise. Thus \(f\) is constant on all adjacent \(r\)-subsets, and the Johnson graph is connected; \(f\) is constant everywhere. Its incidence sum vanishes, so the constant is zero.

The map intertwines the group actions:

\[
\rho_d(g)W_{r,d}=W_{r,d}\rho_r(g).
\tag{31}
\]

If \(\sum_g(\nu(g)-u(g))\rho_d(g)=0\), right-multiply by \(W_{r,d}\) and invoke injectivity to obtain \(\sum_g(\nu(g)-u(g))\rho_r(g)=0\) at every \(r\le d\). By complementation, all ranks \(r>d\) are equivariantly identified with ranks \(n-r\le d\). Therefore **uniform middle-rank marginals imply uniform marginals at every rank for arbitrary \(\nu\)**, and the converse is immediate. The admissible laws in the two optimization problems are identical:

\[
C_{n,d}=C_n^{\rm all}=\frac5{14}\qquad(n\ge6).
\tag{32}
\]

## 6. Complete degree classification

Together with the sharp natural \(S_3\) action and \(S_4,S_5\) pair-action formulas already proved in [the parent permutation-action manuscript](../sharp-robust-permanent/paper.md), Theorem 1 also gives the **complete all-degree formula**

\[
\boxed{
C_n^{\rm all}=
\begin{cases}
0,&n=1,2,\\
1/3,&n=3,4,5,\\
5/14,&n\ge6.
\end{cases}}
\tag{33}
\]

For \(n\le2\) the uniform middle-rank constraints determine the uniform group law uniquely (and for \(S_1\) it is the only law). For \(n=3\) the middle-rank natural action has sharp coefficient \(1/3\); for \(n=4,5\) the previously certified two-subset action has coefficient \(1/3\). The new proof establishes **every degree \(n\ge6\)**. The complete formula makes no assumption that \(\nu\) is central.

## 7. Reproducibility and trust boundary

Two **independent, optimizer-free**, standard-library-only Python checkers are publicly available:

- [Integer checker](check_allrank_sharp_five_fourteenths.py): checks the exact five weights and contacts, **all** 44,582 inequalities (16) after clearing denominators, and the single strict rational tail inequality (20).
- [Independent Fraction checker](check_allrank_sharp_five_fourteenths_independent.py): reconstructs three weights by rational Gaussian elimination, independently generates every partition, checks all values with exact Fraction products, and verifies the tail bound separately.

Execute each from the repository root with ordinary Python 3:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_independent.py
~~~

Both checkers were downloaded from **pinned Git commit SHA URLs** into a fresh VPS directory and passed independently. The audit record in [VERIFICATION.md](VERIFICATION.md) lists source hashes, replay outputs and negative controls. The computer-assisted step is a **finite, exactly described mathematical assertion** with a complete enumerator and two independent rational implementations. The **unbounded** part of the proof is Lemma 2's explicit analytic tail argument, not an extrapolation from the 44,582 checked cases. The four-class primal and middle-rank equivalence are analytic identities proved in Sections 4--5.

This closes the previous \(5/14\) all-rank conjecture from [ALL_RANK_TRACE_KERNEL.md](ALL_RANK_TRACE_KERNEL.md). It does **not** solve the general exact finite-\((n,k)\) atom-modulus problem at arbitrary nonmiddle rank, characterize every extremizer, or prove historical first-discovery priority.


## 8. Extension to every faithful finite permutation group

The upper-bound argument uses only the fact that every nonidentity group element moves some vertices. It does **not** require the group to be the full symmetric group.

**Theorem 5 (universal sharp subgroup bound).** Let \(G\le S_n\) be an arbitrary finite subgroup, acting faithfully on \([n]\), and let \(u_G\) be its uniform probability law. Suppose a probability law \(\nu\) on \(G\) has **the same subset-image marginals as \(u_G\)** for every subset rank:

\[
\nu\{g\in G:gE=H\}
=u_G\{g\in G:gE=H\}
\quad\text{for all }E,H\subseteq[n]\text{ of equal size}.
\tag{34}
\]

No transitivity or homogeneity is assumed; in particular, the common values in (34) need **not** equal \(\binom nk^{-1}\). Then for **every** \(\sigma\in G\),

\[
\boxed{\left|\nu(\sigma)-\frac1{|G|}\right|
\le\frac5{14}\|\nu-u_G\|_{\rm TV}.}
\tag{35}
\]

The constant \(5/14\) is best possible **uniformly over all faithful permutation groups**, since equality occurs for \(G=S_n\) in every degree \(n\ge6\).

*Proof.* The signed measure \(v=\nu-u_G\) annihilates every individual indicator \(\mathbf1_{\{gE=H\}}\), hence the invariant-subset counts (5), hence the five \(U_{q_i}\) and \(\Phi\) of (8). The explicit global dual inequality (13) holds for every nonidentity permutation in \(S_n\), so it also holds after restriction to \(G\). Faithfulness ensures that the only element represented by the identity permutation is the group identity. Thus the range of \(\mathbf1_{\{g=e_G\}}+\Phi(g)\) has length at most \(5/14\), proving (35) at \(e_G\).

For an arbitrary \(\sigma\in G\), translate \(\nu\) on the left by \(\sigma^{-1}\). The group-uniform law \(u_G\) and its image marginals are invariant under that translation, so the translated measure still satisfies (34), and total variation is unchanged. The estimate at the identity becomes the estimate at \(\sigma\). Sharpness of the universal coefficient follows from the attaining \(S_n\) family (23). QED.

If faithfulness is dropped, different group elements can induce the same permutation, and the constant \(5/14\) is not generally valid: moving probability mass between two elements acting identically leaves every image marginal unchanged and can have atom/TV ratio 1.

## 9. Rigidity of every equality case

The two exact finite checkers establish **more** than merely the minimum and maximum: among all nonidentity permutations, the only points at which the constructed dual \(\Phi\) has either endpoint value are

\[
\begin{aligned}
\Phi(g)=1
&\quad\Longleftrightarrow\quad
g\text{ is a single 4-cycle, with all other points fixed},\\
\Phi(g)=9/14
&\quad\Longleftrightarrow\quad
g\text{ is a single transposition or a product of two disjoint 3-cycles}.
\end{aligned}
\tag{36}
\]

Indeed, the independent checker enumerates the **complete** lower-contact list \((2),(3,3)\) and upper-contact list \((4)\) for all 44,582 finite partitions, not only one attaining partition. The primary checker independently enforces the same contact classification by exact integer equalities. The strict tail interval (21) excludes all additional contacts with at least 42 moved vertices. Thus (36) is a rigorous global statement for all \(n\ge6\), not finite evidence about larger degrees.

**Theorem 6 (sharp-support rigidity and class-mass classification).** Fix \(n\ge6\). Let \(\nu\) be any law with the uniform all-rank subset-image marginals and let \(v=\nu-u\), \(\delta=\|v\|_{\rm TV}>0\). Suppose equality holds at the identity with **positive** atom deviation:

\[
v(e)=\frac5{14}\delta.
\tag{37}
\]

Then the positive and negative Jordan parts of \(v\) have **necessarily** the supports

\[
\operatorname{supp}v_+\subseteq I\cup K,\qquad
\operatorname{supp}v_-\subseteq T\cup E,
\tag{38}
\]

where \(I,K,T,E\) are the four conjugacy classes in Section 4, and their **total class masses are rigid**:

\[
\boxed{
\begin{aligned}
v_+(I)&=\frac5{14}\delta,&
v_+(K)&=\frac9{14}\delta,\\
v_-(T)&=\frac67\delta,&
v_-(E)&=\frac17\delta.
\end{aligned}}
\tag{39}
\]

In particular, if \(\nu\) is conjugation-invariant, its signed perturbation is **uniquely** of the form

\[
\boxed{v=\delta(P-Q)}
\tag{40}
\]

with \(P,Q\) exactly as in (23). Negative-atom equality has the sign-reversed Jordan pattern; equality at any other \(\sigma\) is obtained by left-translation. No claim is made that (39) forces **individual class densities** to be uniform when \(\nu\) is noncentral.

*Proof.* Let \(h(e)=1\), and \(h(g)=\Phi(g)\) for \(g\ne e\). In the chain

\[
v(e)=\int h\,dv
=\int h\,dv_+-\int h\,dv_-
\le 1\cdot\delta-\frac9{14}\delta=\frac5{14}\delta,
\]

equality forces \(v_+\) to be supported entirely on **upper contact points** of \(h\), and \(v_-\) entirely on **lower contact points**. The complete contact classification (36) gives (38).

Normalize the positive and negative Jordan parts by \(\delta\). Let \(x=v_+(I)/\delta\) and \(y=v_-(T)/\delta\). The normalized two measures have total class-mass distributions

\[
xI+(1-x)K,\qquad yT+(1-y)E.
\tag{41}
\]

The fixed-subset moments (5) vanish against \(v\), so the associated convex combinations of their cycle polynomials are **equal**. Divide this polynomial identity by the nonzero common factor \((1+z)^{n-6}\). The remaining four polynomials are

\[
(1+z)^6,\quad (1+z)^2(1+z^4),\quad
(1+z)^4(1+z^2),\quad (1+z^3)^2
\]

for \(I,K,T,E\), respectively. Comparing coefficients of \(z\) and \(z^2\) gives the two exact equations

\[
6x+2(1-x)=4y,\qquad
15x+1(1-x)=7y.
\tag{42}
\]

The unique solution is \(x=5/14\), \(y=6/7\); the remaining masses follow from normalization. This proves (39) without any centrality assumption on \(\nu\).

If \(\nu\) is central, its restriction to each conjugacy class is constant, so the class totals in (39) determine \(v\) completely and yield (40). Sign reversal and left translation give the other cases. QED.

A partial converse is immediate and sharp: if a signed marginal-preserving perturbation has its positive part on the upper-contact set and its negative part on the lower-contact set, then every inequality in the displayed oscillation bound is an equality. Thus **the support criterion is also sufficient**, subject to the stated marginal equalities and nonnegativity of the resulting probability law.

## 10. Weaker invariant-subset moment constraints: precise scope

The dual upper bound uses only the \(n+1\) **aggregate** constraints

\[
\mathbb E_\nu A_r(g)=\mathbb E_u A_r(g)=1,
\qquad 0\le r\le n.
\tag{43}
\]

By complementarity \(A_r(g)=A_{n-r}(g)\) and the tautological \(A_0=A_n=1\), only the \(\lfloor n/2\rfloor\) nontrivial constraints matter. The same four-class probability perturbation (23) obeys these aggregate equations. Therefore:

**Corollary 7 (a still weaker sharp identity-atom theorem).** For every \(n\ge6\), the **identity-atom** inequality

\[
\boxed{\left|\nu(e)-\frac1{n!}\right|
\le\frac5{14}\|\nu-u\|_{\rm TV}}
\tag{44}
\]

is sharp even if (43), rather than full subset-image marginal uniformity, is the **only** hypothesis.

However, (44) cannot be promoted to every other atom under (43) alone. Indeed, for two distinct **conjugate nonidentity** permutations \(\sigma,\tau\), the perturbation \(v=\delta(\mathbf1_{\{\sigma\}}-\mathbf1_{\{\tau\}})\) (with \(\delta>0\) sufficiently small) annihilates every central function \(A_r\), but has atom/TV ratio **1 at \(\sigma\)**. Thus the full image-marginal hypothesis is essential for the every-atom assertions of Theorems 1 and 5. This distinction is part of the precise theorem scope, not an unstated assumption.
