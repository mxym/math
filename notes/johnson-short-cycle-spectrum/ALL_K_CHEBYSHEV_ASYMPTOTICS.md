# Sharp first-order atom/total-variation asymptotics for every fixed Johnson rank

**Research manuscript, 8 October 2026; complementary proof.** A parallel task has independently completed the same all-fixed-rank theorem as **Theorem 25, Section 24** of the [permutation-action manuscript](../sharp-robust-permanent/paper.md), with an earlier public commit. The present manuscript retains a **separate proof** using the short-cycle formal transfer expansion, a rational-coefficient dual interpolation with deliberate strict slack, explicit Lobatto weights, and an eventual strict-rank corollary. The shared theorem asserts that every fixed subset rank has the exact leading atom-modulus defect \(2k^2/n\). This is a statement for each fixed \(k\), as \(n\to\infty\), **not** a uniform estimate when \(k\) grows with \(n\). It builds on the exact Johnson transfer identity and rational orbital LP in the [companion note](README.md). No external peer-review, Lean proof or historical priority is claimed.

## 1. Definitions and main result

Let \(G=S_n\) act naturally on the set \(\Omega_{n,k}=\binom{[n]}k\). Let \(u_n\) be the uniform law on \(G\). The *sharp atom-to-total-variation modulus* \(C_{n,k}\) is the smallest constant such that every law \(\nu\) on \(G\) with

\[
\nu\{g:gE=H\}=\binom nk^{-1}\quad
(E,H\in\Omega_{n,k})
\tag{1}
\]

satisfies, for every \(\sigma\in S_n\),

\[
\left|\nu(\sigma)-\frac1{n!}\right|
\le C_{n,k}\|\nu-u_n\|_{\mathrm{TV}}.
\tag{2}
\]

We use total variation of a signed mass-zero law \(v\) in the convention \(\|v\|_{\rm TV}=\sum_{g:v(g)>0}v(g)=\frac12\sum_g|v(g)|\).

**Theorem 1 (sharp all-fixed-rank Johnson asymptotics).** For **every fixed integer \(k\ge1\)**,

\[
\boxed{\displaystyle
C_{n,k}=1-\frac{2k^2}{n}+O_k(n^{-2})\qquad(n\longrightarrow\infty).}
\tag{3}
\]

In particular,

\[
\boxed{\lim_{n\to\infty}n(1-C_{n,k})=2k^2.}
\tag{4}
\]

Both halves of (3) are proved, independently of finite computations:

- There is, for each fixed \(k\), a rational-coefficient conjugacy-invariant orbital **dual** function, valid for **every** permutation \(g\in S_n\) and all sufficiently large \(n\), whose oscillation is at most \(1-2k^2/n+O_k(n^{-2})\).
- For **every sufficiently large integer \(n\)**, there are two explicitly specified, positive, **rational**, conjugacy-invariant probability laws \(P_n,Q_n\), supported on \(k+2\) genuine conjugacy classes, with **exactly identical full \(k\)-subset image marginals** and identity-atom gap \(1-2k^2/n+O_k(n^{-2})\). An actual positive total-variation perturbation attains this gap.

The special \(k=1,2,3\) constants \(2,8,18\) were previously established in the predecessor manuscript. The companion [rank-five result](ASYMPTOTIC_RANK_FIVE.md) gives a separate explicit and stronger quantitative upper bound in the case \(k=4\). The result for the previously conjectural range \(k\ge4\) is also established, independently and earlier, by the concurrent Theorem 25. The two public proofs should be treated as **complementary verifications**, not competing priority claims.

## 2. The orbital primal-dual principle

For \(g\in S_n\) and \(0\le j\le k\), define

\[
F_j(g)=\#\{E\in\Omega_{n,k}:|E\cap gE|=j\}.
\tag{5}
\]

Each \(F_j\) is a sum of individual \(k\)-set image indicator functions. It is central (constant on each conjugacy class). There are \(k+1\) orbitals in \(\Omega_{n,k}\times\Omega_{n,k}\) when \(n\ge2k\), indexed by \(|E\cap H|=j\); the cardinality of orbital \(j\) is \(\binom nk\binom kj\binom{n-k}{k-j}\).

**Lemma 2 (primal and dual sufficiency).** For \(n\ge2k\):

(a) If \(h(g)=\mathbf1_{\{g=e\}}+\sum_{j=0}^{k-1}\lambda_j F_j(g)\) has global oscillation at most \(L\), then \(C_{n,k}\le L\).

(b) If two conjugation-invariant probability laws \(P,Q\) have equal \(\mathbb EF_j\) for \(j=0,\ldots,k\), are disjointly supported and \(P(e)-Q(e)=\gamma>0\), then \(C_{n,k}\ge\gamma\).

*Proof.* For any \(\nu\) satisfying (1), the signed law \(v=\nu-u_n\) has mass zero and annihilates every \(F_j\), so \(\int h\,dv=v(e)\). The Jordan positive and negative parts of \(v\) both have mass \(\|v\|_{\rm TV}\), whence \(|v(e)|\le\operatorname{osc}(h)\|v\|_{\rm TV}\). Left translation of \(\nu\) preserves the uniform image marginals and moves any specified \(\sigma\) to the identity; this proves (a).

For a central law \(\mu\), the probability of \(gE=H\) depends only on \(j=|E\cap H|\) and equals \(\mathbb E_\mu F_j\) divided by the corresponding orbital cardinality. Thus equality of every \(F_j\)-moment for \(P,Q\) implies equality of **every** image marginal. Their difference annihilates all these indicators. For small positive rational \(\delta\), \(\nu=u_n+\delta(P-Q)\) is a nonnegative probability law, has the uniform marginals, and by disjoint support has \(\|\nu-u_n\|_{\rm TV}=\delta\) and atom excess \(\nu(e)-u_n(e)=\delta\gamma\). This proves (b). QED.

The proof only needs this elementary form of the general orbital LP; no numerical optimizer or LP duality is assumed.

## 3. Uniform first-order expansion of *all* intersection orbitals

Write \(m_\ell(g)\) for the number of \(\ell\)-cycles in \(g\), and put

\[
a=m_1(g)/n,\qquad b=m_2(g)/n.
\tag{6}
\]

Every permutation satisfies \(0\le a\le1\) and \(0\le b\le(1-a)/2\). For a **nonidentity** permutation, \(a\le1-2/n\).

Let \(\mathcal B_{j,k}(a)=\binom kj a^j(1-a)^{k-j}\) be the Bernstein basis.

**Lemma 3 (uniform first- and second-homogeneous orbital terms).** For each fixed \(k\ge2\), uniformly over every \(g\in S_n\) and every \(j=0,\ldots,k\),

\[
\frac{k!}{n^k}F_j(g)
=\mathcal B_{j,k}(a)+\frac1nD_{j,k}(a,b)
+O_k(n^{-2}),\tag{7}
\]

where the **explicit rational polynomial** \(D_{j,k}\) is

\[
\begin{aligned}
L(a,t)&=1-a+at,\\
Q(a,b,t)&=t-\frac32
-\frac a2(t^2+2t-3)+b(t-1)^2,\\
D_{j,k}(a,b)&=k(k-1)[t^j]L(a,t)^{k-2}Q(a,b,t).
\end{aligned}\tag{8}
\]

The implied constant in (7) depends **only on \(k\)**. In particular the order \(1/n\) term involves **only** the 1- and 2-cycle counts, for arbitrary fixed \(k\).

*Proof.* The transfer-matrix identity from the companion note (also proved directly by enumerating cyclic binary words) is

\[
\sum_{j=0}^kF_j(g)t^j
=[s^k]L_+(s,t)^n
\prod_{\ell=1}^k
\left(1+\bigl(L_-(s,t)/L_+(s,t)\bigr)^\ell\right)^{m_\ell(g)},
\tag{9}
\]

where \(L_\pm\) are the formal roots of \(X^2-(1+st)X+s(t-1)=0\), characterized by \(L_+=1+O(s)\) and \(L_-=O(s)\). The exact initial expansions are

\[
\begin{aligned}
L_+&=1+s+(t-1)s^2+O(s^3),\\
\log L_+&=s+(t-\tfrac32)s^2+O(s^3),\\
z:=L_-/L_+&=(t-1)s-2(t-1)s^2+O(s^3),\\
\log(1+z)&=(t-1)s-\tfrac12(t^2+2t-3)s^2+O(s^3),\\
\log(1+z^2)&=(t-1)^2s^2+O(s^3).
\end{aligned}\tag{10}
\]

Consequently, the formal logarithm of the generating function on the right of (9), truncated at \(s^k\), equals

\[
U_1s+U_2s^2+\cdots+U_ks^k,\quad
U_1=nL(a,t),\quad U_2=nQ(a,b,t).
\tag{11}
\]

For \(r\ge3\), \(U_r\) is a rational polynomial in \(t\), **linear** in \(n,m_1,\ldots,m_r\) with \(k\)-dependent coefficients. Each coefficient is bounded by a constant times \(n\), uniformly in the conjugacy class (since \(m_r\le n\)). In the coefficient of \(s^k\) of the exponential, the unique contribution with \(k\) factors of the \(U_r\) is \(U_1^k/k!\), and the unique contribution with \(k-1\) factors is \(U_1^{k-2}U_2/(k-2)!\). Every other contribution contains at most \(k-2\) factors and is \(O_k(n^{k-2})\) coefficientwise in \(t\). Substituting (11) and multiplying by \(k!/n^k\) gives (7)--(8). QED.

For \(k=1\), \(F_0(g)=n-m_1(g)=n(1-a)\) exactly; we treat that rank separately where necessary.

## 4. Chebyshev dual with a rigorous global envelope

Let \(T_k\) be the first-kind Chebyshev polynomial, \(T_k(\cos\theta)=\cos(k\theta)\). Define

\[
H_k(a)=\frac{1-T_k(2a-1)}2.
\tag{12}
\]

Then \(H_k\in\mathbb Q[a]\) has degree \(k\), \(0\le H_k(a)\le1\) for \(a\in[0,1]\), \(H_k(1)=0\), and

\[
H_k'(1)=-k^2.
\tag{13}
\]

For \(j=0,\ldots,k\) put

\[
a_j=\frac{1+\cos(j\pi/k)}2;
\quad 1=a_0>a_1>\cdots>a_k=0,
\qquad
H_k(a_j)=\frac{1-(-1)^j}{2}.
\tag{14}
\]

All **interior** extrema \(a_1,\ldots,a_{k-1}\) are nondegenerate quadratic extrema. The endpoints are handled separately.

Write \(H_k\) in the degree-\(k\) Bernstein basis:

\[
H_k(a)=\sum_{j=0}^{k}h_j\mathcal B_{j,k}(a),
\qquad h_j\in\mathbb Q,\quad h_k=0.
\tag{15}
\]

For \(k\ge2\) form the explicit polynomial

\[
J_0(a,b)=\sum_{j=0}^{k-1}h_jD_{j,k}(a,b),
\qquad
J_0(1,0)=0.
\tag{16}
\]

The last equality follows from \(L(1,t)=t\) and \(Q(1,0,t)=-t^2/2\): for \(j<k\), the coefficient of \(t^j\) in \(L^{k-2}Q=-t^k/2\) is zero.

**Lemma 4 (a rational universal correction polynomial).** There exists a polynomial \(D\in\mathbb Q[a]\) of degree at most \(k\), with \(D(1)=0\), for which

\[
\begin{array}{ll}
J(a_j,\tfrac12(1-a_j)\theta)\le-\tfrac12,
&j\ \text{odd},\\
J(a_j,\tfrac12(1-a_j)\theta)\ge 2k^2+\tfrac12,
&j\ \text{even},
\end{array}
\quad (1\le j\le k,\ 0\le\theta\le1),\tag{17}
\]

where \(J(a,b)=J_0(a,b)+D(a)\). In addition \(J(1,0)=0\).

*Proof.* Since \(J_0\) is affine in \(b\), its maximum and minimum as \(\theta\in[0,1]\) varies occur at the endpoints; both are finite real algebraic numbers at the algebraic nodes \(a_j\). Prescribe the values of a real polynomial \(D_*\), of degree at most \(k\), at the \(k+1\) distinct nodes \(a_0,\ldots,a_k\) by

\[
D_*(a_0)=0,\qquad
D_*(a_j)=
\begin{cases}
-1-\max_{0\le\theta\le1}J_0(a_j,(1-a_j)\theta/2),&j\text{ odd},\\
2k^2+1-\min_{0\le\theta\le1}J_0(a_j,(1-a_j)\theta/2),&j\text{ even}.
\end{cases}
\tag{18}
\]

Lagrange interpolation supplies this unique \(D_*\). Expand \(D_*\) in the Bernstein basis of degree \(k\). Its top coefficient, equal to \(D_*(1)\), is zero. Approximate all remaining real coefficients by rationals within \(1/2\), leaving the top coefficient zero. Since the Bernstein basis elements are nonnegative and sum to 1 on \([0,1]\), the resulting rational \(D\) obeys \(\sup_{[0,1]}|D-D_*|<1/2\) and \(D(1)=0\). The slack of 1 in (18) now proves (17). The final identity follows from (16). QED.

Write \(D(a)=\sum_{j=0}^{k-1}d_j\mathcal B_{j,k}(a)\) with \(d_j\in\mathbb Q\). Define the **rational dual**

\[
\boxed{\displaystyle
h_{n,k}(g)=\mathbf1_{\{g=e\}}+
\frac{k!}{n^k}\sum_{j=0}^{k-1}
\left(h_j+\frac{d_j}{n}\right)F_j(g).}
\tag{19}
\]

At \(g=e\), all \(F_j\) with \(j<k\) vanish, so \(h_{n,k}(e)=1\). For every nonidentity \(g\), Lemma 3 yields the **uniform expansion**

\[
h_{n,k}(g)=H_k(a)+\frac{J(a,b)}n+O_k(n^{-2})
\quad(0\le a\le1-2/n,\ \ 0\le b\le(1-a)/2).
\tag{20}
\]

**Lemma 5 (global dual envelope).** For each fixed \(k\ge2\), there exists \(C_k<\infty\) and \(n_k\) such that for all \(n\ge n_k\) and all \(g\ne e\),

\[
\frac{2k^2}{n}-\frac{C_k}{n^2}
\le h_{n,k}(g)
\le1+\frac{C_k}{n^2}.
\tag{21}
\]

*Proof.* For \(a<1\), parameterize \(b=\theta(1-a)/2\), \(0\le\theta\le1\). The function \(\widetilde J(a,\theta)=J(a,\theta(1-a)/2)\) is polynomial in its arguments, hence uniformly bounded and uniformly Lipschitz in \(a\) on the compact square.

At any **interior maximum** \(a_j\) (odd \(j\)), the nondegenerate Chebyshev extremum gives, in a small fixed neighborhood, \(H_k(a)\le1-c_j(a-a_j)^2\) for some \(c_j>0\). By (17), \(\widetilde J(a,\theta)\le-1/2+L_k|a-a_j|\). Writing \(v=|a-a_j|\) and completing the square,

\[
H_k(a)+\widetilde J(a,\theta)/n
\le1-c_jv^2+\frac{L_kv}{n}
\le1+\frac{L_k^2}{4c_jn^2}.
\tag{22}
\]

At any **interior minimum** \(a_j\) (even \(j\)), one has \(H_k(a)\ge c_j(a-a_j)^2\) and \(\widetilde J(a,\theta)\ge2k^2+1/2-L_k|a-a_j|\). Completing the square similarly gives

\[
H_k(a)+\widetilde J(a,\theta)/n
\ge\frac{2k^2}{n}-\frac{L_k^2}{4c_jn^2}.
\tag{23}
\]

Near an interior minimum the upper bound is automatic, since \(H_k\) stays strictly below 1; near an interior maximum the lower bound is automatic, since \(H_k\) stays strictly above 0. At the **left endpoint** \(a_k=0\), (17) and continuity imply that on a sufficiently small neighborhood \(\widetilde J\le-1/4\) if \(H_k(0)=1\), and \(\widetilde J\ge2k^2+1/4\) if \(H_k(0)=0\). Together with \(0\le H_k\le1\), these yield the corresponding desired bound directly. The opposite bound is automatic there.

At the **right endpoint** \(a_0=1\), write \(s=1-a\). A nonidentity permutation has \(s\ge2/n\). The Chebyshev derivative and bounded second derivative give, for small \(s\),

\[
H_k(1-s)=k^2s+O_k(s^2).
\]

Since \(J(1,0)=0\) and \(b\le s/2\), we also have \(|J(a,b)|\le C'_ks\). Thus, for some \(C''_k\),

\[
H_k(a)+J(a,b)/n
\ge k^2s-C''_ks^2-C''_ks/n.
\tag{24}
\]

Choose the right-endpoint neighborhood small enough that the right side of (24) is increasing in \(s\) for all sufficiently large \(n\). Its minimum on \(2/n\le s\le\varepsilon_k\) is then at \(s=2/n\), where it equals \(2k^2/n-O_k(n^{-2})\). The upper bound is automatic in this neighborhood because \(H_k\) is bounded strictly away from 1 there for sufficiently small \(\varepsilon_k\).

On the **compact complement** of these neighborhoods of all the Chebyshev extrema and endpoints, \(H_k\) is separated from both 0 and 1, while \(J\) is bounded. Consequently the required inequalities follow there with room to spare for large \(n\). Finally, add the uniform \(O_k(n^{-2})\) remainder in (20), and take the largest of the finitely many constants. This proves (21). QED.

Now \(h_{n,k}(e)=1\) lies in the same global interval for \(n\) sufficiently large, so Lemma 2(a) and (21) give

\[
C_{n,k}\le1-\frac{2k^2}{n}+O_k(n^{-2}).
\tag{25}
\]

For \(k=1\), the elementary rational dual \(h_{n,1}(g)=\mathbf1_{\{g=e\}}+F_0(g)/n\) is 1 at the identity and lies in \([2/n,1]\) on all nonidentity permutations (they move at least two vertices). Hence \(C_{n,1}\le1-2/n\), the same desired bound with zero error.

## 5. Exact rational primal measures for every sufficiently large degree

Let the \(k\) **nonidentity Chebyshev--Lobatto nodes** \(a_j\), \(1\le j\le k\), be as in (14). For all sufficiently large integers \(n\), put

\[
x_{j,n}=\lfloor na_j\rfloor
\]

and let \(K_{j,n}\) denote the conjugacy class consisting of **one** cycle of length \(n-x_{j,n}\) together with \(x_{j,n}\) fixed points. The long cycle has length at least \(k+1\), and the \(k\) classes are distinct for all large \(n\), since \(a_j<1\) and the \(a_j\) are distinct. Write \(I_n\) for the identity class and \(T_n\) for the class of transpositions. All \(k+2\) classes are distinct.

Let \(U_C\) be the *uniform measure on a conjugacy class \(C\)*. Define the normalized truncated orbital vector

\[
v_n(C)=\binom nk^{-1}(F_0(C),F_1(C),\ldots,F_{k-1}(C))
\in\mathbb Q^k.
\tag{26}
\]

For each \(n\), seek **exact rational weights** \(w_{j,n}\) in the \(k\times k\) system

\[
\boxed{\displaystyle
\sum_{\substack{1\le j\le k\\j\ \mathrm{odd}}}
w_{j,n}\bigl(v_n(K_{j,n})-v_n(I_n)\bigr)
-\sum_{\substack{1\le j\le k\\j\ \mathrm{even}}}
w_{j,n}\bigl(v_n(K_{j,n})-v_n(T_n)\bigr)
=n\bigl(v_n(T_n)-v_n(I_n)\bigr).}
\tag{27}
\]

We now prove that for **every sufficiently large integer \(n\)** the matrix is invertible and the exact rational solution has \(w_{j,n}>0\).

**Lemma 6 (positive Lobatto derivative quadrature).** For \(j=1,\ldots,k\) let

\[
\delta_j=
\begin{cases}
1,&1\le j<k,\\
1/2,&j=k,
\end{cases}
\qquad
\gamma_j=\frac{8\delta_j}{1-\cos(j\pi/k)}>0.
\tag{28}
\]

For **every real polynomial** \(f\) of degree at most \(k\),

\[
\boxed{\displaystyle
-2f'(1)=\sum_{j=1}^k(-1)^{j+1}
\gamma_j\bigl(f(a_j)-f(1)\bigr).}
\tag{29}
\]

Furthermore,

\[
\sum_{\substack{1\le j\le k\\j\ {\rm odd}}}\gamma_j=2k^2.
\tag{30}
\]

*Proof.* The Chebyshev--Lobatto nodes \(z_j=2a_j-1=\cos(j\pi/k)\), \(0\le j\le k\), are the roots of \((z^2-1)U_{k-1}(z)\), with \(U_{k-1}\) the second-kind Chebyshev polynomial. Differentiating this product at the roots, using \(U_{k-1}(\cos\theta)=\sin(k\theta)/\sin\theta\), gives barycentric interpolation weights proportional to \((-1)^j\delta_j\), where \(\delta_0=\delta_k=1/2\) and \(\delta_j=1\) for interior nodes. If \(\ell_j(a)\) is the Lagrange basis for the nodes \(a_0,\ldots,a_k\), its derivative at \(a_0=1\) is

\[
\ell'_j(1)=\frac{(-1)^j\delta_j}
{\delta_0(1-a_j)}
=\frac{4(-1)^j\delta_j}{1-\cos(j\pi/k)}
\quad(j\ge1).
\]

Differentiate the Lagrange interpolation formula for \(f\), then use \(\sum_{j=0}^k\ell'_j(1)=0\) to replace \(f(a_j)\) by \(f(a_j)-f(1)\). Multiplication by \(-2\) gives (29). Apply (29) to \(f=H_k\): since \(H_k(1)=0\), \(H_k(a_j)=1\) on odd \(j\) and 0 on even \(j\), and \(H'_k(1)=-k^2\), we obtain (30). QED.

**Lemma 7 (eventual rational positivity and exact moment matching).** For each fixed \(k\ge1\), system (27) is uniquely solvable for all sufficiently large \(n\). Its solution is rational and satisfies

\[
w_{j,n}=\gamma_j+O_k(n^{-1})>0.
\tag{31}
\]

*Proof.* For every \(g\) with fixed-point fraction \(a\), the normalized orbital counts satisfy the **uniform Bernstein approximation**

\[
\frac{F_j(g)}{\binom nk}=\mathcal B_{j,k}(a)+O_k(n^{-1}),
\tag{32}
\]

because the number of fixed vertices in a uniformly chosen \(k\)-set is hypergeometric and its difference from \(|E\cap gE|\) is a moved image-edge collision of probability \(O_k(1/n)\); the hypergeometric/binomial coupling costs \(O_k(1/n)\). Alternatively (32) follows immediately from Lemma 3 and \(\binom nk=n^k/k!\,(1+O_k(n^{-1}))\). For \(k=1\) it is exact.

Thus \(v_n(K_{j,n})\to(\mathcal B_{0,k}(a_j),\ldots,\mathcal B_{k-1,k}(a_j))\), while \(v_n(I_n)\) and \(v_n(T_n)\) both tend to the truncated Bernstein vector at \(a_0=1\). These limits converge at rate \(O_k(n^{-1})\).

A transposition maps a \(k\)-set to one with intersection \(k-1\) exactly when the set contains **exactly one** of the two transposed vertices. This has probability

\[
p_{n,k}
=\frac{2\binom{n-2}{k-1}}{\binom nk}
=\frac{2k(n-k)}{n(n-1)}.
\tag{33}
\]

Every other \(k\)-set is fixed, so, on adding the omitted last coordinate of the probability vectors,

\[
n\bigl(v_n(T_n)-v_n(I_n)\bigr)
\longrightarrow2k(e_{k-1}-e_k).
\tag{34}
\]

For any polynomial \(f\) of degree at most \(k\), write \(f(a)=\sum_{j=0}^k c_j\mathcal B_{j,k}(a)\). The linear functional represented by (34) on \(f\) is \(2k(c_{k-1}-c_k)=-2f'(1)\), since \(f'(1)=k(c_k-c_{k-1})\).

The limiting matrix of (27), tested against such polynomials, maps \(w\) to
\(\sum_{j\ {\rm odd}}w_j(f(a_j)-f(1))-
\sum_{j\ {\rm even}}w_j(f(a_j)-f(1))\).
This \(k\times k\) matrix is nonsingular: if a polynomial \(f\) of degree at most \(k\) with \(f(1)=0\) annihilates all its \(k\) columns, then \(f(a_j)=0\) for all \(1\le j\le k\); it has \(k+1\) distinct roots and is zero. The Bernstein coefficient pairing is nondegenerate, so this proves full rank.

By Lemma 6, the unique limiting solution of (27) is precisely the strictly positive vector \((\gamma_1,\ldots,\gamma_k)\). Convergence of matrices and right sides at order \(O_k(n^{-1})\), together with invertibility of their limit, implies (31) by the elementary continuity of matrix inversion. For each **integer** \(n\), however, the entries of (27) are rational (the classes are specified by integer cycle counts and \(F_j\) are integers); therefore its *actual*, not approximate, unique solution has rational coordinates. QED.

For \(n\) sufficiently large, define the central probability laws

\[
\begin{aligned}
P_n&=
\left(1-\frac1n\sum_{j\ {\rm odd}}w_{j,n}\right)U_{I_n}
+\sum_{j\ {\rm odd}}\frac{w_{j,n}}n\,U_{K_{j,n}},\\
Q_n&=
\left(1-\frac1n\sum_{j\ {\rm even}}w_{j,n}\right)U_{T_n}
+\sum_{j\ {\rm even}}\frac{w_{j,n}}n\,U_{K_{j,n}}.
\end{aligned}
\tag{35}
\]

By (31) all coefficients are positive and rational for all sufficiently large \(n\), and each side has total mass 1. All supports are pairwise disjoint. Equation (27) is **exactly equivalent** to

\[
\mathbb E_{P_n}F_j=\mathbb E_{Q_n}F_j,
\quad j=0,\ldots,k-1.
\tag{36}
\]

The remaining \(F_k\)-moment also agrees because \(\sum_{j=0}^kF_j(g)=\binom nk\) for every \(g\). By centrality, these \(k+1\) moment equalities imply equality of **every** image marginal in (1), not merely leading-order agreement.

Therefore Lemma 2(b) gives the all-large-degree sharp **lower** bound

\[
\begin{aligned}
C_{n,k}&\ge P_n(e)-Q_n(e)\\
&=1-\frac1n\sum_{j\ {\rm odd}}w_{j,n}\\
&=1-\frac1n\sum_{j\ {\rm odd}}\gamma_j+O_k(n^{-2})\\
&=\boxed{1-\frac{2k^2}{n}+O_k(n^{-2})},
\end{aligned}
\tag{37}
\]

where the \(k^2\) identity uses Lemma 6. The associated total-variation extremizers are *genuine* laws \(u_n+\delta(P_n-Q_n)\), for every sufficiently small positive rational \(\delta\). No optimization-derived positivity or approximate marginal constraint enters this conclusion.

## 6. Completion and independent replication

The universal dual bound (25) and the exact rational primal lower bound (37) match to order \(1/n\). Thus (3)--(4) follow for every fixed \(k\ge2\). The rank-one dual gives the same upper bound at \(k=1\), while the universal primal construction includes \(k=1\) with \(\gamma_1=2\). **Theorem 1 is proved for every fixed \(k\ge1\).** QED.

**Corollary 8 (eventual strict Johnson-rank separation).** For every **fixed pair** of distinct positive integers \(1\le k<\ell\),

\[
\boxed{\displaystyle
C_{n,k}-C_{n,\ell}
=\frac{2(\ell^2-k^2)}{n}+O_{k,\ell}(n^{-2})>0
\quad\text{for all sufficiently large }n.}
\tag{38}
\]

In particular,

\[
\lim_{n\to\infty}n(C_{n,k}-C_{n,k+1})=4k+2.
\tag{39}
\]

*Proof.* Apply Theorem 1 separately at the two fixed ranks and subtract the resulting estimates. The leading coefficient \(2(\ell^2-k^2)>0\) dominates the \(O_{k,\ell}(n^{-2})\) error once \(n\) is sufficiently large. For \(\ell=k+1\), simplify \(2((k+1)^2-k^2)=4k+2\). QED.

This **eventually upgrades the non-strict all-degree hierarchy** from the companion [Theorem E](README.md#6-a-universal-hierarchy-under-increasing-subset-rank) to a strict hierarchy between any two fixed subset ranks. It is not an assertion of uniform strictness at every finite degree or at ranks proportional to \(n\).

**Executable regression material** (from the repository root):

~~~sh
# All-k short-cycle transfer check, pure stdlib integers:
python3 notes/johnson-short-cycle-spectrum/transfer.py

# All-rank rational primal/marginal regression, k=1,...,6, n=100,300,1000:
python3 notes/johnson-short-cycle-spectrum/check_all_k_asymptotic_primal.py

# Separate finite sharp optima k=4, n=11,...,50:
python3 notes/johnson-short-cycle-spectrum/check_k4.py
python3 notes/johnson-short-cycle-spectrum/check_k4_26_50.py

# Separate symbolic k=4 dual replay (optional SymPy):
python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_algebra.py
~~~

The all-rank primal script has **18 literal rational support tests**: at each of \(k=1,\ldots,6\) it solves a fresh exact small rational moment system in three integer degrees and checks strict positivity and **every** corresponding orbital moment equality, rather than trusting a floating-point optimizer. Those finite tests do **not** purport to prove eventual positivity for arbitrary \(k\) or infinite \(n\); Lemmas 6--7 give that proof. The exact transfer check enumerates literal subset images for 1,329 small cases and is likewise supplemental to Lemma 3.

**Prior work and precise new contribution.** The orbital primal-dual framework, exact \(k=1,2,3\) coefficients/asymptotics, the general uniform Bernstein limit, and the proposed coefficient \(2k^2\) appeared in the predecessor [permutation manuscript, Sections 18--23](../sharp-robust-permanent/paper.md); the latter was explicitly marked conjectural for \(k\ge4\). The companion [rank-five asymptotic proof](ASYMPTOTIC_RANK_FIVE.md) first established \(k=4\) separately by an explicit dual polynomial and a six-class positive rational primal. The **specific contribution of this independently derived proof** is a transfer-matrix derivation of the second-homogeneous orbital expansion, a fixed **rational-coefficient** correction obtained by strict-slack interpolation (rather than a necessarily algebraic interpolation polynomial), explicit Lobatto-derivative weights, and an eventual strict-rank gap corollary. The concurrent Theorem 25 proves the same principal two-sided asymptotic statement with a different, hypergeometric-based correction formula. No world-first, mathematical priority, independent human review or machine formalization is claimed. Determining exact finite-degree formulas at all \(k\), tracking \(k\) as \(n\) grows, and obtaining bounds uniform in \(k\) remain separate problems.
