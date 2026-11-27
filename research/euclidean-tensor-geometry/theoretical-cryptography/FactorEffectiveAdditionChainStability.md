# Effective dyadic stability of addition-chain lengths

**Result.** There is a terminating algorithm to decide whether an integer's optimal addition-chain length increases by exactly one at every successive doubling. The algorithm also computes the first doubling where this behavior stabilizes and the stable normalized length, for both ordinary and star chains. The proof gives a uniform explicit bound on the first stabilization index and a finite reduction to integer linear feasibility.

This answers the effective stability question posed explicitly in the introduction of [Harry Altman, *Internal structure of addition chains: Well-ordering*, TCS 721 (2018), 54–69](https://doi.org/10.1016/j.tcs.2017.12.002) ([open preprint](https://arxiv.org/abs/1409.1627)). Altman's stabilization theorem establishes existence, not an algorithm for deciding ordinary addition-chain stability. Hansen's derivative chains and [Neill Clift's encoding of small-step chains](https://additionchains.com/FourSmallStep.html) provide prior examples of compressing the doubling runs; the new use here is a normalization certificate for arbitrary carries with a fixed, bounded number of terms. It applies to every defect level and to all doubling indices at once. It does not establish the much sharper proposed zero-tail threshold in [Clift's *Doubling and Trailing Zeros*](https://additionchains.com/DoublingConjecture.html), and it does **not** solve the Scholz–Brauer inequality.

## 1. Statements

Write \(\ell(n)\) for the shortest length of a strictly increasing addition chain starting at 1 and ending at \(n\) (each new term is the sum of two earlier terms, possibly equal), and \(\ell^*(n)\) if each addition must use the immediately preceding term. Use either choice throughout. Put
\[
\lambda=\lfloor\log_2 n\rfloor,\quad v=\operatorname{popcount}(n),\quad
b_j=\ell(2^j n)-j.
\]
Since appending a doubling costs one step, \(b_j\) is nonincreasing. It is at least \(\lceil\log_2 n\rceil\) and at most \(\lambda+v-1\), the latter by the binary method (a star chain). Denote its minimum by \(\ell_{\rm st}(n)\) and the first \(j\) attaining the minimum by \(J(n)\). In particular \(n\) is stable if and only if \(J(n)=0\). In the star case replace \(\ell\) and \(\ell_{\rm st}\) by their starred versions.

For any integer threshold \(k\ge\lambda\), define
\[
r=k-\lambda,\qquad m_r=\lfloor10r/3\rfloor,\qquad D_r=3m_r+2,\qquad
G_r(\lambda)=D_r!\,(\lambda+r+2^{m_r}+1).
\]
We will prove:

1. The relation \(\exists j\ge0\,[\ell(2^j n)\le j+k]\), also with an optional upper bound \(j\le J_0\), is effectively decidable. If it holds without an upper bound, it already holds for a \(j\le G_r(\lambda)\).
2. Compute \(\ell_{\rm st}(n)\) as the least successful \(k\) in the finite interval above, then \(J(n)\) as the least successful \(J_0\) at this \(k\). In particular,
   \[
   J(n)\le G_{v-1}(\lambda)
   \]
   unconditionally, or \(J(n)\le G_{\ell(n)-\lambda}(\lambda)\) with the actual defect.
3. As a theoretical complexity statement, the threshold decision is fixed-parameter tractable in \(r\), with binary input \(n,k\) and, if supplied, \(J_0\). Computing the stable length and \(J(n)\) is fixed-parameter tractable in \(\ell_{\rm st}(n)-\lambda\), even without knowing this parameter in advance. This is not a practical runtime bound on the accompanying reference code.

## 2. Compressing a bounded-defect chain

A doubling in this section always means \(a_i=2a_{i-1}\), not the doubling of some older term. If an increasing chain step is not a doubling, its two operands have sum at most \(a_{i-1}+a_{i-2}\). Assign \(\varphi=(1+\sqrt5)/2\). A maximal run of consecutive non-doublings starts just after a doubling, as the first step from 1 must be a doubling. If \(a\) is the value at the start of that run, the preceding value is \(a/2\). The first non-doubling gives at most \(3a/2\), and the recurrence \(a_i\le a_{i-1}+a_{i-2}\) and \(\varphi^2=\varphi+1\) then show that \(h\) successive non-doublings increase \(a\) by a factor at most \(\varphi^h\). Consequently a length-\(L\) chain with \(d\) non-doublings ends at most at \(2^{L-d}\varphi^d\). This also recovers the usual bound on the number of non-doublings in terms of defect.

For \(L\le j+k\) and target \(2^j n\), this yields
\[
d\log_2(2/\varphi)\le k-\log_2 n\le r.
\]
Here \(\varphi<34/21\) and \((21/17)^{10}>2^3\), so \(\log_2(2/\varphi)>3/10\), and \(d\le m_r\), independent of \(j\). This bound is all that is required, not a bound on how long a run of consecutive doublings can be.

Represent the chain as \(d+1\) blocks. Block \(i\) contains \(x_i,2x_i,\ldots,2^{t_i}x_i\), where \(t_i\ge0\), and \(x_0=1\). For \(1\le i\le d\),
\[
x_i=2^{u_i}x_{p_i}+2^{v_i}x_{q_i},\qquad
0\le p_i,q_i<i,\quad 0\le u_i\le t_{p_i},\quad 0\le v_i\le t_{q_i}.
\]
The index \(0\) and offset \(0\) are allowed. After the predecessor-block indices \(p_i,q_i\) are fixed, \(t_i,u_i,v_i,j\) are nonnegative integer variables. The length upper bound is
\[
d+\sum_{i=0}^d t_i\le j+k, \tag{1}
\]
and the target is \(2^{t_d}x_d=2^j n\). There are only finitely many predecessor patterns, and in the star case we require \(p_i=i-1\) and \(u_i=t_{i-1}\), swapping the two operands if needed.

Every ordinary chain yields such data. Conversely, any feasible description produces valid additions in the stated dependency order. Its non-doubling-designated steps may in fact coincide with doublings; this does not invalidate an upper length bound. In the ordinary case the resulting calculation need not be increasing: retain the ancestors of the target and identify equal numerical values, then sort by their values. Each retained non-initial value has a generating pair of strictly smaller retained values, since all terms are positive. Thus this gives a conventional chain of length at most (1). In the star case the imposed predecessor equation already makes every new term the sum of the immediately preceding term and a positive earlier term, so the computation is increasing and no reordering is needed.

## 3. Removing the exponentials by a finite carry certificate

For a fixed block pattern the final term expands as
\[
2^{t_d}x_d=\sum_{\beta=1}^{q}2^{E_\beta},\qquad q\le2^d,
\]
where each leaf exponent \(E_\beta\) is a homogeneous linear form in the shift and offset variables, with coefficients 0 or 1. The reason is that a leaf follows a strictly descending sequence of block indices, adding one offset per visited block and finally \(t_d\). In particular no variable appears twice along a single leaf path. Different leaves can give equal exponents.

Write \(S=\{s_1,\ldots,s_v\}\) for the set of positions of the 1 bits of \(n\). The target sum has distinct powers at exponents \(j+s_h\). If \(q<v\), equality is impossible. Otherwise use the following finite disjunction of linear systems:

* Pick a pair of current terms, impose equality of their exponents, and replace the pair by one term with the first exponent plus 1. Repeat \(q-v\) times, enumerating all choices of pairs at each step.
* At the end impose a bijection of the \(v\) surviving expressions with \(j+s_1,\ldots,j+s_v\), enumerating all bijections.

An equality added at a merge is linear: if the two forms are \(E_\beta+c\) and \(E_{\beta'}+c'\), impose \(E_\beta-E_{\beta'}=c'-c\). Every branch of this enumeration therefore consists only of linear equalities and inequalities with integer coefficients.

**Soundness:** each permitted merge preserves the integer sum and the final constraints give the actual target. **Completeness:** at any concrete valid assignment all equal exponents can be combined by ordinary binary carrying. When no duplicates remain, uniqueness of the binary expansion gives precisely the \(v\) desired terms. Every permitted normalization uses \(q-v\) merges, and one such merge sequence and labelling occurs in the enumeration. This reasoning handles arbitrarily large exponent values with no truncation. It would fail if one ignored carries and required the original \(q\) leaves to have distinct exponents.

For each \(d\le m_r\), each block pattern and each carry branch we now have a nonnegative integer linear system in \(3d+2\) variables. Its rows have coefficients in \(\{-1,0,1\}\), including the star restrictions, (1), and the range and optional \(j\le J_0\) constraints. This proves effective decidability by finite integer linear feasibility. The number of systems and their number of rows are bounded by functions of \(r\) alone: \(v>2^{m_r}\) can be rejected first, and otherwise the bit positions are obtained directly from the input. Using [Lenstra's fixed-dimensional ILP algorithm](https://doi.org/10.1287/moor.8.4.538), the decision takes \(f(r)\) times a fixed-degree polynomial in the input bit length. Scanning \(k\) upward until first success only invokes these bounds for \(r\le\ell_{\rm st}(n)-\lambda\), and the search for the least \(j\) can use the bound below.

## 4. Explicit cutoff for the first successful doubling

We use a standard short determinant argument. If \(P=\{z\ge0:Az\le b\}\subset\mathbb{R}^D\) is defined by integer data with \(|A_{ij}|\le1\), \(|b_i|\le B\), and has an integer point, then it has an integer point with each coordinate at most \(D!(B+1)\).

Indeed, \(P\) is a nonempty pointed rational polyhedron, so it is the convex hull of its vertices plus its recession cone. Each vertex is determined by \(D\) independent active constraints (including nonnegativity as needed). Cramer's rule bounds each vertex coordinate by \(D!B\). Every extreme recession ray has a nonnegative integer generator given by cofactors of \(D-1\) independent active homogeneous rows, so its coordinates are at most \((D-1)!\). This includes the case of a lower-dimensional polyhedron: active constraints still have the required ranks at a vertex and on the relative interior of an extreme ray, respectively. Express the recession part of an integer point by at most \(D\) such rays by conic Carathéodory. Subtract from that point the integer part of each ray coefficient times its integer generator. The result stays integral and in \(P\), and its coordinates are at most \(D!B+D(D-1)!=D!(B+1)\).

In our linear systems without an extra bound on \(j\), the carry constants have absolute value at most \(2^d-1\), since at most that many merges have happened. The right sides at the final matching have absolute value at most \(\lambda+2^d\), and \(|k-d|\le\lambda+r+2^{m_r}\). All other right sides are zero. We may take \(D=3d+2\le D_r\) and \(B=\lambda+r+2^{m_r}\). In particular a feasible system has a witness with \(j\le G_r(\lambda)\). This establishes the explicit cutoff and permits binary search on \(J_0\). Monotonicity \(b_{j+1}\le b_j\) then shows that once the computed minimum is attained, all later normalized lengths equal it.

## 5. A dependency-free exact decision procedure

The accompanying program uses a separate finite-state procedure for integer feasibility, not the much faster theoretical Lenstra bound. For each row keep a residual \(c\), initialized to that row's right side. Assign one binary digit to every variable at a time, least significant digit first, with digit vector \(\epsilon\in\{0,1\}^D\). A row with coefficient vector \(a\) is updated to
\[
c'=
\begin{cases}
(c-a\cdot\epsilon)/2, &\text{equality, allowed only if the numerator is even};\\
\lfloor(c-a\cdot\epsilon)/2\rfloor, &\text{inequality}.
\end{cases}
\]
This is exactly the substitution \(z=\epsilon+2z'\) for that row. Starting at \(b_i\), each component stays in the finite interval of radius \(\max(|b_i|,\|a_i\|_1+1)\); this follows by the triangle inequality after division by 2, including the possible rounding. One accepts when the remaining \(z'\) can be zero, i.e. all equality residuals are zero and every inequality residual is nonnegative. Reachability in the finite state graph is therefore necessary and sufficient. A path recovers the witness digits. This is useful for replayability, not for solving instances with many non-doublings quickly.

Run `python3 verify_factor_addition_chain_stability.py` for the finite cross-checks, or supply a positive input (and optionally `--star`) for the complete reference decision. The tests compare the finite-state solver with direct searches on bounded systems, compare symbolic carries with exact binary sums, evaluate random block certificates, and compare small-chain results with an independent enumeration of ordinary and star chains. No Lean run or exhaustive search over Scholz's conjecture is claimed.

## Scope in relation to Scholz–Brauer

For \(M_n=2^n-1\), the identity \(M_{2n}=2^nM_n+M_n\) allows lifting an upper chain from \(M_n\) to \(M_{2n}\) at a cost of \(n+1\). If \(n\) is stable and already satisfies the Scholz inequality, this propagates the inequality at all \(2^j n\); it likewise propagates a strict saving at a stable seed. The stability hypothesis is now decidable, but the proof supplies no Scholz upper chain at an arbitrary seed or at its computed stabilization index. The open inequality and the effective stability question are different statements.
