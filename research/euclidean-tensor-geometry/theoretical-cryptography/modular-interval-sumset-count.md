# Exact modular interval sums from few directions and small length sumsets

**Scope.** This is exact evaluation of a forward probability in a fully supplied mathematical model. There is no unknown parameter, secret recovery, observed cryptographic transcript, or security claim.

Let \(q\ge2\) be given in binary, let \(d\ge1\), and let \(A_1,\ldots,A_N\in(\mathbb Z/q\mathbb Z)^d\) be supplied. Independently choose \(X_i\) uniformly from the integer interval \([a_i,a_i+L_i-1]\) with \(L_i\ge1\) supplied in binary. The quantity of interest is one exact, rational probability
\[
   \Pr\left\{\sum_i A_i X_i=b \pmod q\right\}.
\]
The input lists all \(N\) intervals explicitly. Any prescribed further linear projection can be absorbed by multiplying the columns and target by its supplied matrix.

**Theorem.** Suppose the directions \(A_i\) assume at most \(k\) different values, for fixed \(k\). For each nonempty direction block \(I_j\), put
\[
 S_j=\left|\left\{\sum_{i\in J}L_i:J\subseteq I_j\right\}\right|.
\]
There is a deterministic exact algorithm with time polynomial in the input bit length and the \(S_j\), with exponent depending only on \(k\). In particular, for each fixed \(K\) it runs in bit-polynomial time if, in each direction block, the set \(E_j=\{L_i:i\in I_j\}\) of distinct **integer** lengths satisfies \(|E_j+E_j|\le K|E_j|\). It does not require a progression representation as input, and neither \(q\) nor any \(L_i\) is required to be numerically bounded. In the single-direction case the exact total variation to Haar on the generated cyclic group is also computable within the same bounds. Without structure on the lengths, computing the exact count in the numerator is \(\#\mathsf P\)-complete under polynomial-time counting Turing reductions even for a single direction \(A_i=1\in\mathbb Z/q\mathbb Z\), power-of-two \(q\), and no wraps.

## 1. Explicit breakpoints with signed cancellation

Translate away all \(a_i\) and the resulting deterministic output, and ignore any zero direction by dropping its independent factor from the probability. If no directions remain, the answer is 0 or 1 by comparing with the translated target. Below, products over intervals use the surviving indices unless stated otherwise. One could also merge opposite directions by reflecting the corresponding intervals and translating the target again. Write \(A^{(j)}\) for each remaining direction, \(m_j=|I_j|\), and \(Y_j=\sum_{i\in I_j}(X_i-a_i)\), with \(M_j=\sum_{i\in I_j}(L_i-1)\).

The count \(p_j(s)\) of tuples with \(Y_j=s\) is zero outside \([0,M_j]\) and has generating polynomial
\[
  \sum_sp_j(s)z^s=
     \frac{H_j(z)}{(1-z)^{m_j}},\qquad
  H_j(z)=\prod_{i\in I_j}(1-z^{L_i}).
\]
Let \(h_j(t)=[z^t]H_j(z)\). On integer arguments \(s\in[0,M_j]\),
\[
 p_j(s)=\sum_{t\le s} h_j(t)\binom{s-t+m_j-1}{m_j-1}.       \tag{1}
\]
This is the usual inclusion-exclusion formula for sums of discrete uniforms. The computational point is to list the (possibly colliding) subset sums before treating them as breakpoints. Maintaining a sparse dictionary from \(t\) to its signed coefficient, an insertion of \(L\) changes it to \(h(t)-h(t-L)\). Each partial support is contained in the subset sums of the full multiset, since any partial subset is a full subset. Thus all sparse updates take polynomial time in the input and \(S_j\), even if cancellations later remove terms. Integer keys have \(O(\log(1+\sum L_i))\) bits and signed coefficient magnitudes are at most \(2^{m_j}\). The same visits yield a computable certificate by simply retaining unsigned reachability as well, not relying on early accidental cancellation.

Sort all nonzero breaks in \([0,M_j]\) together with \(0,M_j+1\). Partition \([0,M_j]\) into integer intervals from a break through one less than the next. On each such piece the index set \(t\le s\) in (1) is fixed. The right side is an ordinary rational polynomial of degree at most \(m_j-1\), using the finite falling-factorial formula for the binomial. The number of pieces is at most \(S_j+1\); their endpoints have bit length polynomial in the original input. The coefficient list also has polynomial bit length: use common denominator \((m_j-1)!\), multiply at most \(m_j-1\) affine factors each with polynomial-bit coefficients in each summand, and add at most \(S_j\) terms. A singleton interval, and the case \(L_i=1\) for every index in a direction, fit the same rule.

## 2. The congruence cuts a fixed-dimensional integer box

Let \(A\) have columns \(A^{(j)}\). The integer vectors \(s=(s_1,\ldots,s_k)\) satisfying \(A s=b\bmod q\) are either absent or form a coset \(s_0+B\mathbb Z^k\), where \(B\) is a full-rank integer matrix because the kernel contains \(q\mathbb Z^k\). A polynomial-time integer Hermite/Smith calculation supplies a particular solution and basis; there is no requirement to factor \(q\). For example one can introduce integer variables \(u\) in \(As-qu=b\), solve the integer linear system, and project the solution lattice onto the \(s\) coordinates. The lift \(u=(As-b)/q\) is unique for each \(s\), and a Hermite basis of the projected lattice gives \(B\).

For each choice of one interval from each direction, let \([l_j,u_j]\) be its integer range. In \(z\)-coordinates take the rational parallelepiped
\[
  P=\{z\in\mathbb R^k:l_j-1/2\le (s_0+Bz)_j\le u_j+1/2\ \text{for all }j\}.
\]
It has \(2^k\) explicit rational vertices. An integer \(z\) cannot hit a half-integer facet because \(s_0+Bz\) is integral, so interior and closed-box integer sums coincide. This inflation also gives full dimension for singleton pieces. The weight on the parallelepiped is the polynomial \(\prod_j p_j((s_0+Bz)_j)\) obtained from the appropriate pieces. Its total degree is at most \(N\). Since \(k\) is fixed there are only polynomially many monomials even with this **growing** degree, and expanding an affine substitution and a product keeps every rational coefficient polynomial-bit. The weighted lattice-point sum over this fixed-dimensional rational polytope is available in deterministic polynomial time by Barvinok's [short rational function polynomial summation algorithm](https://arxiv.org/abs/math/0504444), §5, which takes the explicit coefficient list and allows the degree to grow. This is the weighted version, not an appeal to an unweighted counting oracle on a growing dimension.

Add the exact weighted counts over the at most \(\prod_j(S_j+1)\) disjoint integer boxes. Dividing by \(\prod_i L_i\) over surviving intervals gives the probability; multiplying the raw count by the product of discarded lengths would recover the original raw numerator. The output numerator and denominator have at most \(1+\sum_i\lceil\log_2(L_i+1)\rceil\) bits each. This proof never builds a modulus-sized state space. The weighted counting step is a theoretical ingredient, not implemented by the finite replay.

For example, let \(R=(\mathbb Z/q\mathbb Z)[X]/(X^n+1)\) with even \(n\). Three supplied dense ring elements \(A^{(1)},A^{(2)},A^{(3)}\) can multiply any number of independent scalar intervals chosen from three arithmetic progressions of lengths, one progression per direction. Taking coefficient vectors gives exactly the above conditions, including \(q\) with arbitrary composite factorization. This requires genuinely few distinct effective columns after the specified projection; it is not a property of a generic multiplication matrix or of standard Ring-LWE samples. We do not infer any unknown input or output element.

## 3. An intrinsic sufficient condition that does not need to be found constructively

Suppose \(E=E_j\subset\mathbb Z_{>0}\) satisfies \(|E+E|\le K|E|\). The integer Freiman theorem in the proper progression form (e.g. [Green–Ruzsa](https://arxiv.org/abs/math/0505198), introduction and Theorem 1.1 applied in \(\mathbb Z\)) gives a progression \(P\) of rank \(r_K=O_K(1)\) and volume \(\le C_K|E|\) containing \(E\). Writing its side cardinalities as \(d_1,\ldots,d_{r_K}\), the \(h\)-fold sum of \(P\) is contained in a progression on the same generators of side cardinalities at most \(h(d_\nu-1)+1\) for \(h\ge1\), without needing that enlarged progression to be proper. All subset sums of the \(m_j\) lengths lie in \(\bigcup_{0\le h\le m_j}hP\); consequently
\[
 S_j\le 1+C_K |E|(m_j+1)^{r_K+1}.
\]
The algorithm only used the existence of this progression to bound the encountered lists; it does not enumerate progressions or compute their generators. The small-doubling promise itself can be checked by sorting pairwise sums. A single interval length repeated many times, and all lengths drawn from a long arithmetic progression with very large starting point and step but polynomially many positions, are special examples. The exact law also allows distinct lengths even if their binary encodings are long.

## 4. Exact TV to Haar in the single-direction case

For a single nonzero direction, replace the ambient group by the cyclic group it generates. Its order \(Q=q/\gcd(q,A_1,\ldots,A_d)\) is given by the coefficients of that direction; the case \(Q=1\) is constant. In the resulting coordinate we can also compute the **whole-law** total variation to the uniform law in time polynomial in the same subset-sum bound and input bit length. This is not obtained by summing individual oracle queries over \(Q\) residues.

First the law is symmetric and nonincreasing in circular distance from a known center. Indeed each input reduced modulo \(Q\) has a constant part plus a positive multiple of an interval of \(r_i=L_i\bmod Q\) consecutive residues, starting at \(a_i\bmod Q\). If some \(r_i=0\) the convolution is uniform, and this is the only such case for \(Q>1\): at a primitive \(Q\)-th root, the geometric-sum characteristic factor is nonzero whenever \(Q\nmid L_i\). Otherwise the center of the residual interval is \(\gamma_i=a_i+(r_i-1)/2\bmod Q\), an integer or half-integer on the real circle of circumference \(Q\). The center of a convolution is the sum of the chosen centers. To check monotonicity, by nonnegative differences of radial levels it suffices to convolve two interval indicators of lengths \(a\le b\le Q\). Before wrapping, the count at displacement \(t\) from the sum of their centers is
\[
             G(t)=\max(0,\min(a,(a+b)/2-|t|)).
\]
This formula is used on the relevant integer or half-integer grid. For \(0\le t\le Q/2\) the wrapped count is \(G(t)+G(Q-t)\), including both distinct lifts at \(t=Q/2\). Indeed other lifts are outside the support. The second term can increase only once \(t>Q-(a+b)/2\ge(b-a)/2\). There, whenever it increases in the interior, \(t\le Q-t<(a+b)/2\), so the first term decreases at the same rate. The sum is nonincreasing. Any symmetric nonincreasing function on this circle grid is a nonnegative sum of centered interval indicators, by peeling successive radial levels; the constant function is allowed. This proves the asserted shape after any number of convolutions, without invoking continuity of the law as a grid function.

It follows that the residues with mass greater than \(1/Q\) form one circular interval (or the empty set). Its radius can be located in \(O(\log Q)\) point tests using §2, searching the set of allowed distances from the known integer or half-integer center. Ties at \(1/Q\) can be excluded. The total variation is the exact mass of this interval minus its size divided by \(Q\).

For completeness its mass is computable without another dependence on \(Q\). Subtract the deterministic starts and split the translated arc into at most two ordinary residue intervals. On each original polynomial piece \([l,u]\) for the integer sum in §1, the possible lifts of a residue \(r\in\{0,\ldots,Q-1\}\) have the form \(r+Qh\) for
\[
       \lceil(l-r)/Q\rceil\le h\le\lfloor(u-r)/Q\rfloor .
\]
Each of the two lift bounds changes at most once as \(r\) ranges through the representatives: at \(l\bmod Q\) for the lower bound, and one past \(u\bmod Q\) for the upper. Together these breaks give at most twice the number of original pieces plus one residue segments. On each segment the exact count polynomial in \(r\) is obtained by summing \(p(r+Qh)\) over the now fixed integer range of \(h\) for every original piece. Expanding into powers or falling factorials and using the polynomial sum of powers gives its rational coefficient list in polynomial bit complexity; degrees remain at most \(N-1\) in \(r\). The count on the arc is obtained by one more polynomial sum over the intersections of the residue segments with the arc. All factors have polynomial bit length even when the number of lifts is numerically large. This gives a complete exact TV calculation and a polynomial-size representation of all single-direction point masses.

## 5. Exact obstruction already for one modular direction

Let \(w_1,\ldots,w_N>0\) and \(0\le T\le W=\sum_iw_i\) be a counting subset-sum instance. Set \(M=W+1\), \(L_i=M+w_i\), and choose a power of two \(q>NM+W\). Thus every integer sum in the support is already \(<q\). Use direction 1, all interval starts zero, and let \(p(s)\) denote the raw point count retrieved from the point probability (by multiplying by \(\prod_i L_i\)). Let \(p(s)=0\) when \(s<0\).

By multiplying its generating polynomial by \((1-z)^N\), for any nonnegative integer \(v\)
\[
 [z^v]\prod_i(1-z^{M+w_i})=
       \sum_{j=0}^{\min(N,v)}(-1)^j\binom Nj p(v-j).             \tag{2}
\]
For \(v=kM+T\), the integers \(\sum_{i\in J}(M+w_i)\) at that exponent come only from \(|J|=k\) and \(\sum_{i\in J}w_i=T\): the difference of the two small sums has magnitude less than \(M\). Their common sign is \((-1)^k\). Evaluating (2) at all \(k=0,\ldots,N\) therefore recovers the counting subset-sum answer from at most \((N+1)^2\) exact point queries on one supplied law. The support remains an ordinary contiguous interval for each one-site variable. All query arguments are nonnegative and \(<q\) after omitting negative terms, even if a query falls beyond the total support. Numerator counts are in \(\#\mathsf P\) by uniquely guessing the binary encodings of the one-site draws and checking bounds and congruence, and counting subset sum is \(\#\mathsf P\)-hard: for a bipartite graph with \(E\) edges, number its vertices and assign each edge \(\{u,v\}\) the weight \(D^u+D^v\) in base \(D=E+1\). A subset sums to the number with every vertex digit 1 precisely when it is a perfect matching. There are no carries and the representation has polynomial bit length. Trivial empty or isolated cases can be handled separately. Thus [Valiant's zero-one permanent theorem](https://www.cs.bu.edu/faculty/gacs/courses/cs535/papers/Valiant_permanent.pdf) gives the required hardness. One can make all interval lengths odd by using \(M=2W+1\), \(L_i=M+2w_i\) and \(v=kM+2T\); the separation is unchanged. The reduction needs exact signed cancellation; it does not give hardness of relative approximation. In particular the one-dimensional attainable integer values before wrapping fill an interval, so count-hardness is not evidence for a hard support-decision problem.

## Source comparison

- Bradley and Gupta, [On the Distribution of the Sum of n Non-Identically Distributed Uniform Random Variables](https://www.ism.ac.jp/editsec/aism/54/689.html), discrete formulas in §3 for symmetric odd-length intervals, give classical non-identical-uniform sum identities. Equation (1) is their elementary coefficient counterpart; the new use is to compress the colliding breakpoints before imposing arbitrary composite congruences.
- Barvinok's §5 and Green–Ruzsa's fixed-doubling structure are explicitly reused, not reproved.
- The closely related general [independent discrete tail hardness](https://optimization-online.org/wp-content/uploads/2021/08/8566-1.pdf), Theorem 2.8, uses two-point inputs at arbitrary positions; that particular formulation does not give the unit-step interval promise used in (2).
- This note only claims the stated forward exact algorithm and no-wrap exact complexity obstruction; it is not a full classification by direction or subset-sum geometry and does not make a security or deployment claim.
