# Worst-case likelihood is hard on dense fixed designs with uniform local coefficient statistics

The sparse fixed-design reduction may seem to derive its difficulty only from visibly sparse coefficients. That restriction can be removed without replacing the problem by an average-case assertion. For any fixed order of local coefficient statistics, there are deterministic fixed designs of distinct dense units that match all such statistics asymptotically, while exact likelihood optimization on their grid observations remains NP-hard. Global algebraic relations persist and prevent interpreting these designs as independent uniform ones.

## 1. Statement

Fix an odd prime \(q\), a positive integer \(K\), a nonnegative integer \(J\), and a fixed rational \(\epsilon\in(0,1/2)\). For infinitely many power-of-two dimensions \(d\) there is a deterministic, uniformly polynomial-time computable design \((B_1,\ldots,B_T)\) in \(R_d=\mathbb F_q[X]/(X^d+1)\), \(T\le d\), with these properties.

1. The \(B_i\) are distinct units and are linearly independent over \(\mathbb F_q\).
2. Choose any \(1\le \ell\le K\) distinct pairs \((i_j,o_j)\) with \(i_j\in[T]\), \(o_j\in\{0,\ldots,J\}\), repeats of a row at distinct offsets allowed. For every \(u\in\mathbb F_q^\ell\),
   \[
     \left|\frac1d\#\{x\in\{0,\ldots,d-1\}:\
         ( (B_{i_j})_{x+o_j\bmod d})_{j=1}^{\ell}=u\}
              -q^{-\ell}\right|\ \le\ 2d^{-1/2+\epsilon}.           \tag{1}
   \]
   In particular individual rows have proportion \(1-1/q+o(1)\) nonzero coefficients. This tests simultaneous bounded patterns, not randomness of the whole matrix.
3. For every common \(0<b<1\), it is NP-hard in the deterministic worst case to return a label maximizing
   \[
      \sum_{i=1}^{T}\sum_{x=0}^{d-1}
          \log f_b(y_{i,x}-(B_i s)_x/q),\qquad
      f_b(y)=\sum_{n\in\mathbb Z}b^{n^2}e^{2\pi iny},
   \]
   given rational-grid observations \(y\in(\frac1q\mathbb Z/\mathbb Z)^{Td}\) at this fixed design. At \(q=3\), the corresponding coefficient-Hamming decision problem for these designs is NP-complete. Only \(y\) and (for Hamming) its integer distance cutoff depend on the problem instance.

The hardness statement is a search optimization reduction with finite verification on a returned optimizer. It makes no claim that a general transcendental likelihood threshold decision lies in NP. In particular it says nothing about independent random designs, the complexity of an ordinary random-data search problem, or a deployed cryptographic system.

## 2. Spread supports in a fixed-design coloring reduction

We give the fixed-design part explicitly. Pad a graph to a power-of-two size \(N\) using isolated vertices. Let \(p_i=(J+1)i\) for \(0\le i<N\). A slot for a pair \(i<i'\) starts from the binomial \(a_{ii'}=X^{-p_i}-X^{-p_{i'}}\); coordinate zero of \(a_{ii'}s\) is \(s_{p_i}-s_{p_{i'}}\) as long as \(d>p_{N-1}\). For each slot and each \(u\in\mathbb F_q^\times\), allocate \(q(q-1)\) row positions, for a total \(T=q(q-1)^2\binom N2\). Use \(d=C_{q,J}N^2\) for a sufficiently large fixed power of two \(C_{q,J}\). In particular ensure \(d>4(2J+1)T\), \(d>2p_{N-1}+2J+2\), \(T\le d\). Then the two support positions of each base row have cyclic distance \(>J\).

In a fixed enumeration of all slots, scalars and allocated positions, multiply each base row \(u a_{ii'}\) by a public monomial \(X^t\) chosen greedily. Require that its two cyclic support positions have distance \(>J\) from all support positions previously used; take the least shift \(t\) satisfying this condition. Each already used site forbids at most \(2(2J+1)\) shifts (either of the two new sites in its \(J\)-neighborhood). The chosen \(d\) guarantees an available shift. Thus after shifting, the support positions of *all* rows are mutually separated by more than \(J\) on the cycle. Denote the resulting rows by \(A_i\). They are linearly independent and distinct because their supports are pairwise disjoint. They are units: factor out a scalar and a signed monomial, leaving \(1-W\) with \(W=\pm X^h\), \(0<h<d\). Then \(a=d/\gcd(d,h)\) is even, \(W^a=-1\), and
\((1-W)(1+\cdots+W^{a-1})=2\), which is invertible at odd \(q\).

For the observation rule, view every row in its unshifted coordinates, then apply the same signed coordinate permutation \(X^t\) to its responses. The log likelihood is unchanged because \(f_b\) is even. Write \(h(x)=\log f_b(x)\), \(H_q=\sum_{a\in\mathbb F_q} h(a/q)\). At each row group for fixed pair and fixed nonzero \(u\), the nuisance coordinates other than zero visit each grid phase \(q-1\) times, independently of the choices for coordinate zero. Their total contribution is independent of \(s\). At coordinate zero use each nonzero target \(q\) times for a graph edge, and each target including zero \(q-1\) times for a non-edge. If \(z=s_{p_i}-s_{p_{i'}}\), the active contribution over all \(u\ne0\) is
\[
 q\left((q-1)H_q-\sum_{u\ne0}h(uz/q)\right).
\]
For \(z=0\) the sum is \((q-1)h(0)\), while for \(z\ne0\) it is \(H_q-h(0)\). An inactive slot contributes a constant. Thus the entire likelihood is an additive constant plus
\[
       q\big(q h(0)-H_q\big)\,\#\{\,\{i,i'\}\text{ an edge}:s_{p_i}\ne s_{p_{i'}}\,\}.       \tag{2}
\]
The displayed multiplier is strictly positive: \(f_b(0)-f_b(a/q)=2\sum_{n\ge1}b^{n^2}(1-\cos(2\pi n a/q))>0\) for \(a\ne0\). Positivity of \(f_b\) itself follows from its periodized Gaussian form. Every vertex labeling extends to a vector in \(R_d\). The original graph is \(q\)-colorable if and only if all edges are cut on a maximizing label; this is checked by finite arithmetic without a numerical likelihood threshold. The classical NP-completeness of 3-colorability is from [Garey–Johnson–Stockmeyer](https://doi.org/10.1016/0304-3975%2876%2990059-1); for each fixed \(q>3\), adding a universal clique of size \(q-3\) reduces to fixed \(q\)-colorability.

At \(q=3\) the log-density on the grid has just two distinct values (at zero and at the two nonzero residues). Let \(\gamma=h(0)-h(1/3)>0\); the likelihood is exactly \(Td\,h(0)-\gamma D(s)\), with integer Hamming distance \(D(s)\). In (2) the multiplier is \(6\gamma\), so the distance is a baseline integer minus six times the cut count. One can obtain that integer baseline by evaluating \(D(0)\), since the cut count is zero at the all-zero vector. Hence \(D_0=D(0)-6\,|E|\) is a valid computable cutoff for the many-one reduction; if it were negative for any input, that input would already be a NO and could be mapped to a fixed NO. Membership in NP follows by integer multiplication and mismatch counting on a supplied label. The shift construction altered no response count and the design depends on \(N\) (equivalently on \(d\)) only.

## 3. A deterministic common multiplier producing all the local statistics

Temporarily choose \(v=(v_0,\ldots,v_{d-1})\) uniformly in \(\mathbb F_q^d\), without requiring that it is a unit. Consider the rows \(A_i v\). At a fixed cyclic coordinate \(x\), each selected entry at offset \(o\) of row \(i\) is a linear combination of two distinct coordinates \(v_{x+o-a\bmod d}\), one for each support exponent \(a\) of \(A_i\), with nonzero signs or scalars. Across distinct selected pairs \((i,o)\), these input coordinates are disjoint: an overlap would require \(a-a'=o-o'\bmod d\), which is impossible for distinct support sites with cyclic distance \(>J\). If \(a=a'\), the site belongs to a unique row and would force identical offsets and hence identical selected pairs. Therefore the selected entries are independent uniform residues at each fixed \(x\). The signs at negacyclic carries do not affect this conclusion.

For one test pattern in (1), write \(Z\) for its number of occurrences as \(x\) ranges over the cycle. Then \(EZ=dq^{-\ell}\). Changing a single coefficient of \(v\) changes at most \(2\ell\) of the indicator summands (for each chosen pair and each support site, at most one \(x\)). Bounded differences gives a tail \(2e^{-c_\ell t^2/d}\) around its mean. For any even positive integer \(p\) integration of that tail bounds \(E|Z-EZ|^p\le C_{\ell,p} d^{p/2}\). Expanding this centered moment as a polynomial in the indicator summands shows that each term depends on at most \(2\ell p\) distinct coordinates of \(v\). Thus its value is unchanged if \(v\)'s coordinates are only \(2Kp\)-wise independent and uniform. The mean is also unchanged.

Take a fixed even \(p\) so large that \(p\epsilon>K+2\). Markov at \(d^{1/2+\epsilon}\), and the union bound over at most \(O_{q,J,K}(d^K)\) tests, show that all tests attain the bound with coefficient 1 in place of 2, with probability tending to one under any such bounded-independence family. For a deterministic search use the standard polynomial-evaluation construction of bounded independence (compare [Alon–Babai–Itai, Proposition 6.3](https://web.math.princeton.edu/~nalon/PDFS/Publications2/A%20fast%20and%20simple%20randomized%20parallel%20algorithm%20for%20the%20maximal%20independent%20set%20problem.pdf)): take a field extension of \(\mathbb F_q\) of degree \(m=\lceil\log_q d\rceil\), evaluate uniformly chosen polynomials of degree \(<2Kp\) at \(d\) distinct field points, and apply a fixed nonzero coordinate-linear functional to each value. Uniformity on any \(2Kp\) distinct evaluations follows by the Vandermonde matrix. The extension can be found deterministically in polynomial time in \(d\), for example by enumerating monic polynomials of degree \(m\) and checking for monic divisors up to degree \(\lfloor m/2\rfloor\). Both enumerations are polynomial since \(q^m=O(d)\). The family of seeds has size \(q^{m(2Kp)}=d^{O_{K,\epsilon}(1)}\) and every pattern count can be checked in polynomial time. Therefore the first seed satisfying all tests can be selected deterministically from \(d\) alone. The comparisons with the chosen rational-power tolerance can be carried out on integers by clearing denominators and taking a fixed integer power.

It remains to make \(v\) a unit. For all sufficiently large dyadic \(d\), the number \(F\) of irreducible factors of \(X^d+1\) over \(\mathbb F_q\) is
\[
        F=2^{v_2(q^2-1)-2}\le (q+1)/2<q .
\]
Indeed the order of \(q\) modulo \(2d\) is the common factor degree, since every root has exact order \(2d\), and
\(v_2(q^{2^j}-1)=v_2(q^2-1)+j-1\) for \(j\ge1\) by successive differences of squares. Exactly one of \(q-1,q+1\) has 2-adic valuation 1, giving the inequality. In each factor field, at most one scalar \(a\in\mathbb F_q\) can make \(v+a\) zero. Since \(F<q\), one of the \(q\) shifts \(v+a\) is a unit; find it by polynomial greatest common divisor with \(X^d+1\). This changes just one input coefficient and hence changes each pattern count by at most \(2\ell\). The repaired multiplier, denoted \(w\), satisfies (1) for large \(d\).

## 4. Transfer the exact objective and delimit the randomness claim

Use \(B_i=A_i w\). Multiplication by a unit preserves the rows' distinctness, unit property, and coefficient-vector linear independence. Section 3 proves the pattern estimates for them. All choices for \(B_i\) depend solely on \(d\); the same observations as in §2 are used, and the map \(s\mapsto ws\) is a bijection between the likelihood objectives as functions of the labels:
\[
                 B_i s=A_i(ws).
\]
Apply the coloring cutoff to the vector \(ws\) when an optimizer for the dense instance is returned. For \(q=3\) the same Hamming cutoff on the same observations works without evaluating the multiplier numerically; it is again an NP-complete finite verification problem. No sampling from an actual cryptographic instance is involved.

This construction extends the [earlier two-sparse fixed-design reduction](https://github.com/mxym/math/blob/305aab03fea43ba9748ff4a62badc6e76c8f466f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-sparse-likelihood-hardness.md). The independent additions are the disjoint, spaced support arrangement and deterministic common unit gauge that passes every test in (1). The distinction from independent uniform designs is strong: normalizing any pair of rows by one of them cancels the common multiplier and gives the prescribed deterministic ratio \(B_i B_j^{-1}=A_i A_j^{-1}\). Under two independent uniform units that same specified ratio has probability \(1/|R_d^\times|\), which is exponentially small in \(d\) (the number of factors is fixed and each residue field grows exponentially). Thus matching all these bounded patterns cannot justify either an average-case hardness conclusion or a claim that the full design is pseudorandom. The theorem does not analyze any real system.
