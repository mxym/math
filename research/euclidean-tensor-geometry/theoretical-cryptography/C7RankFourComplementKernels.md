# Complement ranks when a thirteen-column \(C_7\) code meets an eight-column hyperplane

Put \(D=\{0,1,-1\}\subset\mathbb F_7\). A rank-five matrix \(H\) with thirteen columns is called **dissociated** here if \(\ker H\cap D^{13}=\{0\}\). This is the linear independence condition for the corresponding code in the strong graph power \(C_7^{\boxtimes13}\), not linear independence of its thirteen columns.

**Theorem.** If a hyperplane \(U\) contains eight of the columns, the other five columns \(Y\) have linear rank at least four. In the quotient line \(\mathbb F_7^5/U\), if their absolute labels have normalized multiset \((1,1,1,2,3)\), the five columns are linearly independent. Consequently a rank-four complementary set is possible only with the quotient multiset \((1,1,2,2,3)\). In these normalized coordinates its one-dimensional kernel is among an explicitly checked list of **167 necessary lines**; the list is not a claim that these kernels can all be realized.

The [earlier proper-flat theorem](C7RankFiveResidualFibers.md) gives the eight-column cap and the two possible quotient multisets; those are not new here. The new ingredient is to examine quotients by small actual kernel subspaces, rather than only the full projected kernel. This is a necessary condition on a prospective rank-five code, not an exclusion of all such codes or a general Shannon capacity bound. For comparison see [Guruswami–Riazanov](https://arxiv.org/abs/2009.05685) on finite-field polynomial bounds.

## 1. From an eight-column separator to a Fourier witness

Write \(X\) for the eight columns in \(U\), which span \(U\) by the earlier rank-three cap. Write \(Q:\mathbb F_7^5\to\mathbb F_7\) for the projection of the five \(Y\)-columns modulo \(U\), in the order displayed in the statement. Column sign changes translate the associated binary image sets and preserve the \(D\)-kernel test; whole-line scalar changes leave \(\ker Q\) unchanged. Thus we use \(Q(v)=\sum_{j=0}^4 M_j v_j\), with \(M_0=1\) and one of the two exact tuples \(M\). Let \(L=\ker Q\cong\mathbb F_7^4\), using coordinates \(v_1,\ldots,v_4\) and forcing \(v_0=-\sum_{j=1}^4M_jv_j\). Put \(K=\ker H_Y\subseteq L\), and let \(S=(D^5\cap L)\setminus\{0\}\).

For reference, if \(t=\vartheta(C_7)=7\cos(\pi/7)/(1+\cos(\pi/7))\), the separator inequality from the earlier theorem is
\[
                 \vartheta(\overline{G_Y})\le t^8/7^4,
\tag{1}
\]
where \(G_Y\) is the Cayley graph on \(L/K\) with nonzero connection set the image of \(S\). Indeed take \(W=H_Y(L)=\operatorname{span}Y\cap U\simeq L/K\) and embed \(H_X^{-1}(W)\) by \(a\mapsto(a,H_Xa)\) into the strong product of \(C_7^{\boxtimes8}\) with \(G_Y\). Confusability would give a nonzero signed column relation, so the image is independent. Its size is \(7^{4+\dim W}\). The product rule for theta and its complement-product identity for vertex-transitive graphs give (1). These identities are due to [Lovász](https://doi.org/10.1109/TIT.1979.1055985).

It suffices to exceed the right side of (1) on a quotient \(L/K_0\) with \(K_0\subseteq K\). Namely take an even function \(f\) supported on zero and the image of \(S\), with \(f(0)=1\), nonnegative Fourier transform, and total mass greater than the right side of (1). Summing \(f\) over the fibers of \(L/K_0\to L/K\) keeps the total mass and restricts the Fourier transform to the quotient characters. The value at zero is unchanged because \(K\cap S\) is empty for a dissociated matrix. On \(L/K\) the scaled matrix \(f(a-b)/|L/K|\) is then positive semidefinite with trace one, zero on edges of the complement, and all-entries sum \(\sum f\), contradicting (1). Collisions among nonzero projected support elements are allowed. This is the Fourier form of the theta bound on finite Cayley graphs; see also [DeCorte–de Laat–Vallentin](https://arxiv.org/abs/1307.5703).

## 2. Exact line and plane census

The exact comparison target is \(12227/2000=6.1135\), strictly greater than \(t^8/7^4\). For \(M=(1,1,1,2,3)\) the set \(S\) has 16 sign-pairs; for \(M=(1,1,2,2,3)\) it has 17. A line meeting \(S\) is impossible from the outset. For any remaining line, project \(S\) to the three-dimensional quotient, combining coincident sign-pairs. The certificates assign the same nonnegative rational weight to both signs of each support class, with \(f(0)=1\). The complete counts are
\[
\begin{array}{c|r|r|r|r}
 M &\text{lines in }L&\text{meeting }S&\text{ruled out by Fourier witnesses}&
 \text{not ruled out by these line tests}\\\hline
 (1,1,1,2,3)&400&16&384&0\\
 (1,1,2,2,3)&400&17&216&167.
\end{array}
\]
Thus in the first case \(K\) contains no line and is zero. In the second case test a putative two-dimensional \(K_0\subseteq K\). Every one of its eight projective lines has to be in the remaining line list. Enumerating all \(2850\) planes of \(L\) leaves precisely eight satisfying this test and avoiding \(S\). Each of the eight also admits a certified Fourier witness achieving at least \(12227/2000\) on its two-dimensional quotient, so none can be a subspace of \(K\). This rules out every \(K\) of dimension at least two; it does not assume the five columns have rank four beforehand. Since \(\operatorname{rank}H_Y=5-\dim K\), the rank and necessary line assertions follow.

## 3. Reproduce the exact inequalities

Run `python3 verify_c7_rank_four_complement_kernels.py` beside [the certificate data](c7_rank_four_complement_kernel_certificate.json). The integer verifier independently regenerates every \(L\)-support, line and plane by reduced echelon forms, checks the coverage of all required cases, and identifies unused data as an error. An explicit normalized description of the remaining 167 lines is the complement of the two rejection sets in the second row, with first nonzero coordinate one in the free coordinates \(v_1,\ldots,v_4\). This can be generated directly from the checker, not by solving an optimization problem.

Each weight has denominator \(10^7\). For a nontrivial frequency with exponent \(j\), bound \(2\cos(2\pi j/7)\) below by its rational endpoint at denominator \(10^9\). The three distinct nontrivial values solve \(z^3+z^2-2z-1=0\), as follows from summing the seventh roots of unity in pairs. Exact signs at the endpoints give the three disjoint intervals and identify the cosine values in decreasing order. The positive largest root also bounds \(\cos^2(\pi/7)=(2+z)/4\) and hence \(t<331767/100000\); rational arithmetic verifies \(t^8/7^4<12227/2000\). Nonnegative weights permit termwise lower bounds, so each Fourier positivity test and each objective comparison is entirely integer arithmetic after multiplication by the fixed denominators. A numerical LP was used to find weights, not to certify them.

The two compressed blocks store base64-encoded gzipped JSON. They map normalized line representatives or plane echelon rows to arrays of integer weight numerators, ordered by the lexicographically sorted nonzero projection sign-pairs. Ordinary Python standard-library decoding is sufficient, including for inspecting all witness terms.
