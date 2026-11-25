# Global repair barriers for address-dependent Fourier pencils

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

This is a restricted lower bound for circuits whose pencil primitives are as in [OpenAI's binary prime-kernel construction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-logarithmic-exponent-of-finite-Fourier-transforms-November-24-2026/build/kernel.tex). It extends the previously recorded fixed-frequency predictor/repair obstruction. The latter section also handles arbitrary joint pointwise gates on the two ordinary address halves at sufficiently wide blocks. None of these results rules out the endpoint for unrestricted Fourier circuits.

## Model

Work over C. There are W independent rows, and within each row the ordinary address is a pair in F_2^{bf} × F_2^{bf}. Let N=2^{2bf} be the number of ordinary addresses. The corresponding Walsh frequency coordinates are X=(X_1,...,X_b) and Z=(Z_1,...,Z_b), each block in F_2^f. Choose m distinguished block indices, numbered 1,...,m; b≥m. Write
\[
a_X(Z)=\sum_{i>m}X_i\cdot Z_i,\qquad
\lambda_j(Z)=X_j\cdot Z_j+a_X(Z),\quad Q_j=(-1)^{\lambda_j(Z)} .
\]
We require the exact product of the Q_j on each row, in the kernel's own coordinates before the input/output monomial maps.

A pencil is an arbitrary constant matrix row combination of I and the Q_j; we count at most t pencils on every unrepaired input-output path. One-sided pointwise row maps may be placed arbitrarily: for each ordinary second-half address z, they act by any prescribed row matrix, independent of the ordinary first-half address. Such a pointwise gate can mix frequencies nontrivially. A network may also have arbitrary linear repairs with a total of H scalar returned wires across the entire register, not H per frequency; their outputs can mix any frequencies and feed future stages or other repairs. The network is acyclic. Cutting those returns gives an unrepaired operator P. The true transfer minus P has rank at most H: after cutting regard all H return values as extra inputs, then substitute their actual linear functions of the original input.

## Exact lower bound

Let independent Y_j have probabilities Pr(Y_j=0)=2^{-f}, and Pr(Y_j=1)=Pr(Y_j=-1)=(1-2^{-f})/2. Then necessarily
\[
 \frac{H}{WN}\ \ge\ \Pr\!\left[\sum_{j=1}^mY_j\ge t+1\right].
\]

Proof. Fix X and let J be its active indices with X_j≠0, L=|J|. Their lambda_j have independent distinguished-block components, so are linearly independent; their span intersects the aux-only span of a_X trivially. Choose a complement C_X to their span containing a_X. In the space of functions of Z, use the basis of Walsh characters indexed by the linear forms \(\beta+\sum_{j\in J}c_j\lambda_j\) with \(\beta\in C_X\), \(c_j\in\mathbb F_2\), and define grade to be the Hamming weight of c. This is also a grading for vector-valued row functions.

The pencil multiplication operator raises grade by at most 1: multiplication by an active Q_j adds lambda_j and flips the corresponding c_j; an inactive Q_j adds a_X and changes only beta. A one-sided ordinary row map fixes X, and in the Z-frequency variables acts by matrix-valued convolution. That convolution is diagonal on Z characters (each gets its own row matrix); in particular it preserves this grading exactly. By induction on circuit paths, P maps grades ≤r to grades ≤r+t. But multiplication by all Q_j flips all L active coordinates and optionally changes beta by (m−L)a_X, so sends grades ≤r to grades ≥L−r.

Take \(r=\lfloor(L-t-1)/2\rfloor\) and use an empty subspace if r<0. On grades ≤r, the exact target is injective and its image has grade strictly above every grade of P. Thus the difference of target and P is injective on this subspace. Both preserve X; consequently their difference is injective on the direct sum of all chosen subspaces. Each X contributes \(W 2^{bf-L}\sum_{i=0}^r\binom Li\) dimensions. Divide the dimension sum by WN. Under uniform X, L has binomial law Bin(m,1−2^{-f}); conditional on active indices, a uniformly random grade is Bin(L,1/2). Therefore the resulting normalized dimension is the asserted tail (active indices each supply independent unbiased ±1 and inactive indices contribute zero). Rank at most H completes the proof.

More abstractly, the same argument works when the permitted side operators are arbitrary degree-filtration-preserving linear maps, not necessarily convolutions. It also allows extra input-independent linear scaling and sums of parallel paths as long as each surviving path uses at most t pencils. No assumption about pointwise repair was used. Choosing the opposite half in place of the second half works by exchanging X,Z; alternating arbitrary maps dependent on opposite halves is outside the result.

## Stage-plus-repair consequence

Uniformly for integers f≥1, let \(\nu=1-2^{-f}\). In the abstract normalized ledger one necessarily has
\[
t+\frac{mH}{WN}\ \ge\ (\sqrt{\nu}-o(1))\sqrt{m\log m}.
\]
Indeed, regard L as Bin(m,ν) and condition on \(|L-\nu m|\le2\sqrt m\), an event of probability at least 15/16 by Chebyshev since variance ≤m/4. Uniformly for L in this range and for t proportional to \(\sqrt{m\log m}\) with coefficients bounded away from 0, a binomial local Stirling estimate on \(\left\lfloor\sqrt{L/\log L}\right\rfloor\) consecutive masses just below \((L-t-1)/2\) gives log tail at least \(-t^2/(2\nu m)-O(\log\log m+1)\); replacing L by νm changes that exponent by \(o(1)\). More explicitly, the individual masses have size at least a constant times \(L^{-1/2}\exp(-t^2/(2L)-O(1))\) on this interval, since displacement within the interval adds a bounded amount to the exponent, and the quartic entropy error is \(O((\log m)^2/m)\). Small t only strengthens the tail by monotonicity. If t≤\((\sqrt{\nu}-\varepsilon)\sqrt{m\log m}\) for fixed sufficiently small ε>0, the bound is at least \(m^{-1/2+c_\varepsilon}\) for some fixed \(c_\varepsilon>0\) uniformly over \(\nu\in[1/2,1)\) and large m. The repair term then dominates \(\sqrt{m\log m}\). In particular even arbitrary global or hierarchical sparse correction wires do not remove the \(\sqrt{\log m}\) loss with these side operations; departing from the one-sided degree-preserving framework, or charging the ledger differently, is necessary.

The argument is a global rank/filtration extension of the Smolensky parity-degree mechanism (see [A proof of Smolensky's lower bound](https://eccc.weizmann.ac.il/report/2015/189/revision/2/download/)); no general circuit-size lower bound is asserted.

## Joint two-sided address dependence via coordinate subspaces

Allow an arbitrary row matrix at each full ordinary address, depending jointly on both halves. The normalized repair lower bound now has a different distribution, but still gives the same leading ledger obstruction in the growing-\(f\) regime:
\[
 \frac H{WN}\ \ge\
 \mathbb{P}\!\left[\operatorname{Bin}\left(m,\tfrac12+2^{-f-1}\right)\le
 \left\lfloor\frac{m-t-1}{2}\right\rfloor\right].
\]
In particular, if \(2^{-f}\sqrt{m/\log m}=o(1)\) (for example \(f\ge\log_2m\)), then \(t+mH/(WN)\ge(1-o(1))\sqrt{m\log m}\).

Work in the ordinary coordinate basis. Each distinguished block uses both \(f\)-bit labels, so has dimension \(B=2^{2f}\). Let \(J\) be the local involution conjugate by normalized Walsh transform to the frequency multiplier \((-1)^{X_j\cdot Z_j}\). Let \(P_-\) be its negative-eigenspace projector. Its rank is \(r=(B-2^f)/2\), by counting the negative signs, and every diagonal entry is \(r/B\), since the Walsh transform has all squared entries \(1/B\).

Consider the coordinate matroid of vectors \(P_- e_i\), of rank \(r\). For any coordinate index set \(X\), the Gram submatrix \(P_-[X,X]\) has eigenvalues in \([0,1]\); its trace is \((r/B)|X|\). Thus its rank, the matroid rank \(r(X)\), is at least \((r/B)|X|\). Therefore \(|[B]\setminus X|\ge 2(r-r(X))\) for every \(X\). The [Edmonds–Fulkerson matroid base-packing criterion](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf) supplies two disjoint coordinate bases \(S,T\), each of size \(r\).

Let \(U=\operatorname{span}\{e_i:i\in S\}\). It intersects the positive eigenspace trivially because projecting \(U\) into the negative eigenspace is injective (by the basis \(S\)). It intersects the negative eigenspace trivially because such a vector supported on \(S\) vanishes on \(T\); the projections \(P_-e_i\), \(i\in T\), span the negative eigenspace. Thus \(U\cap JU=0\): if \(u,Ju\in U\), then \(u+Ju\) and \(u-Ju\) lie in the two respective eigenspaces and must both vanish.

Filter the ordinary array by the number of distinguished blocks outside \(U\). Precisely, \(F_j\) is the sum of tensor subspaces with arbitrary vectors in at most \(j\) distinguished blocks, and factors in \(U\) in all other distinguished blocks; the auxiliary space and the rows are arbitrary. Since \(U\) is a coordinate space, **every** joint pointwise address-dependent row map preserves \(F_j\). A pencil raises \(j\) by at most one: its \(Q_i\) term acts by \(J\) on block \(i\) and by a common operator on auxiliary coordinates, with no effect on the other distinguished blocks. Therefore after cutting repair returns the unrepaired output on \(F_j\) lies in \(F_{j+t}\). In contrast, the target product sends \(F_j\) to the analogous space with at least \(m-j\) factors in \(JU\). Choose a basis simultaneously containing bases of \(U\) and \(JU\). If \(2j+t<m\), the basis-tensor supports for these two spaces are disjoint: a tensor cannot have both \(m-j\) slots in \(JU\) and \(m-j-t\) slots in \(U\). The target minus the unrepaired map is then injective on \(F_j\). Its rank is at most \(H\), so its relative dimension, \(\mathbb P[\operatorname{Bin}(m,1-r/B)\le j]\), proves the displayed formula.

For the asymptotic consequence, in the stated regime the mean displacement of this binomial from the cutoff is \((t+o(\sqrt{m\log m})+O(1))/2\), and the variance is \((1+o(1))m/4\). Stirling's formula on a block of \(\lfloor\sqrt{m/\log m}\rfloor\) consecutive masses just below the cutoff yields a lower tail of \(m^{-\frac12(1-\varepsilon)^2+o(1)}\) whenever \(t\le(1-\varepsilon)\sqrt{m\log m}\) for fixed \(\varepsilon>0\). The repair term then dominates \(\sqrt{m\log m}\). This argument is valid uniformly along such growing-block sequences. Arbitrary permutations or gates which move inputs between ordinary addresses can change many distinguished coordinate memberships simultaneously; they are not covered as free operations. 
