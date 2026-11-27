# Four orthogonal characters certify a nine-point ternary tile

Let \(A\) be a nine-point subset of \(V=\mathbf F_3^d\), with \(d\ge2\). For a linear functional \(b\in V^*\) let \(\chi_b(x)=\omega^{b(x)}\), where \(\omega=e^{2\pi i/3}\). Orthogonality is with respect to the sum inner product over \(A\). A translational tile is a set \(A\) for which some subset \(B\) gives each element of \(V\) a unique representation \(a+b\); \(B\) is not assumed to be linear.

**Theorem.** The following conditions are equivalent:

1. At least four restricted characters on \(A\) are pairwise orthogonal.
2. \(A\) is spectral.
3. A surjective linear map \(\pi:V\to\mathbf F_3^2\) restricts to a bijection on \(A\).
4. \(A\) tiles with a linear-subspace complement.
5. \(A\) is a translational tile.

In fact, from any four such frequencies and any prescribed base frequency among the four, two of the three differences from the base span a two-dimensional linear spectrum of \(A\). The maximum number of pairwise orthogonal restricted characters is always one of \(1,3,9\), and all three occur in every \(d\ge3\). In particular, four cannot be replaced by three in condition 1.

The partial-orthogonality assertion has an elementary proof. The ordinary-tiling implication uses the published nine-element nonfull-rank factorization theorem of Szabó.

## 1. An elementary ternary-word lemma

Call a word of length nine over \(\mathbf F_3\) balanced if each residue occurs three times. If \(u,v,w\) are balanced and all their pairwise differences are balanced, **at least one of their pairwise sums is balanced**.

For any two words \(x,y\) to which the hypothesis applies, the sums of their entries and their squared entries, and those for \(x-y\), are zero in \(\mathbf F_3\). Expanding the last square gives \(\sum_i x_i y_i=0\). Hence the first and second moments of \(x+y\) also vanish. If \(n_1,n_2\) are the counts of residues 1 and 2 in the sum, these moments say \(n_1+2n_2=n_1+n_2=0\) modulo 3. All three counts are multiples of three; when the sum is not balanced its histogram is a permutation of \((9,0,0)\) or \((6,3,0)\).

Suppose \(u+v\) and \(u+w\) are both unbalanced. Neither can be constant, since their difference \(v-w\) is balanced. Write
\[
u+v=a+\varepsilon 1_S,\qquad u+w=b+\delta 1_T,
\qquad |S|=|T|=3,\quad\varepsilon,\delta\in\mathbf F_3^\times .
\]
If \(\delta=-\varepsilon\), their difference is a shift and scaling of \(1_S+1_T\), whose residue counts are \((3+k,6-2k,k)\) for \(k=|S\cap T|\). No \(k\) makes those counts all three. Thus \(\delta=\varepsilon\), and balance of \(1_S-1_T\) forces \(S\cap T=\varnothing\). The word \(v\) is obtained from the balanced word \(a-u\) by shifting the entries on \(S\) by \(\varepsilon\). Since \(v\) is also balanced, the counts on \(S\) must be invariant under this three-cycle of residues. Accordingly \(S\) has one entry of each value of \(u\), and the same argument applies to \(T\). On \(S\cup T\) the values of \(u\) occur twice each. It follows that
\[
v+w=a+b+u+\varepsilon 1_{S\cup T}
\]
is balanced. This proves the lemma.

## 2. From four restricted characters to a linear spectrum

A restricted character sum vanishes exactly when its exponent word is balanced: \(n_0+n_1\omega+n_2\omega^2=0\) with integer \(n_i\) if and only if \(n_0=n_1=n_2\). This follows directly from \(1+\omega+\omega^2=0\) and the nonreality of \(\omega\).

Translate the four frequencies by the negative of the prescribed base. Order the points of \(A\), so that evaluating the three remaining frequency differences gives words \(u,v,w\). The six orthogonality conditions give balance of the three words and their three pairwise differences. Use the lemma to select two whose sum is also balanced, and call the corresponding functionals \(p,q\). They are linearly independent since \(q=p\) would have zero difference word and \(q=-p\) would have zero sum word. The four projective directions
\[
p,\quad q,\quad p+q,\quad p-q
\]
are all Fourier zeros of \(1_A\); so are their negatives. Thus every nonzero member of \(\operatorname{span}(p,q)\) is a Fourier zero and the nine characters indexed by this span are an orthogonal basis on \(A\).

The pushforward of \(1_A\) by \(x\mapsto(p(x),q(x))\) has zero Fourier coefficients except at zero. Since its total mass is nine, it is identically one on \(\mathbf F_3^2\). This proves conditions 2 and 3 from condition 1. Condition 2 trivially implies condition 1. The kernel of the map in condition 3 supplies the linear complement in condition 4, while a linear complement in condition 4 gives the quotient in condition 3. Condition 4 implies condition 5.

## 3. An arbitrary tiling already has a linear complement

Assume that \(A\) tiles \(V\). Translate both factors so they contain zero, and put \(W=\operatorname{span}(A)\). Since \(A\subset W\), the unique sum representations restrict to \(W=A\oplus B_0\) with \(B_0=B\cap W\). Apply [Szabó's Theorem 1](https://dergipark.org.tr/en/download/article-file/232910) to this normalized factorization of the elementary abelian group \(W\): a nine-element factor and its partner cannot both span the group. As \(A\) spans \(W\), \(B_0\) is contained in a hyperplane \(H\) of \(W\).

Choose a linear surjection \(j:W\to\mathbf F_3\) with kernel \(H\). For each \(s\in\mathbf F_3\) choose \(y_s\) with \(j(y_s)=s\) and write \(A_s=(A\cap(y_s+H))-y_s\). The same set \(B_0\) tiles \(H\) with each of the three \(A_s\). Each \(A_s\) has exactly three points since \(|B_0|=|H|/3\). The indicator of \(B_0\) on \(H\) is nonconstant, so there is a nonzero \(\lambda\in H^*\) with \(\widehat{1_{B_0}}(\lambda)\ne0\). The three tiling convolution identities \(1_{A_s}*1_{B_0}=1_H\) force \(\widehat{1_{A_s}}(\lambda)=0\) for every \(s\). Therefore \(\lambda\) takes each value once on each \(A_s\).

Extend \(\lambda\) to \(\Lambda\in W^*\). On the fiber \(A\cap(y_s+H)\), the values of \(\Lambda\) differ from the values of \(\lambda\) on \(A_s\) by a constant, so also occur once each. Thus \((j,\Lambda):W\to\mathbf F_3^2\) is a linear quotient bijective on \(A\). Extend both functionals to \(V\); the restricted bijection remains true, and translating \(A\) back preserves it. This proves condition 3 from condition 5.

## 4. The three possible maxima, all attained

When a nonzero Fourier zero \(b\) exists, \(0,b,-b\) supply three mutually orthogonal characters. If four exist, the theorem supplies nine and no orthogonal family can exceed the dimension nine. If there is no nonzero Fourier zero, no orthogonal pair exists.

For maximum three, in the slices \(z=0,1,2\) of \(\mathbf F_3^3\) take respectively
\[
 \{(0,0),(1,0),(0,1)\},\qquad
 \{(t,t):t\in\mathbf F_3\},\qquad
 \{(t,0):t\in\mathbf F_3\}.
\]
Projection onto \(z\) gives orthogonality of the three \(z\)-characters. The horizontal differences include all four projective directions: the first slice gives the two axes and direction \((1,-1)\); the second gives direction \((1,1)\). Differences from the \(z=1\) slice to the \(z=2\) slice have the form \((s-t,-t,1)\), covering all nine horizontal choices when the last coordinate is 1; negation covers the remaining slice. Consequently \(A-A=\mathbf F_3^3\), which rules out any translational tiling there because a tiling complement would have size three and any difference between two of its distinct members would cause a collision. In a larger ambient space the same example is supported in this three-space; a tiling there would restrict to a tiling in the three-space after normalizing the complement to contain zero. Thus this example has maximum three in every \(d\ge3\).

For maximum one, use the two \(x\)-lines \(y=0,1\) at \(z=0\) together with \((0,0,1),(0,1,1),(1,2,1)\). For a functional \(a x+b y+c z\) with \(a\ne0\), the six points at \(z=0\) contribute two to each residue. The last three give \(c,c+b,c+a+2b\); these can be distinct only if \(b\ne0\) and \(a=0\), a contradiction. For \(a=0,b\ne0\), the six lower points occupy two residues with three occurrences each, whereas the three upper points have distinct residues; balance again fails. For \(a=b=0\) the lower six already have one common value. This gives no nonzero Fourier zeros in \(\mathbf F_3^3\). Embedding in a higher-dimensional space preserves failure of balance, since a functional restricts to one on the three-space, possibly zero. Maximum nine is attained by a linear two-plane.

## Prior literature and scope

[Aten et al.](https://arxiv.org/abs/1509.01090) prove the finite-field Fuglede equivalence in \(\mathbf F_3^3\); [Fan and Zhang, Corollary 1.11(3)](https://arxiv.org/html/2408.12901) prove tiling implies spectrality in \(\mathbf F_3^4\). The [previous four-space classification](FactorFugledeF3FourClassification.md) handles the spectral implication at nine points there. The tiling implication above is a direct consequence of [Szabó (2008)](https://dergipark.org.tr/en/download/article-file/232910); it is not a new nonfull-rank factorization theorem.

For full spectra, the linear-complement existence assertion can also be extracted from prior complete matrix data. [Lampio, Östergård and Szöllősi, Table 2](https://arxiv.org/abs/1707.02287) list three monomial-equivalence classes of \(\mathrm{BH}(9,3)\) matrices. The three cocyclic representatives given by [Egan, Flannery and Ó Catháin, Section 6.1](https://arxiv.org/abs/1502.02717) therefore exhaust them: there is the tensor Fourier example, a circulant example, and its adjoint class. In the tensor example the coordinate functionals are available directly. For the circulant representative with exponent word \(000012021\), subtracting the zero-shift row from the one- and three-step cyclic shifts gives \(000111222\) and \(012012012\); these two words and their sum and difference are balanced. Taking the adjoint only conjugates and reverses the shifts. The balanced-pair property is preserved by row and column permutations and monomial phases: column phases cancel in row differences, and row phases add constants. The added content here is the sharp test with only four characters, the recovery of a spectrum from differences at any specified base, and the elementary connection to ordinary tiling stated with its factorization dependency. No claim is made for other cardinalities by this nine-point theorem.

## Six-point corollary of the earlier classification

For comparison, any six-point ternary spectral set has affine rank at least four. Restrict the spectrum to the affine span of the set (after translation); no two distinct orthogonal frequencies can restrict to the same functional there. If the affine rank is \(r\), translate the spectrum to contain zero and form the symmetric bilinear form on the \(r\)-dimensional dual space from \(Q(b)=\sum_{a\in A}b(a)^2\). The balance of every nonzero difference of frequencies gives \(Q=4=1\) in \(\mathbf F_3\) on those differences. For any four nonzero frequencies from the spectrum their Gram matrix is \(\frac12(I_4+J_4)\) by polarization; it is nonsingular, so \(r\ge4\). Rank four has exactly the one affine orbit from the [earlier classification](FactorFugledeF3FourClassification.md). Rank five is an affine simplex, and an affine projection onto the earlier six-point example, matching the six points bijectively, pulls its restricted characters back to a spectral basis. These exhaust all cases since six points have affine rank at most five. Neither rank can tile by cardinality.

Thus for \(d\ge5\) there are exactly two ambient affine classes of six-point spectral non-tiles. The rank-four class contains \(2\,729\,376\cdot3^{d-4}{d\brack4}_3\) sets, with \({d\brack4}_3\) the number of four-dimensional linear subspaces. The rank-five class contains \(3^d\prod_{i=0}^{4}(3^d-3^i)/6!\) sets, by counting ordered affine bases and forgetting their order. These are consequences of the previous six-point classification, not a replacement of that result.

The independent auxiliary check is `python3 verify_ternary_nine_point_rigidity.py`. It enumerates 1,485 normalized word pairs, checks the three examples directly, and verifies the cited representative's row calculation. No computation from this check is used by the proofs above.
