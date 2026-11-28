# Exact identity of progression-convolution laws over finite vector spaces

**Scope.** A deterministic identity test for two completely specified forward distributions. This does not infer a parameter or secret from observations, evaluate a real cryptographic target, or solve Ring-LWE. The result concerns the additive geometry, so it applies to the additive group of any supplied algebra over a prime field without requiring its multiplication to be used.

Let the binary-encoded prime \(p\), dimension \(d\), and lists of integers and vectors be supplied. Each law has the form
\[
        X=A+\sum_{i=1}^N U_i v_i\in G=\mathbb F_p^d,
        \qquad U_i\ {\rm independent\ uniform\ on}\ \{0,\ldots,L_i-1\},
\]
with \(A,v_i\in G\) and \(L_i\ge1\) binary integers. All wrapping multiplicities are part of the model. Arbitrary deterministic starts of individual progressions are included in \(A\).

**Theorem.** Equality of two such probability laws is decidable by a deterministic algorithm polynomial in the input bit length, with no bound on \(p\), \(d\), stride sizes, number of distinct directions, or length values. The algorithm computes and compares sparse signatures of the supplied lists and does not enumerate \(\mathbb F_p^d\) or its characters. In contrast, an exact point mass for the same class is \(\#\mathsf P\)-hard under polynomial-time counting Turing reductions already for \(p=2\), all lengths equal and odd in each input, and all steps supported on just two coordinates.

## 1. Eliminate the visible uniform directions

Let \(W=\operatorname{span}\{v_i:p\mid L_i\}\subseteq G\). A factor indexed by \(i\) with \(p\mid L_i\) is uniform on \(\langle v_i\rangle\). Its nonzero Fourier coefficients are exactly the characters trivial on that line. A factor with \(p\nmid L_i\) has all coefficients nonzero, as the nontrivial values come from an uncancelled geometric ratio. Independence therefore gives precisely \(\operatorname{Ann}(W)\) as the Fourier support. In particular \(W\) is identified by the law and is computed by ordinary linear algebra on the supplied list.

If the two \(W\)'s differ, the laws differ. Otherwise project both to the same quotient \(V=G/W\). Each original law is constant on the cosets of \(W\), so equality of the original laws is equivalent to equality in \(V\). Fix coordinates of \(V\) from the common ambient presentation of \(W\). Discard the now-zero strides, but retain the projected start \(A\). Every remaining stride is nonzero with \(p\nmid L_i\). If \(V=0\), there is nothing more to compare. In what follows use \(d'\) for its dimension.

## 2. The signature

For every projective line \(D\) in \(V\), retain the product
\[
             P_D=\prod_{i:v_i\in D\setminus\{0\}} L_i .
\]
These products are sparse, with default value one. For \(p=2\) the remaining signature consists just of \(A\) and these products.

For odd \(p\) define the signed, finitely supported counts on nonzero vectors
\[
  B(w)=\#\{i:(L_i\bmod p)v_i=w\}
                   -\#\{i:v_i=w\},\qquad w\in V\setminus\{0\}.
\]
Choose a common deterministic representative \(w\) of each pair \(\{w,-w\}\), for example the lexicographically smaller binary coordinate vector, and let \(\mathcal R\) be the representative set (used only on the sparse support). The additional parts are the folded counts and the natural center
\[
             B^+(w)=B(w)+B(-w)\quad(w\in\mathcal R),\qquad
             C=A+\tfrac12 \sum_i (L_i-1)v_i\in V .               \tag{1}
\]
Here \(1/2\) is in the prime field. Even the signs of the primitive Fourier values are forced once the line products, folded counts and center are specified.
The theorem asserts that two laws are equal exactly when all these signature parts, including their \(W\)'s, agree. A line is canonically represented by scaling its first nonzero coordinate to 1, so all dictionary keys and operations have polynomial bit length. Only supplied vectors, their scalar multiples, and their signs are inserted. The signatures do not need approximations to complex roots of unity.

## 3. Completeness, from character constraints back to sparse data

For a character parameter \(\ell\in V^*\), define the denominator
\(D(\ell)=\prod_{i:\ell(v_i)\ne0}L_i\). Let \(\zeta=e^{2\pi i/p}\). When \(p\) is odd, after the quotient all Fourier values are nonzero and
\[
 \widehat P(\ell)=
    \frac{\zeta^{\ell(A)}}{D(\ell)}
        \prod_{\substack{w\ne0\\\ell(w)\ne0}}
                           (1-\zeta^{\ell(w)})^{B(w)}.                \tag{2}
\]
The active exponent sum is zero, since every factor's numerator has active status exactly when its denominator does. The absolute norm of \(1-\zeta^u\) is \(p\) for \(u\ne0\); therefore \(|\mathrm{Norm}(\widehat P(\ell))|=D(\ell)^{-(p-1)}\). Equality of laws implies equality of their \(D(\ell)\) for every \(\ell\). For \(p=2\), replace (2) by the simpler \(\widehat P(\ell)=(-1)^{\ell(A)}/D(\ell)\), giving the same implication.

Here is why equality of denominators gives the line products exactly. Let \(M\) be the projective non-orthogonality matrix, with rows indexed by dual lines \([\ell]\), columns by primal lines \(D\), and \(M_{\ell,D}=1\) if \(\ell\) is nonzero on \(D\). For \(d'\ge2\), the diagonal of \(M^\mathsf TM\) is \(p^{d'-1}\), and the off-diagonal is \((p-1)p^{d'-2}\): nonzero prescriptions on one or two independent vectors give the corresponding counts on \(\ell\), divided by \(p-1\). Thus \(M^\mathsf TM\) is invertible over the reals, with positive diagonal-minus-off-diagonal. In dimension one \(M=[1]\). Taking logarithms only in the **proof**, the equations \(\log D(\ell)=\sum_D M_{\ell,D}\log P_D\) imply that the \(P_D\)'s coincide whenever the laws do. No such potentially immense matrix is created by the algorithm. For \(p=2\), the remaining character signs coincide iff the starts agree, completing that case.

For odd \(p\), set \(\Delta(w)=B(w)-B'(w)\). After matching denominators, equality in (2) forces at each \(\ell\), for each nonzero \(g\bmod\{\pm1\}\),
\[
        \sum_{w:\ell(w)=g}\Delta(w)
        +\sum_{w:\ell(w)=-g}\Delta(w)=0.                    \tag{3}
\]
This is the classical absolute cyclotomic-factor independence at prime order. For clarity, take the squared absolute value of the ratio, an algebraic equality in the real cyclotomic field, and apply all Galois automorphisms. The resulting log equations form the group convolution matrix of \(x\mapsto\log|1-\zeta^x|\) on \(\mathbb F_p^\times/\{\pm1\}\), up to inversion. Its trivial Fourier coefficient is \(\frac12\log p\), and its nontrivial even-character coefficients are \(-\frac12\tau(\overline\chi)L(1,\chi)\ne0\) by the primitive Gauss sum identity and Dirichlet nonvanishing. One obtains the formula by the Abel expansion of \(\log|1-t\zeta^x|\) and \(t\uparrow1\), as in the cyclic prime-power companion proof. Thus the log matrix is invertible and (3) follows. This is a necessity argument, not a numerical calculation of logarithms.

Put \(H(w)=\Delta(w)+\Delta(-w)\) on \(V\setminus\{0\}\) and \(H(0)=0\). Equation (3) says all its nonzero-value fibers under every \(\ell\) have zero mass. Its total mass is also zero, because each law's \(B\) has total sum zero. Hence every zero-value fiber has zero mass too. Taking any additive character of the projected one-dimensional function proves that every Fourier coefficient of \(H\) on \(V\) vanishes. This forces \(H=0\), equivalently the folded counts in (1) agree. It is this elementary simultaneous fiber argument that recovers the **full joint** signature, rather than running a cyclic test along exponentially many directions.

Now \(\Delta(-w)=-\Delta(w)\). For \(\ell(w)\ne0\) and \(w\in\mathcal R\), using
\(1-\zeta^{-\ell(w)}=-\zeta^{-\ell(w)}(1-\zeta^{\ell(w)})\)
shows that the quotient contribution from the pair is
\((-1)^{\Delta(w)}\zeta^{\Delta(w)\ell(w)}\). For \(\ell(w)=0\) both factors are omitted.

The residual sign is forced by the already matched line products. Fix a generator \(v_D\) of each projective line, and write \(w=t_wv_D\) for each nonzero \(w\in D\). Then
\[
 \prod_{w\in D\setminus\{0\}}t_w^{B(w)}=P_D\bmod p
\]
by the definition of \(B\): each input contributes its length residue. Dividing between the laws, and using that \(\Delta\) is antisymmetric, gives
\[
        1=\prod_{w\in D\setminus\{0\}}t_w^{\Delta(w)}
          =(-1)^{\sum_{w\in\mathcal R\cap D}\Delta(w)}
                           \quad\text{in }\mathbb F_p^\times .
\]
Since \(p\) is odd the integer exponent parity on every line is even. Thus the signs cancel for all \(\ell\), whose active pairs are exactly all or none of each line. Finally
\[
 \sum_{w\in\mathcal R}\Delta(w)w
          =\tfrac12\sum_{w\ne0}\Delta(w)w
          =\tfrac12\left[\sum_i(L_i-1)v_i-\sum_i(L_i'-1)v_i'\right].
\]
Terms with \(\ell(w)=0\) do not affect the phase exponent even when included in this sum. Therefore the remaining ratio in (2) is precisely \(\zeta^{\ell(C-C')}\). Equality at all \(\ell\) is now equivalent to \(C=C'\). Conversely the matched signature yields equality by these same identities, so all character values and the laws agree.

The center has an independent interpretation: reflecting each uniform index shows the law is symmetric about \(C\). After taking the quotient there are no nonzero translation periods, by full Fourier support. Two distinct centers would yield such a period because \(p\) is odd. This also explains why no pair-dependent choice of phase representative is needed in the signature.

## 4. Point mass can be hard at fixed \(p=2\)

Take a bipartite graph with \(m\) vertices on each side and \(N\) edges. Each edge gives a vector on the \(2m\) vertex coordinates, with 1 at its two endpoints. Consider the supplied progression convolution on \(\mathbb F_2^{2m}\) with these strides and common length \(2k+1\) at integer query parameters \(k=1,\ldots,N+1\). The parity of each integer index is 1 with probability \(k/(k+1+k)\), and 0 with probability \((k+1)/(k+1+k)\). The exact forward probability at the all-ones vector, divided by \(((k+1)/(2k+1))^N\), is the evaluation at \(k/(k+1)\) of
\[
       \sum_{\substack{S\subseteq E:\ {\rm all\ vertex}\\
                                   {\rm degrees\ in\ }S\ {\rm odd}}}
                           z^{\,|S|}.
\]
From \(N+1\) rational evaluations one interpolates this degree-\(N\) polynomial in polynomial bit time. A chosen edge set in its degree-\(m\) coefficient has degree at least 1 at all \(2m\) vertices and total degree \(2m\); hence each vertex has degree exactly 1, i.e. it is a perfect matching. This reduces the zero-one permanent to the exact forward probability query, as claimed. It gives no hardness result for approximation of the point mass, and concerns no cryptographic target.

## Source comparison and scope

The cyclic prime-power companion theorem handles one cyclic coordinate with arbitrary valuation and uses compressed cyclotomic cosets. At prime order its one-character absolute-value independence is classical; see [Dasgupta, *Factorization of p-Adic Rankin L-Series*](https://sites.math.duke.edu/~dasgupta/papers/Factorization.pdf), §4.2. The full-vector novelty of the present argument is the sparse inverse implication through linear fibers, the projective non-orthogonality argument for denominators, and the forced sign via line products reduced modulo the prime. The finite hyperplane transform is standard; see [Grinberg, *The admissibility theorem for the hyperplane transform over a finite field*](https://www.sciencedirect.com/science/article/pii/0097316590900633). Neither operation requires building a dense transform. The point-mass reduction uses [Valiant's permanent theorem](https://www.cs.bu.edu/faculty/gacs/courses/cs535/papers/Valiant_permanent.pdf). These are exact claims for fully specified arithmetic progressions. They do not say that marginal equality along an arbitrarily chosen subset of lines suffices, that a composite-modulus module behaves identically, or that any unknown noise or signal is recoverable.
