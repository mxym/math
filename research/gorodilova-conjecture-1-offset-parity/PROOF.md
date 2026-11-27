# Proof of Gorodilova's offset parity conjecture

All vector spaces, tensor operations and sums in the proof are over \(\mathbb F_2\), unless otherwise indicated. Let \(V,W\) be binary vector spaces of the same dimension \(n\), and \(F:V\to W\) a quadratic APN map. The source defines “quadratic” to mean algebraic degree exactly two, so for its odd-dimensional Conjecture 1 the range starts at \(n=3\).

Denote the alternating bilinear polar form by
\[
 \beta_F(a,x)=F(a+x)+F(a)+F(x)+F(0).
\]
It induces a linear map \(B_F:\Lambda^2 V\to W\), defined by \(B_F(a\wedge x)=\beta_F(a,x)\). For \(a\ne0\), the derivative \(F(x+a)+F(x)\) is the map \(\beta_F(a,x)\) translated by \(F(a)+F(0)\). The linear map \(x\mapsto\beta_F(a,x)\) has kernel \(\langle a\rangle\): \(0,a\) are in it and APN prohibits more. Thus it has a unique nonzero normal \(\pi(a)\in W^*\). Put \(\pi(0)=0\). This is the source's \(\Phi_F\) under the coordinate dot product. In particular its auxiliary function is
\[
 \varphi_F(a)=
 \begin{cases}
  \pi(a)(F(a)+F(0)),&a\ne0,\\
  1,&a=0.
 \end{cases}
\]
The rule at the origin is part of the definition in the original paper, not inferred from a derivative in direction zero.

## 1. Plane fibers and a linear splitting

For a 2-dimensional linear subspace \(R=\langle a,x\rangle\), let \(p_R=a\wedge x\) for any basis. It is independent of the basis since invertible binary 2-by-2 matrices have determinant one. For each \(v\ne0\) in \(W\), set
\[
 \mathcal R_v=\{R:B_F(p_R)=v\},\qquad
 M_v=\{a\in V:\pi(a)(v)=0\}.
\]
The nonzero points of \(M_v\) partition into the triples \(R\setminus\{0\}\) for \(R\in\mathcal R_v\). In fact a nonzero \(a\) belongs to \(M_v\) exactly when \(v\) lies in the image of \(\beta_F(a,\cdot)\). The two solutions then have the form \(x,x+a\) with \(x\notin\langle a\rangle\), as \(v\ne0\). They specify one and the same \(R\). Conversely, each of the three nonzero points of \(R\) has a partner in \(R\) giving the same polar value \(v\), by alternation and bilinearity. This also proves the required disjointness.

If \(n\) is odd, \(\pi\) bijects \(V\) with \(W^*\): for each nonzero \(\lambda\in W^*\), the scalar alternating form \(\lambda\circ\beta_F\) on an odd-dimensional space has nonzero radical. Each nonzero \(a\) in it has \(\pi(a)=\lambda\). This proves surjectivity, and the two spaces have equal size. Therefore \(|M_v|=2^{n-1}\) and
\[
 |\mathcal R_v|=(2^{n-1}-1)/3
\]
is odd for each \(v\ne0\). Equivalently, oddness of the plane count is the only parity input needed below. In even dimension \(n\ge4\) the same oddness is proved separately in Section 4.

Assume now \(n\ge3\). Define \(P_F(0)=0\) and, for \(v\ne0\),
\[
 P_F(v)=\sum_{R\in\mathcal R_v}p_R \ \in\ \Lambda^2 V.
\]
To see that this is linear, fix a basis \(e_1,\ldots,e_n\) of \(V\). In the corresponding exterior basis the coefficient on \(e_i\wedge e_j\), for \(i<j\), of \(p_R\) is
\[
 a_i x_j+a_j x_i=\sum_{y\in R}y_i y_j
\]
by summing the points \(0,a,x,a+x\). By the partition, the coefficient of \(P_F(v)\) is therefore \(\sum_{y\in M_v}y_i y_j\). With \(1_{M_v}(y)=1+\pi(y)(v)\) and \(\sum_{y\in V} y_i y_j=0\) in dimension at least three, this coefficient is
\[
 h_{ij}(v),\qquad
 h_{ij}:=\sum_{y\in V} y_i y_j\,\pi(y)\ \in W^*.
\]
The origin appears in \(M_v\) but contributes zero to the sum. The formula also holds at \(v=0\), where \(P_F(0)=0\) and \(h_{ij}(0)=0\). Thus \(P_F\) is a linear map \(W\to\Lambda^2 V\). Since each summand maps to \(v\) and the number of summands is odd, \(B_F P_F\) is the identity on \(W\).

## 2. Trace contraction

Two more moment identities remove the affine part. In odd dimension \(\sum_{a\in V}\pi(a)=0\) by bijectivity (and \(n\ge3\)). In even dimension see Section 4. For each coordinate \(i\) and nonzero \(v\),
\[
 \left(\sum_{a\in V}a_i\,\pi(a)\right)(v)
 =\sum_{a\in V}a_i+\sum_{a\in M_v}a_i=0.
\]
The first sum is zero because \(n\ge2\); the second is zero because each disjoint nonzero plane triple sums to zero. The equality also holds for \(v=0\). Hence \(\sum_a a_i\pi(a)=0\). In particular, adding any affine map to \(F\) makes no contribution to the sum \(\sum_a \pi(a)(F(a))\).

Write \(Q_F(x)=\sum_{i<j}c_{ij}x_i x_j\) for the homogeneous quadratic part of the square-free ANF, with \(c_{ij}=\beta_F(e_i,e_j)\). The endomorphism \(B_F P_F\) is the sum of the rank-at-most-one endomorphisms \(v\mapsto h_{ij}(v)c_{ij}\). The trace of this rank-one expression is \(h_{ij}(c_{ij})\), also when it vanishes. Therefore
\[
 \begin{aligned}
 n\bmod 2
 &=\operatorname{tr}(I_W)=\operatorname{tr}(B_FP_F)\\
 &=\sum_{i<j}h_{ij}(c_{ij})
 =\sum_{a\in V}\pi(a)(Q_F(a))
 =\sum_{a\in V}\pi(a)(F(a)+F(0)).
 \end{aligned}
\]
More generally, for any quadratic map \(G:V\to W\) the same expansion gives \(\sum_a \pi(a)(G(a))=\operatorname{tr}(B_G P_F)\). In the parity application the second map is \(G=F\).

## 3. Consequence for the offset

The value at zero in the last display is zero, whereas \(\varphi_F(0)=1\). Thus
\[
 \operatorname{wt}(\varphi_F)\equiv 1+\sum_a\pi(a)(F(a)+F(0))
 \equiv 1+n\pmod2.
\]
The coefficient of the square-free monomial of degree \(n\) of a Boolean function is exactly the sum of its \(2^n\) truth values modulo two: all smaller monomials take the value 1 an even number of times. For odd \(n\), \(\deg \varphi_F<n\). This is Conjecture 1 of the cited paper, with its exact associated-function convention.

A direct interpretation is that the number of unordered distinct input pairs with equal output has parity \(n+1\pmod2\). In fact APN gives at most one such pair for each nonzero difference, and \(\varphi_F(a)=0\) precisely when difference \(a\ne0\) supports a collision. Therefore that number is \(2^n-\operatorname{wt}(\varphi_F)\), and it has the same parity as the weight.

## 4. Even dimensions, for the uniform formula

The even-dimensional conclusion comes from Proposition 1 of the source. Here is also an elementary justification of the plane-count parity and the zero moment, so the same trace proof applies for even \(n\ge4\).

Fix a basis of \(V\), and for \(\lambda\in W^*\) let \(A_\lambda\) be the alternating matrix of \(\lambda\circ\beta_F\). For \(\lambda\ne0\), \(\pi^{-1}(\lambda)\) consists of the nonzero vectors in \(\ker A_\lambda\); it has odd size if the matrix is singular and is empty otherwise. Let \(p(\lambda)\) be the sum over perfect matchings of the \(n\) indices of the product of the \(n/2\) matched entries of \(A_\lambda\). Then \(\det A_\lambda=p(\lambda)^2\): in the determinant expansion all permutations with a cycle of length greater than two cancel in pairs with the reverse of the first such cycle (using symmetric entries and the least index on such cycles to choose it); a fixed point gives a zero diagonal entry, and the remaining permutations are the matchings. Since \(\lambda\) has binary coordinates, \(1+p(\lambda)\) is the singularity indicator and \(p\) has Boolean degree at most \(n/2\). Therefore
\[
 \sum_{a\in V}\pi(a)=\sum_{\lambda\in W^*}\lambda\,[1+p(\lambda)]=0.
\]
Indeed the coordinate polynomials of the summand have degree at most \(n/2+1<n\), and the additional term at \(\lambda=0\) is zero. It follows that for \(v\ne0\) the integer \(|M_v|\) is even, since \(|M_v|\equiv 2^n+\sum_a\pi(a)(v)\). The partition \(|M_v|=1+3|\mathcal R_v|\) then forces \(|\mathcal R_v|\) odd as needed.

For \(n=2\), the polar value \(c=\beta_F(e_1,e_2)\ne0\) by APN and the unique nonzero normal annihilating \(c\) is the same for all nonzero directions. Since the quadratic part is \(c x_1x_2\), the function \(a\mapsto\pi(a)(F(a)+F(0))\) is simply that fixed normal applied to the linear ANF part, including at zero. Its weight is even, so changing the stipulated origin to 1 yields odd weight. This gives the uniform \(n+1\) rule in the smallest even dimension as well.
