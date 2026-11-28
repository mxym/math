# Exact \(r\)-FWS classification by ambient trace duality

## 1. Maximum distance of every orbit

Put \(L=\mathbb F_{q^n}\) and \(\mathcal C_L(S)=\{\alpha S:\alpha\in L^\times\}\) for a \(k\)-dimensional \(\mathbb F_q\)-subspace \(S\). The subspace distance between two such spaces is \(d(S,T)=2k-2\dim(S\cap T)\). Common scaling is an isometry, so the distribution can be read from distances to \(S\). Repeated scalars defining the same codeword are counted only once in the code. For \(0\le r<k\), say \(r\)-FWS when the support of nonzero distances is exactly
\[
 \{2,4,\ldots,2(k-r)\}.
 \tag{1}
\]
This is the last-\(r\)-zeros convention of [CPZ, §7]; \(r=0\) is ordinary FWS.

Let \(1\le h\le n/2\) and \(U\le L\) have dimension \(h\). Then \(U\cap\alpha U\ne\{0\}\) if and only if \(\alpha\in U^\times/U^\times\), where \(U^\times=U\setminus\{0\}\). This quotient set has at most \((q^h-1)^2/(q-1)\) elements: the diagonal action of \(\mathbb F_q^\times\) on the ordered pairs is free and does not change the quotient. In particular its size is strictly less than \(q^n-1\), since \((q^h-1)^2<q^{2h}-1\le q^n-1\). Choose a nonzero \(\alpha\) outside it. The two translates are disjoint except for zero, distinct since \(h>0\), and at distance \(2h\). All stabilizers have already been included among the forbidden scalars, so the argument does not assume a full-length orbit.

Use the nondegenerate symmetric trace pairing \(\langle x,y\rangle=\operatorname{Tr}_{L/\mathbb F_q}(xy)\), and write \(U^\perp\) for its annihilator in \(L\). We recall the ambient dual isometry [CGLPZ, Proposition 4.1]. Namely
\[
 (\alpha U)^\perp=\alpha^{-1}U^\perp,\qquad
 \dim(S^\perp\cap T^\perp)=n-2k+\dim(S\cap T).
 \tag{2}
\]
The first follows by moving the scalar to the other entry of the pairing; the second comes from \((S+T)^\perp=S^\perp\cap T^\perp\). Thus ambient perpendicularity is an isometry between the two Grassmannians and bijects \(\mathcal C_L(S)\) with \(\mathcal C_L(S^\perp)\), preserving distances and their multiplicities. It also gives
\(d(U,\alpha U)=d(U^\perp,\alpha U^\perp)\) for the *same* multiplier \(\alpha\), since scaling turns \((U^\perp,\alpha^{-1}U^\perp)\) into \((\alpha U^\perp,U^\perp)\).

It follows that any orbit with \(1\le k<n\) has maximum distance \(2h\) for \(h=\min(k,n-k)\), not just the ambient upper bound without attainment. Consequently an \(r\)-FWS orbit has
\[
 r=k-h=\max(0,2k-n).
 \tag{3}
\]
For \(k\le n/2\) it must be ordinary FWS, and for \(k>n/2\) it is \(r\)-FWS if and only if \(S^\perp\) generates an ordinary FWS orbit of dimension \(h=n-k\). The empty-positive-spectrum cases \(k=0\) and \(k=n\) have one codeword and are not in (1); if the vacuous convention permits \(r=k\), each is a separate trivial orbit.

## 2. All families and their exact equivalence

For clarity, the result is for the full \(\mathrm{GL}_n(q)\) acting on codewords, not just the multiplicative normalizer. For \(T\in\mathrm{GL}_n(q)\), let \(T^*\) be its adjoint under the trace pairing. Then
\[
 (T U)^\perp=(T^*)^{-1}U^\perp.
 \tag{4}
\]
Indeed \(y\) is on the left exactly when \(T^*y\) annihilates \(U\). The operation is an involution on subspaces and sends a linear equivalence of codes in one dimension to a linear equivalence in the complementary dimension, in both directions. At fixed \(q,n,k\), ambient duality thus gives a bijection of the needed equivalence classes; no injectivity of a particular scalar parametrization is assumed.

For \(h=1\) there is just the orbit of all lines, or its dual consisting of all hyperplanes. For \(h\ge2\), use the two known FWS families of dimension \(h\) from [CPZ, Theorem 1.2], with their complete equivalences from [SO, Theorem 1.1]:

- **Powers over \(\mathbb F_q\).** \(U=P_h(\lambda)=\langle1,\lambda,\ldots,\lambda^{h-1}\rangle_{\mathbb F_q}\), with \(\lambda\) of degree \(t\ge2\). If \(t=n\), require \(2h\le n\); if \(t<n\), require \(2h-1\le t\). Two codes are equivalent exactly when
\[
 \mu=\frac{a\lambda^{q^j}+b}{c\lambda^{q^j}+d},
 \quad
 a,b,c,d\in\mathbb F_q,\quad ad-bc\ne0,\quad 0\le j<n .
\]
This automatically forces equal \(t\), including the proper-subfield boundary \(t=2h-1\).
- **Powers over the quadratic subfield with one extra \(\mathbb F_q\)-line.** Here \(n\) is even, \(K=\mathbb F_{q^2}\), \(h=2\ell+1\) with \(\ell\ge1\), and \([K(\lambda):K]>2\ell\). Take
\[
 U=\langle1,\lambda,\dots,\lambda^{\ell-1}\rangle_K\oplus\lambda^\ell\mathbb F_q .
\]
Two codes are equivalent exactly when
\(\mu=a+b\lambda^{q^j}\), \(a\in K,\ b\in K^\times,\ 0\le j<n\).

The families are inequivalent by [CPZ, Corollary 4.12]; their ordinary distance-two counts differ. Use \(\mathcal C_L(U)\) if \(k=h\), and \(\mathcal C_L(U^\perp)\) if \(k>h\). The equivalence tests are exactly the same for these latter codes by (4). Every permitted parameter in [CPZ] gives an \(r\)-FWS code this way, and all possibilities are covered. In particular for each \(1\le k<n\) the value in (3) is attained: if \(h\ge2\) a degree-\(n\) element gives the first family, and \(h=1\) was handled separately. This corrects the positive-\(r\) structural classification and settles its equivalence question without assuming [SS, Theorem 4.6].

## 3. Relation to the two printed families

The main difference from [SS, arXiv v1, Theorem 4.6] is not a change of parameter symbols. For \(k>n/2\), its printed families (as orbit codes, so the representative can be scaled) are precisely the ambient duals of the *first* ordinary family, with \(h=1\) understood as the trivial hyperplane orbit.

Write \(K'=\mathbb F_{q^t}\) for the field generated by the printed multiplier. In the printed direct sum, the nonzero vector \(b\) belongs to the displayed power space since \(m>0\); the direct sum and \(K'\)-linearity of \(\overline S\) therefore give \(bK'\cap\overline S=0\). Scaling by \(b^{-1}\) sets \(b=1\), as in the source proof, so the order of \(b\) in the printed auxiliary intersection condition is immaterial to this orbit comparison.

For the translation, set \(P_a(\lambda)=\langle1,\lambda,\ldots,\lambda^{a-1}\rangle_{\mathbb F_q}\) inside \(K'=\mathbb F_{q^t}=\mathbb F_q(\lambda)\). The known trace-power identity in \(K'\) is
\[
 P_a(\lambda)^{\perp_{K'}} = f'(\lambda)^{-1}P_{t-a}(\lambda),
 \quad 1\le a<t ,
 \tag{5}
\]
where \(f\) is the minimal polynomial. This follows by Lagrange interpolation: for \(j<t-1\), comparison of the leading coefficient in the interpolation formula for \(X^j\) gives \(\operatorname{Tr}_{K'/\mathbb F_q}(\lambda^j/f'(\lambda))=0\); basis products from the displayed spaces have exponent at most \(t-2\), and dimensions agree. This is [CPZ, Proposition 3.3; SO, Lemma 3.3].

When \(t=n\), equation (5) makes the dual a scalar multiple of \(P_k(\lambda)\), giving printed family (1) and \(r=2k-n\). If \(t<n\), transitivity of trace gives
\[
 P_h(\lambda)^{\perp_L}
    =\{z:\operatorname{Tr}_{L/K'}z\in f'(\lambda)^{-1}P_{t-h}(\lambda)\}.
 \tag{6}
\]
Since the relative trace is a nonzero \(K'\)-linear functional, choose \(b\in L\) with relative trace \(f'(\lambda)^{-1}\). The right side is
\(\ker\operatorname{Tr}_{L/K'}\oplus bP_{t-h}(\lambda)\).
Write \(l=n/t-1\), \(m=t-h\). Then \(k=tl+m\) and the \(K'\)-span is the entire field, \(2m\ge t-1\) is \(t\ge2h-1\), and \(2m+t(l-1)=n-2h=r\). These are the data of printed family (2). Conversely any such direct sum with \(K'\)-span \(L\) has \(\overline S\) a \(K'\)-hyperplane, the kernel of \(z\mapsto\operatorname{Tr}_{L/K'}(cz)\) for a suitable \(c\), by nondegeneracy. Its annihilator in \(L\) then lies in \(cK'\), and relative trace transitivity and (5) show that it is a scalar multiple of \(P_{t-m}(\lambda)\). Thus with \(h\ge2\) these printed forms cannot cover the ambient dual of the second ordinary family: dualize any proposed identification and apply the ordinary families' inequivalence. The \(h=1\) hyperplane orbit needs no parameter equivalences.

For an explicit alternative positive-\(r\) form of the omitted family, keep the quadratic \(K\) and \(\ell,\lambda\) from §2. Its representative in dimension \(k=n-2\ell-1\) can be written as
\[
 S=\{z\in L:\operatorname{Tr}_{L/K}(z\lambda^i)=0\ (0\le i<\ell),\
                       \operatorname{Tr}_{L/\mathbb F_q}(z\lambda^\ell)=0\}.
 \tag{7}
\]
The first \(\ell\) equations give a \(K\)-space of dimension \(n/2-\ell\), using the independent powers and nondegeneracy of relative trace. The last is one nonzero \(\mathbb F_q\)-linear condition on it, since the relative-trace functional for \(\lambda^\ell\) is nonzero there and has image \(K\). Thus \(S\) has exactly the advertised dimension and its \(K\)-span is that proper \(K\)-space (removing one \(\mathbb F_q\) dimension cannot reduce a \(K\)-span). Formula (7) is just the ambient trace annihilator, so it imports the entire second-family equivalence test.

## 4. Direct counterexample at \(q=2,\ n=8\)

For any prime power \(q\), take \(n=8\), \(K=\mathbb F_{q^2}\), and choose \(\lambda\) of degree four over \(K\) in \(L\). Set \(U=K\oplus\lambda\mathbb F_q\) and \(S=U^\perp\). For \(u\in K^\times\setminus\mathbb F_q^\times\), \(U\cap uU=K\). Also \(U\cap\lambda U=\lambda\mathbb F_q\) and \(U\cap\lambda^2U=\{0\}\), by independence of \(1,\lambda,\lambda^2,\lambda^3\) over \(K\). These give exactly the distances \(2,4,6\) for \(U\); by (2) the \(k=5\) orbit of \(S\) is \(r=2\) FWS.

In fact **every** distance-two multiplier is in \(K^\times\setminus\mathbb F_q^\times\). To see this, suppose \(\mu\notin K\) has a nonzero intersection vector, giving a quotient \(\mu=(a+b\lambda)/(c+d\lambda)\), with \(a,c\in K,\ b,d\in\mathbb F_q\). Any two such representations give a true polynomial equality on cross multiplication: the degree is at most two, less than four. The two linear or constant polynomials of a given quotient are coprime, since their ratio is nonconstant and they have degrees at most one. All representations therefore differ by a common nonzero multiplier in \(K\). At least one degree-one coefficient is nonzero in \(\mathbb F_q\), so this multiplier must be in \(\mathbb F_q^\times\). Hence the intersection has dimension at most one. The same multiplier classification holds for \(S\) by (2).

For each distance-two \(\mu\) we thus have \(t=[\mathbb F_q(\mu):\mathbb F_q]=2\). Printed family (1) would require \(t=n\). Printed family (2) requires \(Y=\langle S\rangle_K=L\), but \(S\subseteq K^\perp=\ker\operatorname{Tr}_{L/K}\) and its \(K\)-span is this proper \(K\)-hyperplane: \(S\) has \(\mathbb F_q\)-dimension five and the hyperplane has dimension six. Scaling the representative does not change these facts. Independently, the printed parameter expression has \(t=2,l=2,m=1\) and gives \(r=4\), not \(2\). There is no alternative choice of distance-two multiplier that brings the orbit into either family.

For the binary case one may take \(L=\mathbb F_2[X]/(X^8+X^4+X^3+X^2+1)\) and \(\lambda=X\bmod f\). The checkers verify irreducibility, construct \(\mathbb F_4\) and the trace dual exactly, and verify the distance counts \((1,2,36,216)\) at \(0,2,4,6\). The second checker uses a different tower field and trace computation. These are finite reproductions, not assumptions of the missing-family proof.
