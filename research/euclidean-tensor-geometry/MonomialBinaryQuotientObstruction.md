# Binary quotient obstruction for two one-parameter monomial coloring cases

**Yongxian Zhang.** AI-assisted mathematical development and internal verification; no external review or priority claim.

For Davidson's named unresolved degree-twenty polynomial \(f_\ast\) in [§5, arXiv:2610.09474](https://arxiv.org/html/2610.09474v1#S5), the **entire** binary residue quotient graph has chromatic number at least 18. Thus no four-coloring of the original monomial Cayley graph can factor through this full binary quotient or any further quotient of it. This is a restriction on the method only; it does not give a chromatic lower bound of 18, five, or any other new lower bound on the actual Euclidean direction graph.

The degree-sixteen branch with \(Q(y)\equiv y^3+y+1\bmod2\) in the [companion theorem](MonomialFourColorsDegreeSixteen.md) has the same phenomenon, with a full binary quotient lower bound 10. For that degree the actual graphs nevertheless admit four colors by odd quotients or the large real norm argument in the companion theorem.

## Finite-field model and spectrum

For a monic integer minimal polynomial \(f\) of \(\alpha\), the full mod-two reduction of \(\mathbb Z[\alpha]\) is \(\mathbb F_2[x]/(\bar f)\), and the generator \(\alpha^j\) maps to \(x^j\). Suppose \(\bar f=g g^\vee\), where \(g\) and its reciprocal \(g^\vee=x^r g(1/x)\) are distinct primitive binary polynomials of degree \(r\). If \(\xi\) is the class of \(x\) modulo \(g\), the two ring projections are evaluation at \(\xi,\xi^{-1}\) inside the same field \(\mathbb F_q\), \(q=2^r\). The Chinese remainder theorem identifies the residue quotient with \(\mathbb F_q^2\), and primitivity identifies the signed step set (signs coincide in characteristic two) with
\[
S=\{(u,u^{-1}):u\in\mathbb F_q^\times\}.
\]

The resulting hyperbola Cayley graph is \((q-1)\)-regular. Its additive Fourier eigenvalues are indexed by \(a,b\in\mathbb F_q\):
\[
\lambda_{a,b}=\sum_{u\ne0}(-1)^{\operatorname{Tr}(au+b/u)}.
\]
The trivial eigenvalue is \(q-1\), and those with exactly one of \(a,b\) zero equal \(-1\). All remaining values are the exact Kloosterman sums \(K(c)=\sum_{u\ne0}(-1)^{\operatorname{Tr}(u+c/u)}\), \(c=ab\ne0\). The character formula follows by testing the adjacency operator against the additive characters of the binary vector space; the trace pairing is nondegenerate.

The [integer verifier](verify-monomial-binary-quotients.js) verifies each polynomial product and reciprocity, then directly verifies that \(x\) cycles through all \(q-1\) nonzero residues modulo \(g\). The latter proves that the residue ring is a field (all nonzero residues are invertible), and proves primitivity without a separate irreducibility routine. It then computes the exact Kloosterman minimum by polynomial-bit arithmetic for every \(c\ne0\).

| Case | \(g\), high-to-low binary coefficients | \(g^\vee\) | \(q-1\) | minimum | chromatic lower bound |
| --- | --- | --- | ---: | ---: | ---: |
| degree-sixteen exceptional parity | 101001101 | 101100101 | 255 | -29 | 10 |
| degree-twenty \(f_\ast\) | 10100100011 | 11000100101 | 1023 | -61 | 18 |

For completeness, if a regular \(N\)-vertex graph has valency \(k\) and least adjacency eigenvalue \(\lambda<0\), an independent class of density \(\delta\) has indicator quadratic form zero. Decomposition along the constant vector gives \(0\ge k\delta^2 N+\lambda\delta(1-\delta)N\), hence \(\delta\le-\lambda/(k-\lambda)\). This is the regular Hoffman ratio bound; summing over color classes gives \(\chi\ge \lceil1+k/(-\lambda)\rceil\), the last column of the table.

A quotient coloring would pull back to the monomial Euclidean graph, but its nonexistence does not push a lower bound back to the original graph. The binary obstruction is genuinely specific to factoring through mod two: the degree-sixteen result provides explicit examples where four colors still suffice by a different quotient.
