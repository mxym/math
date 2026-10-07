# Pinned dependencies and proof scope

The supplement uses the entry005 manuscripts in the public repository
[`mxym/math`](https://github.com/mxym/math), pinned to commit
[`6785c1c830f8e19e2eb07b0bb89f4d475a8b154a`](https://github.com/mxym/math/commit/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a).
The exact byte identifiers are recorded in [DEPENDENCIES.json](DEPENDENCIES.json).
The supplement has a complete written proof and has passed independent model
mathematical audits. Human peer review and proof-assistant formalization remain
outside that verification scope. This dependency record fixes the statements
being used; it does not certify them by a numerical test.

## Manuscript pins

| Source at the pinned commit | SHA-256 of the complete Markdown file |
| --- | --- |
| [v2: Projection-volume calculus for joins and Cartesian products](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v2/paper.md) | `8b7ad76a8a4b96ff40d43e9f9c3e7f4fe494dbadcf82bbdc114f980971ffb430` |
| [v3: Random-determinant rigidity, sharp symmetric cone bounds, and spectral nonattainment](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v3/paper.md) | `7827af9bbd122acd0852778c22ba94dbc9c80b729b5502f2944574f8b9e5121a` |
| [v4: Equality in the symmetric projection-cone bound](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v4/paper.md) | `19eb5aa0c79e34280cc3619cf40c1bea7acda6f6ec1161b05fbb6bf2308fda81` |

## Statements used directly

The quantities are normalized by
\[
R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad
a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1.
\]
Here \(\Pi K\) is the projection body, and \(\mathcal P K\) is a pyramid
with base \(K\). The interval convention is \(\Pi I=[-1,1]\).

| Input | Exact source location | Use in the supplement |
| --- | --- | --- |
| Affine invariance of \(R\) and \(a\) | v2 Lemma 2.1, lines 74–104; extension in §5, lines 219–227 | Affine normalization and the definition of distance to affine shapes. |
| \(a(A\times B)=[r a(A)+s a(B)]/(r+s)\) for factors of dimensions \(r,s\) | v2 §3, lines 139–153; arbitrary-body extension in §5 | The converse equality construction and products of equality factors. |
| Pyramid formula \(R(\mathcal P K)=(1+1/d)^d(1+a(K))R(K)\) | v2 §3, lines 155–171; §5, lines 219–227 | Agreement of the facet calculation with the invariant for general convex bodies. |
| Cone-law definition and determinant representation | v3 §4 and Proposition 4.1, lines 167–190, equation (4.2) | For \(\nu_K=(u/h_K(u))_*[h_K\,dS_K/(d|K|)]\), the identity \(a(K)=B(\nu_K)/[(d+1)A(\nu_K)]\). The proof there includes the weak-continuity passage from polytopes to arbitrary bodies. |
| Balanced Rademacher estimate | v3 Lemma 6.1, lines 258–277, equation (6.1) | On \(\sum |c_i|=1\), \(\max |c_i|\le1/2\), the sign average is at most \(1/2\). The supplement proves its quantitative refinement. |
| Sign averaging and the upper bound | v3 Theorem 6.2 and Corollary 6.3, lines 279–308, equation (6.2) | The exact upper deficit \(\delta=1/2-a(K)\ge0\), and the zero-cost cases in dimensions one and two. |
| Complete equality class | v4 Theorem 1.1, lines 22–46, with proof in §7, lines 346–389 | At \(\delta=0\), equality holds exactly for affine products of centrally symmetric factors of dimensions one or two. |

In the determinant representation,
\[
A(\nu)=\mathbb E|\det(X_1,\ldots,X_d)|,\qquad
B(\nu)=\mathbb E\left|\det\begin{pmatrix}
X_1&\cdots&X_{d+1}\\1&\cdots&1
\end{pmatrix}\right|.
\]
These definitions are in v3 §2, lines 58–70. The distinction between the
spherical cone-volume measure and its radially rescaled probability law is
essential: the determinant expectations above use the latter.

## Exact antecedents that are replaced quantitatively

The complete v4 proof was read, including its treatment of arbitrary measures.
The following v4 statements explain the architecture of the supplement, but
none of them supplies an effective rate on its own.

| v4 location | Exact mechanism | Quantitative replacement in the supplement |
| --- | --- | --- |
| Lemma 2.1, lines 65–124 | Rademacher equality has two branches: support of size at most three, or a coefficient of half the total absolute mass. | A robust coefficient inequality retaining both branches. |
| Lemmas 3.1 and 4.1, lines 139–198 | Exposedness almost everywhere eliminates long circuits at exact equality. | A contact-slab surface-area estimate controls near-half-mass long circuits without assuming a quantitative exposedness margin. |
| Lemma 5.1, lines 204–286 | Fubini and a matching of basis indices give a direct sum of lines and planes. | A conditioned basis and a quantitative matching estimate control expected distance to a union of one- and two-dimensional blocks. |
| Lemma 6.1, lines 292–344 | Block-supported surface area measure forces an exact Cartesian product. | A support-function and mixed-volume argument turns approximate block support into a Banach–Mazur containment. |
| Theorem 8.4, lines 423–479 | Compactness gives a qualitative modulus in each fixed dimension. | An explicit dimension-dependent power estimate proved by the quantitative gates. The supplement does not infer a rate from compactness. |

The half-mass branch is not dispensable. The four-point boundary-law guard in
v4 §9, lines 481–512, shows that an arbitrary even boundary law can have zero
Rademacher defect without the convex-body equality decomposition. The
supplement uses the contact geometry of \(\nu_K\) at this gate.

## Classical inputs

The proof also uses the symmetric form of John's ellipsoid theorem;
almost-everywhere regularity of convex boundaries; the area formula for
coordinate projection of a rectifiable boundary; the Gauss-map definition of
surface area measure; the divergence theorem; the first mixed-volume formula;
and Minkowski's first inequality. These standard theorems apply to general
full-dimensional convex bodies. They are analytic inputs, not consequences of
the exact finite checks. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*,
second expanded edition, Cambridge University Press, 2014, is a general
reference for the convex-geometric inputs. The primary cone-volume and
stability sources and their distinct hypotheses are compared in
[LITERATURE.md](LITERATURE.md).

## Related results outside the dependency chain

At the same pinned public commit,
[`notes/quantitative-projection-simplex-stability`](https://github.com/mxym/math/tree/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/notes/quantitative-projection-simplex-stability)
studies the lower-end deficit \(a(K)-1/(d+1)\), with a simplex target.
[`entry005 v5`](https://github.com/mxym/math/tree/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/preprints/005-simplex-product-optimum/v5)
studies balanced homogeneous spectral recursions. Neither is a proof input for
the symmetric upper-end estimate toward the entire one-/two-dimensional
product equality class. The distinct deficits, equality mechanisms, and
targets must not be interchanged.

## Reproduction and rights

The new exact-check scripts are self-contained and require only Python's
standard library. Optional inherited-check replay is documented separately
by [code/dependency-inputs.json](code/dependency-inputs.json); it requires an
explicit external checkout and verifies its pinned source bytes before
running. Outputs belong in a separate build directory. No inherited
manuscript or checker source is copied into this supplement merely to satisfy
an undocumented local path.

The repository's pinned
[NOTICE.md](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/NOTICE.md)
identifies inherited OpenAI/math material at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` and retains its Apache-2.0 license in
[`third_party_licenses/openai_math_LICENSE.txt`](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/third_party_licenses/openai_math_LICENSE.txt).
That upstream license is not a blanket license for separately authored
material. This package does not assign a new license to its newly written
manuscript or exact-check sources.
