# Dependencies, comparison and research screening

## Independent tensor theorems

The all-orders and cubic theorems are proved from elementary multilinear polarization, compactness of the finite-dimensional unit sphere and orthogonal group, the second derivative test, spectral diagonalization of a real symmetric matrix, Cauchy–Schwarz and Minkowski. They import no OpenAI theorem.

Prior framework: Ada Boralevi, Jan Draisma, Emil Horobeț and Elina Robeva, *Orthogonal and unitary tensor decomposition from an algebraic perspective*, arXiv:1512.08031, DOI 10.1007/s11856-017-1588-6. The primary PDF's Section 3.1, Lemma 11 and Proposition 12 establish the exact symmetric-cubic associativity/orthogonal-decomposition equivalence; the higher-order part describes the algebraic reduction. We inspected this primary text. That equivalence and the general algebraic variety viewpoint are acknowledged prior work.

Relevant further comparison: Arnab Auddy and Ming Yuan, *Perturbation bounds for (nearly) orthogonally decomposable tensors with statistical applications*, DOI 10.1093/imaiai/iaac033; and *Successive Rank-One Approximations for Nearly Orthogonally Decomposable Symmetric Tensors*, DOI 10.1137/15M1010890. Bibliographic records were located. Their full theorem-by-theorem comparison is pending. A forward perturbation estimate about a known decomposition is not automatically the inverse residual estimate here, but novelty cannot be inferred merely from that distinction.

## Nonlinear compatibility

Its exact zero-set proof generalizes the elementary Jacobian compatibility argument in the copied OpenAI-101 rigidity.tex. Matrix functional calculus and Gaussian Poincaré are standard inputs. The local coercivity uses a finite-dimensional compact smooth orbit and its explicitly calculated transverse derivative.

## Conditional entropy implication

The upstream pin is openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, family 101, dated 5 October 2026. The copied sources and scalar checker are byte-preserved. SOURCES.json records their paths, original URLs and hashes, and the original Apache-2.0 license is included.

The imported remainder R is exactly matrix.tex, Theorem mat:entropy-smooth, with its stated affine normalization and Sobolev regularity from transport.tex. Extension to nonsmooth log-concave densities imports the approximation assertion in approximation.tex. Equality compatibility is in rigidity.tex. The entropy theorem is not independently audited in full in this package. Copying its sources and replaying its scalar checker do not eliminate this dependency.

## Screening record and limits

The complete public catalogue was available at the pinned 372-family snapshot. We inspected the current repository and selected primary source interfaces; **we did not review the proofs of all 372 families**.

The earlier proposed Jacobsthal target h(k)=o(k²) is already covered by the source's displayed h(k) << k²/(log log(3k))², if that theorem is valid. Merely reproving that target would not be a further improvement.

For Mahler, a qualitative global modulus follows formally from uniqueness plus compactness of normalized convex bodies. Combining an existing local linear stability theorem with a valid global uniqueness theorem can also give a dimension-dependent global bound by compactness. A claimed new global stability project must check that overlap before asserting a major contribution.

The Fujita source explicitly excludes point and tangent separation. Its minimizing-center source was inspected at this interface; no first-jet extension was proved here. Ryser's sufficiently-large-prime construction does not by itself decide rank six. The existing balanced eight-dimensional Borsuk slice in mxym/math is explicitly an exclusion of one proposed witness, not a solution of the dimension-eight problem.

The present work moved from conditional entropy rigidity to an independent global tensor-defect problem. All results and gaps are stated in the manuscripts; screening observations are not mathematical breakthroughs.
