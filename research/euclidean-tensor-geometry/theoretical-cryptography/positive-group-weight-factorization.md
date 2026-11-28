# Exact product factorization of compact positive group weights

This note is about explicit mathematical input, namely finite abelian groups, homomorphisms, and small tables of positive rational numbers. It identifies exactly when the represented weight decomposes into independent blocks, even when factors cross the eventual blocks and cancel. It does not learn a distribution from samples or solve any cryptographic instance.

## 1. Problem and result

Let \(G=\prod_{j=1}^r G_j\) be finite abelian, written additively, with invariant-factor coordinates for each supplied group \(G_j\). The numerically enormous Cartesian product need not be enumerated. The input gives surjective homomorphisms \(A_i:G\to H_i\) in invariant-factor coordinates and complete positive rational tables \(w_i:H_i\to\mathbb Q_{>0}\). Put
\[
                         W(x)=\prod_{i=1}^m w_i(A_i x).                 \tag{1}
\]
The bit length \(L\) includes the full tables, binary integer orders, and the homomorphism matrices. Translated factors can be absorbed into reindexing their explicit tables. A claim about a non-surjective presented map can instead be formulated with its image table, but surjectivity is the input convention here.

There is a deterministic polynomial-in-\(L\) algorithm to find the finest partition \(\mathcal P\) of the supplied blocks \(G_1,\ldots,G_r\) over which \(W\) is a product: \(W(x)=\prod_{B\in\mathcal P} W_B(x_B)\), for positive block functions. Equivalently, it gives the finest partition over which the probability proportional to \(W\) is independent. The algorithm accounts for exact cancellation; it does not simply take the union of formal input factor scopes.

There is a second result on \(G=\mathbb F_p^N\). Even if a new invertible \(\mathbb F_p\)-linear system of coordinates is allowed, one can deterministically find the finest intrinsically nonuniform independent subspace decomposition of (1) in the same bit complexity. It is canonical on the quotient by directions where \(W\) is constant, up to block order and coordinates within each block. These are computational assertions about given function descriptions, not statistical identification.

For either form, if each resulting block needs at most polynomially many points to enumerate, its exact normalization sum, and hence that of \(W\), is polynomial-time. A group factor on which \(W\) is constant may be summed out just by its cardinality.

## 2. Block factorization and cycle classes of frequencies

All characters use the normalized Fourier convention \(\widehat f(\gamma)=\mathbb E_x f(x)\overline{\gamma(x)}\). Write \(F=\log W\), with the ordinary real logarithm. By character orthogonality, a product representation over a proposed partition is equivalent to saying that each nonzero-frequency character with \(\widehat F(\gamma)\ne0\) is supported inside one block of the partition. The forward direction follows by taking logarithms. For the reverse direction assign each nonconstant Fourier term to its single block; the conjugate terms belong to that same block, so the resulting functions are real. Exponentiate the resulting sum. The zero frequency can be absorbed into any block. This argument proves existence and uniqueness of the finest partition as the connected components of the hypergraph of active character supports.

Only characters in
\[
                      \bigcup_i A_i^*(\widehat H_i)                     \tag{2}
\]
can occur. They can be enumerated by listing the dual elements of each \(H_i\), taking their pullbacks on the given generators of \(G\), and deduplicating. This uses at most \(\sum_i |H_i|\) frequencies and polynomially many bit operations in the stated representation. Each candidate character has order \(h\le\max_i|H_i|\). Surjectivity makes \(A_i^*\) injective. Membership of \(\gamma\) in \(A_i^*(\widehat H_i)\) is equivalent to that of \(\gamma^a\) whenever \(\gcd(a,h)=1\).

For our purpose, one need not decide whether an individual complex number \(\widehat F(\gamma)\) vanishes. Group together the generators of each cyclic subgroup of characters in (2). They all have the same support on \(G_1,\ldots,G_r\), because exponentiation by a unit modulo \(h\) preserves whether a given restriction is trivial. It is enough to decide exactly whether *all* the generators in that class are inactive. Different cyclic subgroups are disjoint as generator classes. They can be named by, for example, the lexicographically least encoding among the at most \(h\) generators. The trivial class does not affect the partition.

## 3. Exact groupwise zero tests without logarithms

Fix a cyclic class of order \(h>1\) and choose its generator \(\gamma\). For each \(i\) whose pullback contains \(\gamma\), let \(\eta_i\) be the unique preimage character. For \(y\in H_i\) let \(b_i(y)\in\mathbb Z/h\mathbb Z\) be defined by \(\eta_i(y)=e^{2\pi i b_i(y)/h}\). All these integer phases are determined by the given invariant-factor coordinates. Set
\[
  s_b=\sum_{i:\gamma\in A_i^*(\widehat H_i)}
              \frac{1}{|H_i|}\sum_{\substack{y\in H_i\\b_i(y)=b}}\log w_i(y).
\]
The Fourier coefficient at \(\gamma^a\), for \(\gcd(a,h)=1\), is \(\sum_{b=0}^{h-1}s_b e^{-2\pi iab/h}\). This follows by averaging each pullback term over a uniform preimage fibre; terms whose dual image does not contain \(\gamma^a\) contribute zero.

Let \(c_h(k)=\sum_{a\bmod h,\gcd(a,h)=1}e^{2\pi i a k/h}\) be the Ramanujan sum. Elementary Möbius inversion in the coprimality indicator gives the integer formula
\[
                     c_h(k)=\sum_{d\mid\gcd(h,k)}d\,\mu(h/d).           \tag{3}
\]
In particular \(|c_h(k)|\le h\). Up to the factor \(1/h\), the cyclic convolution of \(s\) by \(c_h\) is the Fourier projection onto the primitive frequencies modulo \(h\). Thus this cyclic class is inactive iff
\[
                    \sum_{b=0}^{h-1} c_h(j-b)s_b=0\quad(0\le j<h).      \tag{4}
\]
This test works also for composite \(h\); replacing (4) by the requirement that all \(s_b\) are equal would be too strong then.

Let \(D\) be the least common multiple of the contributing \(|H_i|\). The bit length of \(D\) is at most the sum of their bit lengths. Multiplying each equation (4) by \(D\), and exponentiating only symbolically, yields the exact rational identity
\[
        \prod_{i,y} w_i(y)^{
                    (D/|H_i|)c_h(j-b_i(y))}=1.                          \tag{5}
\]
One must not materialize these powers: the numerical value of \(D\) can be very large. Instead use ordinary product-of-exponentials equality, with rational bases split into integer numerators and denominators. Signed exponents are written in binary. No factoring of those integer bases or equality test on approximated logarithms is needed.

For completeness, the gcd-free equality argument is as follows. Merge identical bases and omit \(1\). If distinct bases \(a,b>1\) have \(g=\gcd(a,b)>1\), replace \(a,b\) by the nontrivial members of \(g,a/g,b/g\), absorbing the first two exponents into the sum at \(g\), and keep merging identical bases. The sum of base-2 logarithms of the distinct present bases drops by at least \(\log_2 g\ge1\), ignoring any further decrease by merging. It starts at most the input bit length of the bases. Hence at most polynomially many refinements occur, and each may increase exponent lengths by only a constant number of bits from a bounded number of merges. At the end all bases are pairwise coprime, and the product equals one iff each remaining signed exponent is zero. Including bases whose current exponent is zero is harmless. This gives a straightforward polynomial bit implementation of (5).

The number of tests \(j\) per class, and trial enumeration of divisors or prime factors of \(h\) in (3), are polynomial because \(h\) is bounded by an actual explicit table size. The computation of \(D\), signed exponents and phases uses only bounded bit-length integer arithmetic before the equality test. Thus the full hypergraph, after removing precisely the inactive cyclic classes, is obtained in deterministic polynomial bit time.

## 4. Finding an intrinsic linear product, not only supplied block cuts

Now let \(G=\mathbb F_p^N\). Identify a character with its vector in the dual via the usual dot pairing and the \(p\)-th root of unity. Each nontrivial cyclic class consists of the nonzero elements of one dual line. If the class is active, take one nonzero vector on its line even if its own Fourier coefficient happens to vanish. A linear decomposition permits the whole line or excludes the whole line from each dual block. Let \(S\) be the span of the active lines.

Given a direct-sum representation \(S=\bigoplus_j S_j\) with each active line in one summand, the logarithmic Fourier terms split over the corresponding primal block coordinates. Conversely an independent decomposition in linear coordinates gives such a covering of the active lines by dual summands. Upon restricting to \(S\), each nonzero summand is the span of the lines it covers. Any leftover directions in the primal annihilator \(S^\perp\) carry constant weight; they do not generate additional nonuniform factors.

The finest such partition of the active lines is the direct-sum decomposition of their linear matroid. A direct proof and algorithm uses any basis \(v_1,\dots,v_k\) from the active lines. Express every nonbasis line representative in this basis. Join the indices of its nonzero coefficients into one hyperedge. Each connected component \(C\) of this graph yields an independent block \(\operatorname{span}\{v_j:j\in C\}\), and every line fits one of these blocks. Conversely in any direct-sum decomposition satisfying the line condition, the basis vectors in each summand form a basis there: they are globally independent, and the sum of the dimension upper bounds is exactly \(k\). Therefore every nonbasis line must use basis indices from a single proposed summand, so every connected component is kept together. This proves fineness and its independence of the original basis. All steps are polynomial in the number of candidates and the binary representation of \(p\). Dual-basis linear algebra supplies actual coordinates on the primal quotient and any chosen complement. The case \(S=0\) is just constant weight.

## 5. Exact evaluation, examples, and prior scope

For a product across \(k\) permitted blocks, the original unnormalized function has the exact identity
\[
      W(x)=W(0)^{1-k}\prod_{B} W(x_B,0_{-B}),\qquad
      \sum_{x\in G} W(x)
          = W(0)^{1-k}\prod_B\sum_{x_B} W(x_B,0_{-B}).                   \tag{6}
\]
It holds as written also after a linear coordinate change. Each table evaluation on the right is the product of the explicit original factor values at one argument, with polynomial bit length. Common denominators for the sums can be bounded by the product of denominators of the original tables; all integer lengths remain polynomial when the blocks are explicitly enumerated. For a constant block multiply its value by its cardinality rather than enumerating it. This is a positive tractability criterion with a certifiable structural condition, not a claim about the case of large nonconstant blocks.

Two examples illustrate why the tests are not merely formal scope analysis.
* On the group \(\mathbb Z/6\mathbb Z\) decomposed into its order-2 and order-3 coordinates, the full positive table \(w(z)=2^{(-1)^z}3^{1_{\{z=0\bmod3\}}}\) does not vary only in one coordinate. Nonetheless the order-6 generator class is inactive: the log is already a sum of an order-2 and an order-3 function. Exact primitivity testing allows this product.
* On a binary vector space start with distinct independent dual directions, each carrying a nonconstant positive two-entry table. Add any number of apparent cross-block factors with inverse positive tables on the same maps. The formal scopes can be dense and cross all blocks, while (5) removes the cancelled classes. The intrinsic decomposition in Section 4 still returns exactly the original nonconstant one-dimensional factors. The supplied coordinate system need not be aligned with them.

For a finite ring presented as a CRT product, its underlying additive group and explicit homomorphic factor maps are admissible input. This is an exact arithmetic criterion for decomposing a *given mathematical weight* on that product. It does not claim that a standard independently noisy sample distribution admits a small-block factorization or that one can manufacture one from samples. The strictly positive explicit rational hypothesis is essential to the argument; zeros, compressed black-box tables, and approximate cancellation are not dealt with here.

[Etessami–Stewart–Yannakakis, equality of products of exponentials](https://arxiv.org/abs/1304.5429) is the classical polynomial subroutine for (5), not a new number-theoretic task; inequalities for succinct products are not used. [Vaidyanathan, Ramanujan subspaces](https://pmc.ncbi.nlm.nih.gov/articles/PMC6939226/) gives the standard primitive-frequency projector background. [Cohen–Welling, Harmonic Exponential Families](https://pure.uva.nl/ws/files/2509130/162956_cohenb15.pdf) uses a related log-Fourier representation for harmonic probability models, and [Gutch et al., ICA over finite fields](https://www.sciencedirect.com/science/article/pii/S0165168411003513) studies recovery of independent components in a statistical source model. In contrast, this note combines exact character-class zero tests for rational factor descriptions with both fixed-block and intrinsic linear decomposition, without numerical thresholds, sample inference, or enumeration of the ambient group.
