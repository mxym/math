# Deterministic approximation of weakly coupled shifted lattice Gaussians

**Scope.** This note studies an explicit, supplied quadratic law on
integer coefficients, used only as a forward noise model. It does not
estimate centers or parameters from observations, provide a recovery
procedure, or draw conclusions about a concrete cryptographic scheme.
A sparse Gram matrix in the dyadic coefficient algebra is included
as a mathematical example. The conclusion is deterministic relative
approximation in a fixed-width, bounded-degree weak-coupling regime,
not merely a large-width smoothing statement.

Fix positive constants \(\beta_0,\beta_1\) with \(\beta_0\le\beta_1\)
and a positive integer \(\Delta\). A simple graph \(G=(V,E)\) with
\(n\) vertices has maximum degree at most \(\Delta\). The supplied
rational parameters are \(\beta_i\in[\beta_0,\beta_1]\), shifts
\(\theta_i\), and edge couplings \(J_{ij}\) of either sign. Write
\[
  Z=\sum_{x\in\mathbb Z^n}
   \exp\!\left[-\sum_i\beta_i(x_i-\theta_i)^2
           -\sum_{ij\in E}J_{ij}(x_i-\theta_i)(x_j-\theta_j)\right].
                                                               \tag{1}
\]
Shifts may first be reduced individually modulo one, since this
does not change the sum.

**Theorem.** There is an explicit positive constant
\(J_*=J_*(\beta_0,\beta_1,\Delta)\) such that if
\(\max_{ij}|J_{ij}|\le J_*\), then (1) has a deterministic
fully polynomial-time approximation scheme: for
\(0<\varepsilon\le1\), it returns a value within multiplicative
\(e^{\pm\varepsilon}\) in time polynomial in the input bit
length and \(1/\varepsilon\), with the constants fixed.
No estimate of graph treewidth is needed.

The useful point is that the alphabet \(\mathbb Z\) is not
truncated separately at every site of a connected cluster to
sum its weight. Such a local brute-force sum would already be
quasipolynomial at the relevant cluster size. Instead the
connected Taylor coefficients are sums of products of
one-dimensional Gaussian moments.

## 1. A uniform zero-free disk for the interaction quotient

Let \(Z_i=\sum_{k\in\mathbb Z}e^{-\beta_i(k-\theta_i)^2}\);
write \(X_i=k-\theta_i\) under this normalized one-site law,
independently over sites. Set
\[
  W(z)=\mathbb E\exp\left[-z\sum_{ij\in E}J_{ij}X_iX_j\right],
  \qquad Z=W(1)\prod_i Z_i .
\]
Take \(\theta_i\in[-1/2,1/2]\) and fix any \(M\ge1\) satisfying
\[
 M \ \ge\
 e^{\beta_1/4}\sum_{k\in\mathbb Z}
   \bigl(1+(|k|+1/2)^\Delta\bigr)
   e^{-(3\beta_0/4)(|k|-1/2)_+^2}.
\]
A rational upper bound can be selected once for the fixed
constants, by a Gaussian tail bound. One choice is
\[
         J_*=\min\!\left\{\frac{\beta_0}{4\Delta},
                      \frac{1}{32 M^2\Delta^2}\right\}.        \tag{2}
\]
In particular the quadratic form in (1) is positive definite
by diagonal dominance. For \(|z|\le2\), absolute convergence
and analyticity in a slightly larger disk follow from
\[
 \sum_{ij\in E}|zJ_{ij}X_iX_j|
        \le \frac{|z|J_*\Delta}{2}\sum_i X_i^2
\]
and a fixed positive margin in the one-site Gaussian tails.
The same observation holds with any subset of the edges.

For a nonempty connected edge set \(S\) (connectivity is in its
incident vertices), define
\[
 w_S(z)=\mathbb E\prod_{ij\in S}(e^{-zJ_{ij}X_iX_j}-1).
\]
Expand the product over edges and group chosen edges into their
connected components. Since disjoint components depend on
disjoint \(X_i\), \(W(z)\) is the partition sum over collections
of vertex-disjoint connected edge sets with weights \(w_S(z)\).
The single-edge inequality \(|e^u-1|\le|u|e^{|u|}\)
gives, for \(|z|\le2\),
\[
 \begin{split}
 |w_S(z)|
 &\le (2J_*)^{|S|}\prod_{i\in V(S)}
    \mathbb E\!\left[|X_i|^{\deg_S(i)}
                  e^{J_*\deg_S(i)X_i^2}\right]\\
 &\le (2J_*M^2)^{|S|}.                                        \tag{3}
 \end{split}
\]
For the last bound, \(Z_i\ge e^{-\beta_1/4}\) from a nearest
integer and \(J_*\deg_S(i)\le\beta_0/4\), so each factor is at most
\(M\). Also \(|V(S)|\le2|S|\).

Here is an elementary proof of the needed zero-free estimate.
Let \(\Xi(U)\) denote the same partition sum on vertices
\(U\subseteq V\), keeping all available edges of \(G[U]\).
For \(v\in U\),
\[
 \Xi(U)=\Xi(U\setminus\{v\})+
  \sum_{\substack{S\subseteq E(G[U])\text{ connected}\\v\in V(S)}}
       w_S(z)\Xi(U\setminus V(S)).                            \tag{4}
\]
The number of connected \(k\)-edge sets containing a specified
vertex is at most \(\Delta^{2k}\): duplicate each edge of a
connected set and traverse an Euler walk of length \(2k\) starting
there, then recover the edge set from the walk.
Inductively suppose the deletion ratios on smaller sets all
differ from one by at most \(1/2\), and are therefore nonzero.
Deleting the \(|V(S)|-1\) vertices after deleting \(v\) yields
\[
 \left|\frac{\Xi(U\setminus V(S))}{\Xi(U\setminus\{v\})}\right|
       \le 2^{|V(S)|-1}.
\]
By (2)–(3) the deviation of the ratio in (4) from one is at most
\[
       \sum_{k\ge1}(8J_*M^2\Delta^2)^k\le1/3 .
\]
This closes the induction from \(\Xi(\varnothing)=1\).
Thus \(W(z)\ne0\) on the disk. Multiplying deletion ratios
along any nested ordering, choose their logarithms analytic in
the disk about one, each of magnitude at most \(\log2\).
Their sum is the logarithm of \(W(z)\) normalized at zero, and
\[
                       |\log W(z)|\le n\log2\quad(|z|\le2).    \tag{5}
\]
On the real segment from zero to one this is its ordinary real
logarithm, because (1) is positive.

## 2. Effective Taylor coefficients without large local sums

By (5) and Cauchy's coefficient estimate, dropping terms of
degree above \(L\) in the Taylor series of \(\log W(1)\)
has error at most \(n\log2\,2^{-L}\).
Use \(L=\lceil\log_2(8n/\varepsilon)\rceil\).

For any edge set \(T\) let \(W_T(z)\) be the corresponding
expectation with only those edge couplings. For each \(j\le L\),
the connected support identity is
\[
 [z^j]\log W(z)
   =\sum_{\substack{S\subseteq E\text{ connected}\\1\le |S|\le j}}
       \ \sum_{T\subseteq S}(-1)^{|S|-|T|}
                   [z^j]\log W_T(z).                         \tag{6}
\]
One proof is to give every edge its own formal variable.
The inner sum retains precisely the monomials with support
exactly \(S\), of which none have support size greater than
their degree. Disconnected supports give zero: with other
edges set to zero, the expectation factors over vertex-disjoint
components, so its logarithm has no monomial using two components.
This is the usual connected-support principle specialized to
an explicit expectation.

Enumerate connected sets \(S\) of at most \(L\) edges by walks
of length at most \(2L\) from every starting vertex,
deduplicating their edge sets and retaining the stated sizes.
There are \(n\,\max(2,\Delta)^{O(L)}\) candidates. For \(T\subseteq S\)
compute the coefficients \(b_j(T)=[z^j] W_T(z)\) by
\[
 b_j(T)=
   \sum_{\substack{(m_e)_{e\in T}\ge0\\ \sum m_e=j}}
      \left(\prod_{e\in T}\frac{(-J_e)^{m_e}}{m_e!}\right)
      \left(\prod_{i\in V(T)}
              \mathbb E X_i^{\,\sum_{e\ni i}m_e}\right).       \tag{7}
\]
Each summand factors into one-dimensional moments. There are
at most \(\binom{2L}{L}\) exponent assignments up to degree \(L\)
because \(|T|\le L\); the empty edge set is trivial.
Taking the formal log of the truncated series with \(b_0=1\)
and summing (6) costs only \(n\max(2,\Delta)^{O(L)}\)
times a polynomial in the significant bit count.
In particular no \(L^{\Theta(L)}\) factor from joint spin
enumeration or from listing labeled cluster trees occurs.

## 3. Bit precision and the final relative error

For completeness, the infinite alphabet does not hide an
arithmetic oracle. For \(0\le b\le L\), compute
\(\mathbb E X_i^b\) and \(Z_i\) by one-dimensional sums with
polynomial-bit error bounds. For \(|u|\) large,
\[
 |u|^b e^{-\beta_0u^2}
    \le \bigl(b/(e\beta_0)\bigr)^{b/2}
                     e^{-\beta_0u^2/2},
\]
with the \(b=0\) factor interpreted as one. Thus for absolute
error \(2^{-P}\) a cutoff
\(O_{\beta_0,\beta_1}(\sqrt{P+L\log(L+2)+1})\) on \(|k|\)
suffices with a constant enlargement for the Gaussian sum tail.
The normalizing denominator is uniformly bounded below,
so its division is well behaved. These computations only
involve exponential evaluation at rational arguments of
polynomially bounded magnitude and polynomial precision,
obtainable by rational Taylor evaluation and range reduction.

Here is a conservative propagation bound. The moments of
orders at most \(L\) are bounded in magnitude by
\(\exp(O(L\log(L+2)))\), and each product in (7) uses at most
\(2L\) nontrivial moments. As \(|J_e|\) is uniformly bounded,
each \(b_j\) and the Lipschitz error amplification from those
moments is at most \(\exp(O(L^2\log(L+2)))\).
Expand the formal log as
\(\sum_{\ell=1}^L(-1)^{\ell+1}(W_T-1)^\ell/\ell\)
modulo degree \(L+1\). Each coefficient is a sum of at most
\(\exp(O(L))\) products of at most \(L\) coefficients, so a
loose propagation bound is
\(\exp(O(L^3\log(L+2)))\).
This, the connected-set count, and the \(2^L\) subset count
in (6) are covered by \(P=O(L^4+\log(n/\varepsilon))\)
binary fractional bits with sufficiently large fixed constants.
Thus the rounding contribution can be made at most
\(\varepsilon/4\). Rational intermediates can be kept polynomial
in bit length: use common denominators for rounded moments and
the rational \(J_e\), and note that the degrees of the arithmetic
expressions are polynomial in \(L\) and the factorial and
formal-log denominators have polynomial bit length.

Sum the logarithm of the single-site factors to error
\(\varepsilon/4\), using the same uniform lower bound on \(Z_i\).
Combine with the truncation error and exponentiate with another
reserved error margin. The resulting multiplicative error is at
most \(e^{\pm\varepsilon}\). The logarithm being exponentiated
has magnitude \(O(n)\) by fixed-width single-site bounds and (5),
so the relative output can be represented with polynomial bits.
Since \(L=O(\log(n/\varepsilon))\) and \(\Delta\) is fixed, all of
these steps are polynomial in the stated parameters.

## 4. A forward residue-law consequence

Fix an integer modulus \(q\ge2\) independently of the input size.
One may reduce \(J_*\) in advance to
\(J_*(\beta_0,q^2\beta_1,\Delta)/q^2\). Then cylinder probabilities
of the given known discrete Gaussian reduced coordinatewise
modulo \(q\) have the same deterministic relative approximation.
For a specified set of residue constraints, write
\(x_i=m_i y_i+a_i\) with \(m_i=q\) at constrained sites and
\(m_i=1,a_i=0\) elsewhere. This turns the numerator mass into
another sum of form (1), with diagonal coefficients
\(\beta_i m_i^2\), couplings \(J_{ij}m_i m_j\), and a shifted
center \((\theta_i-a_i)/m_i\). Its parameters still pass the
strengthened condition. Take its ratio to the original mass.
Consequently an abstract forward sampler for this finite
residue law can use the approximate cylinder masses to
normalize each site's conditional probabilities, with
\(O(nq)\) such evaluations at relative error \(O(\varepsilon/n)\).
An ordinary sequential coupling bounds the resulting total
variation error by \(O(\varepsilon)\).
This consequence is for a fully specified law, not a sampler
claim for arbitrarily dense covariance or any concrete protocol.

For a dyadic example, let \(P\) be the signed cyclic shift
in the power basis of \(\mathbb Z[X]/(X^n+1)\). A matrix
\(C=sI+\sum_{\nu=1}^k t_\nu P^{j_\nu}\), with fixed \(k\),
has \(C^{\mathsf T}C\) with only a fixed number of shifted
diagonals even when the shifts are large. If \(s^2\) is
bounded above and below and the other coefficients are
sufficiently small, its symmetric Gram matrix gives
\(\beta_i,J_{ij}\) in the stated regime after combining
coincident shifts. Bounded degree here does not require that
the original shift graph be a short-width chain. This is
a sufficient mathematical structure for certified forward approximation.

## Prior scope

* [Barvinok, *Computing the theta function*, arXiv:2208.05405](https://arxiv.org/abs/2208.05405),
  [full paper §§2.1 and 8](https://sites.lsa.umich.edu/barvinok/wp-content/uploads/sites/1434/2025/05/thetalog.pdf):
  an FPRAS for shifted theta under a spectral condition and a
  deterministic FPTAS in the smooth range. Here the algorithm is
  deterministic under bounded-degree weak coupling, while eigenvalues
  can stay at fixed positive width (neither of the smooth conditions).
  This is a narrower structural family, not a deterministic solution
  for Barvinok's whole nonsmooth spectral interval.
* [Helmuth, Perkins and Regts, *Algorithmic Pirogov–Sinai theory*](https://research-information.bris.ac.uk/files/209839753/Full_text_PDF_submitted_manuscript_.pdf)
  and [Mann–Minko, *Algorithmic Cluster Expansions for Quantum Problems*](https://arxiv.org/abs/2306.08974)
  exemplify zero-free polymer algorithms. The deletion argument
  and connected-support extraction here are standard kinds of
  tools. The relevant implementation detail for the unbounded
  alphabet is (7) and its polynomial-bit moment calculation,
  not a new general cluster theorem.

The companion finite tests check the combinatorial coefficient
identity with exact rational arithmetic on generated tables, and
separately compare low-dimensional Gaussian values. They do not
serve as the proof of analyticity.
