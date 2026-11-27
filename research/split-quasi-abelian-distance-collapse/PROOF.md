# Split spectral cubes force vanishing relative distance

## 1. Statement and parameters

Let \(q\) be a prime power, \(p\) a prime dividing \(q-1\), \(d\ge1\),
and \(E=\mathbb F_p^d\) with its additive group law. Thus \(p\) is
not the characteristic of \(\mathbb F_q\). Set \(N=p^d\) and
\(R=\mathbb F_q[E]\). The coefficients in the group-element basis give
\(R^\ell\) the Hamming space of length \(\ell N\).
For a nonzero \(R\)-submodule \(C\subseteq R^\ell\), let
\[
 \rho=\frac{\dim_{\mathbb F_q}C}{\ell N},
 \qquad D(C)=\frac{\min_{c\in C\setminus\{0\}}\mathrm{wt}(c)}{\ell N}.
\]
Let \(M=(q^\ell-1)/(q-1)\), the number of lines in
\(\mathbb F_q^\ell\), and let \(\alpha=\rho/M\).
If \(C\) is systematic of rank \(k\ge1\) with generator
\((I_k\mid A)\), one may
instead use \(\alpha=q^{-(\ell-k)}\).

**Theorem 1 (all submodules).** For every integer \(0\le s\le d\)
satisfying \(\alpha^{2^s}\ge p^{s-d}\),
\[
                       D(C)\le (1-1/p)^s. \tag{1}
\]
In particular, put \(\beta=\max(1,\log_p(1/\alpha))\) and
\(\eta=\log_2(p/(p-1))\). For \(d\ge2\beta\), taking
\(s=\lfloor\log_2(d/(2\beta))\rfloor\) gives
\[
 D(C)\le (4\beta/d)^\eta. \tag{2}
\]
For \(p=2\) this is \(D(C)\le4\beta/d\).
Fixed \(q,p,\ell\) and a uniform positive lower bound on rate make
\(\beta\) bounded. In the binary-group case \(p=2\), the same
formula also implies decay for varying odd \(q\) and index whenever
\(\ell\log_2 q+\log_2(1/\rho)=o(d)\).

## 2. Full Fourier decomposition and a dense common factor vector

Choose a primitive \(p\)th root \(\zeta\in\mathbb F_q\), possible
because the field's multiplicative group is cyclic. Pair the dual
group with \(E\) via the standard dot product in \(\mathbb F_p\).
For a coefficient array \(a\in R\), use
\[
 \widehat a(x)=\sum_{y\in E}a(y)\zeta^{x\cdot y},
 \qquad a(y)=N^{-1}\sum_{x\in E}\widehat a(x)\zeta^{-x\cdot y}.
\]
The inverse holds by summing the characters: the sum for a nonzero
linear functional is zero by the geometric sum, and for the zero
functional is \(N\), nonzero in the field. Direct convolution
expansion gives \(\widehat{ab}(x)=\widehat a(x)\widehat b(x)\).
Thus the transform is a ring isomorphism onto
\(\prod_{x\in E}\mathbb F_q\) and gives a product decomposition
\[
           \widehat C=\prod_{x\in E} C_x,
           \qquad C_x\le\mathbb F_q^\ell.
\]
Indeed, take \(C_x\) to be the image of coordinate projection.
To assemble arbitrary \(v_x\in C_x\), take a respective preimage
in \(\widehat C\), multiply by the scalar coordinate idempotent at
\(x\), and sum. In particular, the sum of the dimensions of \(C_x\)
is \(\rho\ell N\). Since each dimension is at most \(\ell\), at least
\(\rho N\) constituents are nonzero. Select a line in each such
constituent. Some common line occurs in at least \(\rho N/M\) of
them. Fix a nonzero vector \(v\) on that line; there is a set
\(S\subseteq E\) of density at least \(\alpha\) on which \(v\in C_x\).

For the systematic refinement, the first row of \((I_k\mid \widehat
A(x))\) has a fixed first \(k\) coordinates and only
\(q^{\ell-k}\) possible tails. This gives the higher density without
using any randomness. The dimension of a systematic code is \(kN\)
by its first \(k\) columns.

## 3. A nondegenerate additive cube, by elementary counting

For a set \(S\subseteq E\) of density at least \(\alpha>0\),
let \(A_i\) be the probability over independent uniform
\(x,h_1,\ldots,h_i\in E\) that
\[
                 x+\sum_{j\in J}h_j\in S
                 \quad\text{for all }J\subseteq\{1,\ldots,i\}.
\]
For fixed directions \(h_1,\ldots,h_i\), let \(T\) be the set of
basepoints with all these properties. The extra dimension is the
condition that both \(x\) and \(x+h_{i+1}\) belong to \(T\).
Those two points are independent uniform since
\((x,h_{i+1})\mapsto(x,x+h_{i+1})\) is bijective. Therefore
\(A_{i+1}=\mathbb E(|T|/N)^2\ge(\mathbb E|T|/N)^2=A_i^2\).
By iteration \(A_s\ge\alpha^{2^s}\).

A dependence among \(h_1,\ldots,h_s\) implies that at some first
step \(i+1\), the next vector lies in the span of the first \(i\).
Conditional on prior independent directions that span has
\(p^i\) elements. Hence the probability of dependence is bounded by
\[
                \sum_{i=0}^{s-1}p^{i-d}
                =\frac{p^s-1}{(p-1)p^d}<p^{s-d}. \tag{3}
\]
This upper bound also holds for \(s=0\), when the failure probability
is zero. Thus under (1)'s hypothesis some such cube has independent
directions, and all its \(2^s\) vertices are distinct. The argument
needs only these binary choices of vertices even when \(p>2\);
it does not assume a full \(p^s\)-point affine subspace in \(S\).

## 4. Product support identity and rate conclusion

Take the cube from §3. In \(\widehat C\), use the constituent vector
\((-1)^{|J|}v\) at \(x+\sum_{j\in J}h_j\) and zero elsewhere.
It belongs to the product code because the support is in \(S\)
and every relevant constituent contains \(v\). Its inverse
transform, as an \(\ell\)-vector at coordinate \(y\in E\), is exactly
\[
  c(y)=\frac{v}{N}\zeta^{-x\cdot y}
                    \prod_{j=1}^s(1-\zeta^{-h_j\cdot y}). \tag{4}
\]
This follows by multiplying out the product. The sign convention is
also valid in characteristic two, where minus equals plus.
Since \(v\neq0\), its nonzero coordinate blocks have identical support:
precisely the \(y\) for which every \(h_j\cdot y\) is nonzero.
The map \(y\mapsto(h_j\cdot y)_j\) has rank \(s\), so each output
in \(\mathbb F_p^s\) has \(p^{d-s}\) preimages. It follows that
\[
 \mathrm{wt}(c)=\mathrm{wt}(v)(p-1)^s p^{d-s}>0.
\]
Dividing by \(\ell N\) proves (1).

For (2), \(\beta2^s\le d/2\) and \(s\le d/2\) (since
\(d/(2\beta)\le d/2\) and \(\log_2(d/2)\le d/2\)).
Thus \(\alpha^{2^s}\ge p^{-d/2}\ge p^{s-d}\).
Also \(2^s>d/(4\beta)\); inserting this into
\((1-1/p)^s=(2^s)^{-\eta}\) proves (2).

In the question's systematic ensemble the rate equals \(k/\ell\)
regardless of the sampled matrix. For each fixed \(q>2\) and
\(1\le k<\ell\), choose any prime \(p\mid(q-1)\), then let
\(G=C_p^d\) with \(d\to\infty\). Theorem 1 gives \(D(C)\to0\)
uniformly over all such matrices (including every realization of a
random one). Any fixed \(\delta>0\) below the usual GV threshold
therefore has \(\Pr[D(C)>\delta]=0\) for sufficiently large \(d\),
rather than tending to one. Such \(\delta\)'s exist because
\(h_q(\delta)\to0\) as \(\delta\downarrow0\), while \(k/\ell<1\).
The negative answer concerns arbitrary-group extension of the
distance theorem only. It does not address growing-index results,
individual cyclic families, the nonsplit case for every group,
or any cryptographic interpretation.

## 5. Systematic-code extension to a quotient

Let a finite abelian group \(G\) surject onto \(E=C_p^d\) by
\(\pi\). Let \(\pi_*\) sum group-algebra coefficients in each fiber,
so it is a surjective ring map. For a coefficient word over \(E\)
define its lift by \((\iota b)(g)=b(\pi(g))\) on \(G\). Then
\(\iota(b)a=\iota(b\,\pi_*a)\), by grouping the convolution sum
according to each fiber of \(\pi\). Each coefficient repeats exactly
\(|\ker\pi|\) times; this argument neither divides by that number
nor requires it to be invertible. Thus every word in
the systematic quotient code \((I_k\mid \pi_* A)\) lifts into
\((I_k\mid A)\) by lifting its information symbols, preserving
relative Hamming weight. The systematic bounds extend to any such
quotient, without any sampling assumptions. This is not a claim that
an arbitrary nonsystematic code's image on the quotient has positive rate.
