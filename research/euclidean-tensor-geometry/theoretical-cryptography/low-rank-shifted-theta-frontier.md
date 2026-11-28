# A numerical-range frontier for low-rank shifted lattice theta evaluation

**Status.** A deterministic positive approximation theorem and a matching qualitative bit-complexity obstruction for a forward sum. All matrix data and the shift are supplied. This is not an inverse problem, a search/decision Ring-LWE algorithm, or a result about cryptographic parameter distributions.

For a positive-definite rational matrix \(Q\) and a rational shift \(\theta\), write
\[
 Z(Q,\theta)=\sum_{x\in\mathbb Z^n}
          \exp\bigl(-(x-\theta)^{\mathsf T}Q(x-\theta)\bigr).
\]
In particular \(Z\) is the normalizer of a specified discrete Gaussian. A factor \(e^{\pm\varepsilon}\) means the interval \([e^{-\varepsilon},e^\varepsilon]\).

**Theorem 1 (deterministic numerical-range FPTAS).** Fix a rank parameter \(r\). Suppose a factorization
\[
 Q=D+U C U^{\mathsf T},\qquad
 D=\operatorname{diag}(\beta_i),\quad U\in\mathbb Q^{n\times r},\quad
 C=C^{\mathsf T}\in\mathbb Q^{r\times r}
\]
is part of the input, with \(0\le\beta_i\le B\), every entry of \(U,C\) of magnitude at most \(B\), and \(Q\succeq aI\), where \(B\ge1\), \(0<a\le1\) are supplied rational bounds. For rational \(0<\varepsilon\le1\), a positive dyadic within a factor \(e^{\pm\varepsilon}\) of \(Z\) can be computed deterministically in time polynomial in the input bit length, \(B,1/a,1/\varepsilon\), for every fixed \(r\). The low-rank term need not be positive semidefinite. In particular this is an ordinary FPTAS on a promised family with polynomially bounded \(B,1/a\). There is no sparsity or weak-edge condition.

**Theorem 2 (rank one alone does not suffice).** A deterministic bit-polynomial algorithm for a factor-2 approximation to \(Z\), for every \(Q=I+uu^{\mathsf T}\), \(u\in\mathbb Z^n\), even with the single shift \(\theta=(1/2,\dots,1/2)\), would imply \(\mathsf P=\mathsf{NP}\). This is a polynomial-time promise-gap reduction from PARTITION. The diagonal, minimum spectral bound and shift are fixed; it is the numerical size of the rank-one factor that is unbounded. It does not give strong NP-hardness, a sharp dependence on \(B\), or any hardness claim for a random ensemble.

## 1. Relative truncation despite an exponentially small normalizer

Reduce each \(\theta_i\) modulo \(\mathbb Z\), which does not change the sum, and let \(y=x-\theta\). Using \(\|U\|_{\mathrm{op}}^2\le nrB^2\) and \(\|C\|_{\mathrm{op}}\le rB\), we have
\[
 \|Q\|_{\mathrm{op}}\le B+nr^2B^3.
\]
A coordinatewise nearest integer vector therefore gives \(Z\ge e^{-H}\) for
\(H=n(B+nr^2B^3)/4\). The following coarse, uniform bound suffices:
\[
 \sum_{j\in\mathbb Z} e^{-a(j-c)^2/2}\le 2+\sqrt{2\pi/a}\le F,\qquad F=8/a.
\]
For the first inequality count at most two points in each shell \(k\le |j-c|<k+1\) and compare the decreasing Gaussian sum with its integral. If \(\|y\|_\infty>R\), split the \(a\|y\|^2\) lower bound into halves to obtain
\[
 \sum_{\|y\|_\infty>R} e^{-y^{\mathsf T}Qy}
 \le e^{-aR^2/2}F^n.
\]
Taking an integer \(R\ge1\) with \(aR^2/2\ge H+nF+L\), where \(L=\lceil\log_2(8/\varepsilon)\rceil\), loses at most \((\varepsilon/8) Z\). Such an \(R\) of polynomial numerical size can be found by rational comparisons and doubling. The use of a nearest-vector *term*, rather than a lower bound under an auxiliary probability law, makes this uniform even for shifts for which the true sum is exponentially small.

## 2. Pointwise energy rounding and a finite dynamic program

For \(|y_i|\le R\), let \(v_i\) be the \(i\)-th row of \(U\), treated as an \(r\)-vector. Express the energy as
\[
 \sum_i\beta_i y_i^2 + z^{\mathsf T}Cz,\qquad z=\sum_i v_i y_i.
\]
For a positive dyadic \(\delta\le1\), round each coordinate of \(v_i y_i\) down to the mesh \(\delta\mathbb Z\), and sum those rounded vectors to \(\tilde z\). We have
\(\|z\|_\infty\le nBR,\ \|\tilde z-z\|_\infty\le n\delta\), hence
\[
 \big|\tilde z^{\mathsf T}C\tilde z-z^{\mathsf T}Cz\big|
 \le r^2B n^2 (2BR\delta+\delta^2).
\]
Choose \(\delta\) between half and all of
\(\varepsilon/[32r^2 B n^2(BR+1)]\) (and use the trivial product when \(r=0\)). This error is at most \(\varepsilon/16\); it controls the **multiplicative** error pointwise, without subtracting potentially almost equal numbers.

For each coordinate \(i\), the allowed \(x_i\) are the at most \(2R+2\) integers with \(|x_i-\theta_i|\le R\). Each attaches a positive weight \(e^{-\beta_i(x_i-\theta_i)^2}\) to the rounded local vector. Convolve these \(n\) tables by ordinary addition on the mesh and multiply each resulting bin by \(e^{-\tilde z^{\mathsf T}C\tilde z}\). The grid at all times lies in \([-n(BR+1),n(BR+1)]^r\). Thus there are at most \((1+2n(BR+1)/\delta)^r\) bins, and each update uses at most \(2R+2\) transitions per bin. No approximation has yet been made to any weight in this description.

For bit arithmetic, approximate every one-site and every final weight by a positive dyadic within relative log-error \(\varepsilon/[8(n+1)]\), with a common denominator \(2^p\). One can take \(p\) polynomial in
\[
 BR^2+r^2B n^2(BR+1)^2+\log_2((n+1)/\varepsilon)+1.
\]
Indeed all rational exponents have this magnitude bound; the minimum weight is at least the exponential of minus that bound and the maximum is at most its positive exponential. To see the elementary precision cost, for \(|s|\le K\) use the Taylor series for \(\exp(s/2^j)\) with \(2^j\ge K+1\), then square \(j\) times with guard bits. Alternatively summing the rational terms of the Taylor series for \(\exp(s)\) directly to \(O(K+p+1)\) terms gives absolute error \(2^{-p-O(1)}\) by factorial decay; the intermediate bit lengths are polynomial. Approximate the final rational by the common dyadic mesh with a guard bit. Exact positive integer additions/multiplications can now be used throughout. At stage \(i\) the denominator is \(2^{ip}\) and aggregates include at most \((2R+2)^i\) products. This bounds every numerator's bit length by a polynomial; neither exponentially small relative masses nor the possibly larger-than-one final weights for indefinite \(C\) are an issue.

Accumulated arithmetic multiplies every summand by a factor \(e^{\pm\varepsilon/8}\). Adding this to the rounding loss and the relative truncation loss gives \(e^{\pm\varepsilon}\), since \(1-\varepsilon/8\ge e^{-\varepsilon/4}\) for \(0<\varepsilon\le1\). This proves Theorem 1.

A fixed finite cylinder in residues modulo a fixed \(q\) can be normalized the same way. In the specified coordinates set \(x_i=m_i t_i+b_i\), with \(m_i=q\) at the specified locations and \(m_i=1\) elsewhere. The transformed diagonal entries are \(m_i^2\beta_i\), the rows of \(U\) become \(m_i v_i\), the shift becomes \((\theta_i-b_i)/m_i\), and the quadratic form still dominates \(aI\). Taking the ratio of the two forward sums gives relative accuracy with at most twice the log error. This is a forward property of a supplied model; it does not infer unknown error or secret data. Dense examples already occur with \(Q=I+\mathbf1\mathbf1^{\mathsf T}\), as compared with the companion weak bounded-degree theorem, which instead permits large rank.

## 3. Rank-one obstruction at fixed shift and fixed diagonal

An instance of PARTITION supplies positive integers \(w_1,\dots,w_m\). It asks whether \(\sum_i w_i(2b_i-1)=0\) for some binary \(b_i\). Use \(\ell=16(m+1)\) replicas \(x_{i,0},\dots,x_{i,\ell-1}\) of each formal item, \(n=m\ell\), \(R=n+1\), \(b=8R\), and \(J=m(\ell-1)\). Attach individual distinct exponents \(j(i,k)\in\{0,\dots,J-1\}\) to the replica constraints with \(k\ge1\). Put
\[
 S(x)=\sum_{i,k\ge1} b^{j(i,k)}(x_{i,k}-x_{i,0})
             +b^J\sum_i w_i(x_{i,0}-1/2).
\]
This is a linear form in \(y=x-\tfrac12\mathbf1\). Take \(u\) such that \(u^{\mathsf T}y=2nS(x)\); its coordinates are integers, and their bit length is \(O(J\log b+\log n+\max_i\log(w_i+1))\). Set \(Q=I+uu^{\mathsf T}\).

If the original instance has a partition, putting all replicas equal to the chosen bit of their item gives \(S=0\) and quadratic energy \(n/4\). Thus \(e^{n/4}Z\ge1\). We bound the normalized mass in a NO instance by \(1/8\). There are three parts:

1. **Outside the box.** For \(\|x-\tfrac12\mathbf1\|_\infty>R\), discard the nonnegative rank-one term. Bounding the shifted one-dimensional sum at exponent \(1/2\) by \(2+\sqrt{2\pi}<5\) gives normalized mass at most \(5^n e^{n/4-R^2/2}<1/32\), since \(n\ge32\).
2. **Nonzero \(S\).** The value \(2S(x)\) is always an integer. Thus nonzero \(S(x)\) costs \((2nS(x))^2\ge n^2\). Summing the diagonal Gaussian alone bounds this normalized mass by \(5^n e^{n/4-n^2}<1/32\).
3. **Zero \(S\) inside the box.** Multiply the equation by 2. Reduction modulo \(b\) shows that the lowest replica difference is zero, since its doubled magnitude is at most \(4R<b\). Dividing by \(b\) and repeating proves all replica equalities. The final equation is \(\sum_i w_i(2x_{i,0}-1)=0\). In a NO instance at least one of the now common integers is not binary. The normalized one-block sum is
\[
 T_\ell=\sum_{z\in\mathbb Z}\exp\bigl(-\ell[(z-1/2)^2-1/4]\bigr)
       =2+2\sum_{j\ge1}e^{-\ell j(j+1)}
       \le2+4e^{-2\ell}.
\]
Dropping the final weighted relation but requiring a nonbinary block bounds this part by \(T_\ell^m-2^m\le 2^m\,4m e^{-2\ell}<1/32\). We used \((1+t)^m-1\le e^{mt}-1\le2mt\) for \(mt\le1\).

The total NO bound is \(3/32<1/8\). A factor-2 approximation would distinguish \(\ge1/2\) from \(<1/4\) in normalized units, with ample room to approximate \(e^{n/4}\) by a rational to fixed relative accuracy. Thus it decides PARTITION in bit-polynomial time. The reduction has an explicit numerical-size bottleneck: the replica equalities and weighted relation are packed in an integer positional radix, rather than kept as separate quadratic terms. The gap is for the entire infinite positive sum, not merely for the lowest-energy point.

## 4. Why the promise is not automatic for rational dyadic ring geometry

There is also a direct obstruction to interpreting Theorem 1 as a generic dyadic ring statement. Let \(n\) be a power of two and let \(P\) be the signed negacyclic shift on \(\mathbb Q^n\), multiplication by \(X\) modulo \(X^n+1\) in coefficient coordinates. If a rational matrix \(Q\) commutes with \(P\) and is not scalar, then for **every** rational diagonal matrix \(D\) one has
\[
 \operatorname{rank}(Q-D)\ge n/3. \tag{*}
\]
Indeed \(\mathbb Q[X]/(X^n+1)\) is a field, since \(X^n+1=\Phi_{2n}(X)\), and its regular module is cyclic with generator 1. A rational linear map commuting with \(P\) is therefore multiplication by a field element. Thus \(Q-cI\) is full rank for each \(c\in\mathbb Q\) when \(Q\) is not scalar.

Now write \(s=\operatorname{rank}(Q-D)\). If a value \(c\) occurs \(m_c\) times on \(D\)'s diagonal, the preceding full-rank fact and the rank triangle inequality give \(n\le s+n-m_c\), so \(m_c\le s\). Also \(D-P^jDP^{-j}\) has rank at most \(2s\) for every \(j\), by commutation of \(Q\). Its rank is the number of unequal entries between the diagonal sequence and its \(j\)-fold cyclic rotation; the signs cancel. Averaged over \(j\bmod n\) this number is \(n-\sum_c m_c^2/n\), at least \(n-s\). Hence \(2s\ge n-s\), proving (*). No self-adjointness is needed for the rank statement. Consequently fixed rank is a substantive promise for a supplied correlated model; it does not follow from rational negacyclic symmetry. The argument is not a claim about approximately low numerical rank or irrational precision matrices.

## Prior work and limitations

- Park, Yang, Yun and Shin, [Spectral Approximate Inference](https://proceedings.mlr.press/v97/park19c.html), §§2.1 and 2.3, already use quantized low-dimensional projections and a dynamic program for finite-spin low-rank graphical models. The mesh DP is that existing idea. Theorem 1 adds a relative-tail and bit-precision argument for unrestricted integer spins with arbitrary shifts; the theorem is about a supplied factorization and numerical bounds, not general approximate inference.
- Koehler, Lee and Risteski, [Sampling Approximately Low-Rank Ising Models](https://proceedings.mlr.press/v178/koehler22a.html), §2.2 and Theorem 1.1, give randomized Boolean-cube partition/sampling guarantees using spectral conditions, grids, tempering and a variational tilt. The above rounding controls energy pointwise on a relative truncation and therefore does not require tilting or a trace-log condition on \(U C U^{\mathsf T}\).
- Barvinok, [Computing the Theta Series](https://www.theoryofcomputing.org/articles/v022a009/), §§2.1–2.2 and 8, gives randomized theta approximation under spectral conditions, and deterministic approximation in the two smooth regimes. Our rank and magnitude conditions are different and do not require smoothness. His near-spectral theorem and ours need not contain one another.
- The numerical lower bound uses the classical NP-completeness of PARTITION, e.g. [Karp, Reducibility Among Combinatorial Problems](https://doi.org/10.1007/978-1-4684-2001-2_9). It is an encoding/complexity statement for a forward scalar sum, not evidence for hardness of any particular ideal-lattice sampling construction. No average-case rarity, standard Ring-LWE reduction, or theorem on arbitrary unstructured Gaussian evaluation is claimed. The bundled checker audits finite algebra and numerical constants, not the asymptotic proof.
