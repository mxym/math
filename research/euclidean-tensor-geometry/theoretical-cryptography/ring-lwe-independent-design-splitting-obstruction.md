# A statistical obstruction to splitting ring rows into independent scalar designs

Expanding a ring sample in a power basis yields many scalar responses, but their public coefficient vectors are rotations of one vector. Merely observing that they are dependent does not rule out an arbitrary random conversion of the whole experiment. In a broad wrapped-noise model, we prove a quantitative obstruction to such a conversion, even if it may choose the **new public coefficients after seeing the responses**. This is an impossibility bound, not a sample-generation method.

## 1. Setup and results

Fix odd \(q\ge3\), including composite \(q\), dyadic \(d\to\infty\), and \(R=(\mathbb Z/q)[X]/(X^d+1)\). All ring coordinates are in the power basis. For \(b=\beta/d\) with fixed \(\beta>0\), write
\[
 f_b(y)=\sum_{r\in\mathbb Z}b^{r^2}e^{2\pi i r y},\qquad
 g_b(y)=\frac1q\sum_{a\in\mathbb Z/q}f_b(y-a/q).
\]
The source experiment, with unknown parameter \(s\in R\), consists of \(k\ge1\) independent public uniform rows \(A_i\in R\) and \(Y_i=A_i s/q+E_i\) modulo the coefficient torus, with independent scalar errors of density \(f_b\). Assume \(k=o(d/\log d)\). This is an abstract broad, small-information regime, not a deployment regime.

The target experiment, with the **same** parameter \(s\), consists of \(m\) independent public coefficient vectors \(U_j\) uniform in the additive group \(R\), and scalar responses \(Z_j=\langle U_j,s\rangle_{\mathrm{dot}}/q+\epsilon_j\) modulo one, with independent \(\epsilon_j\) of wrapped densities \(f_{b_j'}\). Dot denotes the coefficient pairing, so these are scalar linear phases, not further ring rows. Let
\[
 \Delta=\inf_K\sup_s\operatorname{TV}\big(KP_s^{\rm source},P_s^{\rm target}\big)
\]
be the one-way statistical deficiency, over every measurable parameter-independent Markov kernel \(K\). It need not retain the source, be efficient or algebraic, output coefficients independent of its input, or even have exactly the desired marginal law of target coefficients. With \(m\le d^{O(1)}\),
\[
 \Delta\ \ge\ \frac12\left(
     \frac1m\sum_{j=1}^m b'_j - b\frac{\min(k,m)}m -O(b^2)
                     \right)_+.                              \tag{1}
\]
The \(O(b^2)\) is uniform over the target amplitudes \(0<b'_j<1\) and kernels, along the specified growth sequences. In particular one random ring row does not produce \(d\) independent scalar designs of the same width to error \(o(b)\), despite having \(d\) scalar coordinates.

There is a stronger scale statement for \(m\to\infty\) with \(m=o((\log d)^2)\). Suppose \(b'_j=b'=\gamma/d\) for fixed \(\gamma>0\). If for some fixed \(0<\eta<1\),
\[
 \frac{k}{m}\le (1-\eta)\frac{\gamma}{\beta},
\]
then \(\Delta=\Theta_{\eta,\beta,\gamma}(b'\sqrt m)\), the same order as the total variation of the target law from its label-independent product-Haar reference. This bound is for a theoretical statistical comparison with a loss depending on the unknown parameter; a witness used in its proof need not be measurable from public responses alone.

## 2. A pointwise posterior harmonic estimate

Use a uniform prior \(S\) on \(R\) for the lower bound. If \(u\in R\), put \(\chi_u(s)=e^{2\pi i\langle u,s\rangle_{\mathrm{dot}}/q}\), and let the orbit of \(u\) mean \(\{\pm X^j u:0\le j<d\}\). With probability \(1-e^{-\Omega(d)}\) over the source design alone, the following holds simultaneously for every \(y\) and \(u\ne0\):
\[
 \left|\mathbb E[\chi_u(S)\mid A,Y=y]\right|
 \le b\,\mathbf1_{\{u\text{ in an orbit of some }\overline A_i\}}
                +C b^2,\qquad \overline A_i=A_i(X^{-1}).       \tag{2}
\]
In particular the estimate also holds if the tested direction is selected after seeing \(y\).

To prove this, use product \(g_b\) as the source reference. Write
\[
 v_a(y)=\frac{\sum_{r\equiv a\pmod q} b^{r^2}e^{2\pi i r y}}{g_b(y)},
 \qquad a\in\mathbb Z/q.
\]
Then \(v_0=1\), \(\|v_{\pm1}\|_\infty\le b+O_q(b^4)\), and the other nonzero residues have supremum \(O_q(b^4)\). This uses \(g_b=1+O(b^{q^2})\), \(q\ge3\). The signed multiplication-by-\(X\) matrix has transpose its inverse, so the coefficient adjoint of multiplication by \(A_i\) is multiplication by \(\overline A_i\). Averaging \(\chi_u(S)L_{A,S}(y)\) over labels, where \(L_{A,s}\) is the source response likelihood relative to product \(g_b\), selects exactly the terms
\[
 F_A(u;y)=
 \sum_{\substack{w\in R^k\\\sum_i\overline A_i w_i=u}}
                 \prod_{i,j} v_{(w_i)_j}(y_{i,j}).             \tag{3}
\]
The posterior is \(F_A(u;y)/F_A(0;y)\).

For a nonzero \(w\in R^k\), the random sum \(\sum_i\overline A_i w_i\) is uniform in \(J=\sum_i w_iR\), a nonzero ideal. Every nonzero ideal has size \(e^{\Omega_q(d)}\). Indeed a minimal nonzero ideal inside it is a simple module, isomorphic to \(R/\mathfrak m\) for a maximal ideal. All these simple residue degrees over the associated prime field are \(\operatorname{ord}_{2d}(p)=\Omega_p(d)\) for odd \(p\mid q\), since each root of \(X^d+1\) modulo \(p\) has order \(2d\) and \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\). Thus each particular nonzero \(w\) is in the kernel with probability \(e^{-\Omega_q(d)}\).

Let \(N=kd\). Choose \(L\) a sufficiently large constant times \(k+\log d\), so \(L=o(d/\log d)\). The number of \(w\)'s of scalar weight at most \(2L\) is \(\exp(O(L\log(qN)))=\exp(o(d))\). By the preceding bound and the union bound there is no nonzero kernel word of weight \(\le2L\), except on a design event of probability \(e^{-\Omega(d)}\). On this event, each sum \(u\) has at most one representation of weight \(\le L\) (subtract two such words). Meanwhile the absolute total of all terms of weight \(>L\), even without the constraint in (3), is bounded by
\[
 \sum_{\ell>L}\binom N\ell(C_q b)^\ell=O(d^{-10}).               \tag{4}
\]
For this choose \(L\ge4e C_q Nb+20\log d\); \(Nb=\beta k\), and the binomial bound makes each term at most \(4^{-\ell}\). The estimate is uniform in \(y\).

For \(u=0\), the only short representation is the zero word, so \(F_A(0;y)=1+O(d^{-10})\). For nonzero \(u\) a short representation consisting of one signed unit entry gives \(b+O(b^4)\) and is an orbit hit; a one-site residue other than \(\pm1\) gives \(O(b^4)\), and any short representation with at least two sites gives \(O(b^2)\). Combining these with (4) proves (2). The same estimate is valid when \(u\) depends on additional Markov-kernel randomness: given the whole source, the kernel's output is conditionally independent of \(S\).

## 3. A first-harmonic budget for arbitrary output choices

In comparing the two experiments, pair the output with the uniform label \(S\). The TV on this joint law is the prior average of the conditional TVs and lower bounds the worst-case TV for every kernel. Let \(\mathcal G(U)\) be the event that all \(U_j\ne0\) and no two belong to the same signed orbit. Under the target its failure probability is at most
\[
 m q^{-d}+\binom m2 (2d)q^{-d}=e^{-\Omega(d)}
\]
for polynomial \(m\). No promise about \(\mathcal G\) is imposed on the kernel output.

Use the bounded, label-dependent comparison function
\[
 \mathbf1_{\mathcal G(U)}\sum_{j=1}^m
       \cos\big(2\pi(Z_j-\langle U_j,S\rangle_{\rm dot}/q)\big).   \tag{5}
\]
Under the target its expectation is \(\Pr(\mathcal G)\sum_j b'_j\). Under a converted source law, condition on the source and the kernel output. On a good source design and when \(\mathcal G\) holds, at most \(\min(k,m)\) output directions can belong to the union of source signed orbits, irrespective of how they were generated. Equation (2) bounds the conditional expected value of (5) by \(b\min(k,m)+C m b^2\). On bad output designs the function is zero, and on bad source designs its absolute value is at most \(m\). Its range is contained in \([-m,m]\), so the dual TV inequality yields (1). This proof neither conditions on an unobserved correctness event of the kernel nor assumes its output coefficients are independent of the responses.

## 4. A collective witness at the natural TV scale

In the growth range for the stronger result, refine the good event on target designs as follows. Let
\(U(\eta)=\sum_j\eta_jU_j\) for \(\eta\in(\mathbb Z/q)^m\).
We require this map to be injective, and require that if \(U(\eta)\) and \(U(\eta')\) for nonzero \(\eta,\eta'\) are in the same signed orbit, then \(\eta'=\pm\eta\). These conditions hold with probability \(1-e^{-\Omega(d)}\) under the independent target designs. Here is a prime-power proof including composite \(q\). For a nonzero \(\eta\) the equation \(U(\eta)=0\) reduces, after dividing out a common prime power at a prime where an entry is nonzero, to one containing an invertible nonzero scalar modulo that prime. For a candidate orbit collision
\(\sum_j(\eta_j-\varepsilon X^h\eta_j')U_j=0\), \(\varepsilon=\pm1\), \(0\le h<d\), if \(h=0\) and \(\eta'\ne\pm\eta\) use the same scalar argument. If \(h>0\), choose a prime power component on which some coefficient pair is nonzero and divide the least valuation of all coefficient pairs. After reduction to its prime field, some coefficient is \(\alpha-\delta X^h\) not identically zero. Its multiplication matrix has rank at least \(d/2\): when both constants are nonzero the number of roots shared with \(X^d+1\) is at most \(\gcd(h,2d)\le d/2\), and the modulus is squarefree at an odd prime. Conditioning on all other \(U_j\), the collision thus has probability at most \(e^{-\Omega_q(d)}\). Union over at most \(O(d\,q^{2m})\) choices. Write \(\mathcal G_*(U)\) for this good event. Injectivity on the dual group also makes the map \(s\mapsto(\langle U_j,s\rangle)_j\) surjective.

For a small fixed \(a>0\), put \(\lambda=a/\sqrt m\). For \(z\in\mathbb T^m\), define \(H(z)=\prod_j e^{i\lambda\cos(2\pi z_j)}\). Use the real bounded comparison function
\[
 F(U,z,s)=\mathbf1_{\mathcal G_*(U)}
 \operatorname{Im}\left[
       H(z-(\langle U_j,s\rangle/q)_j)
       -\frac1{q^m}\sum_{v\in(\mathbb Z/q)^m} H(z-v/q)\right].    \tag{6}
\]
It has absolute value at most 2. The second term is the invariant part and cancels precisely the zero Fourier mode of the first term on the finite grid of shifts.

For each \(z\), the grid coefficients of each factor \(e^{i\lambda\cos(2\pi(z_j-v_j/q))}\) have zero-residue magnitude \(\le1\), and nonzero-residue magnitudes \(\le\lambda/2+C_q\lambda^2\). Indeed the term \(i\lambda\cos\) contributes only to the two distinct residues \(\pm1\), with magnitude \(\lambda/2\), and the exponential Taylor remainder has magnitude \(O(\lambda^2)\). Thus the nonzero coefficients of the product are each at most \(\lambda/2+C_q\lambda^2\); their total absolute mass is at most \((1+C_q\lambda)^m\le e^{C_q a\sqrt m}\). On \(\mathcal G_*(U)\), each source orbit hits at most two of the nonzero image directions \(U(\eta)\); the coefficients might otherwise come from any mixed combination, which is why \(\mathcal G\) alone does not suffice. By (2), conditioning again on the source and the arbitrary output, (6) has expected value under the converted source at most
\[
 2k(\lambda/2+C_q\lambda^2)b
    +O(b^2 e^{C_q a\sqrt m})+e^{-\Omega(d)}
  = a b k/\sqrt m\,(1+o(1))+o(b'\sqrt m).                       \tag{7}
\]
Here \(m=o((\log d)^2)\) and \(\gamma/\beta\) is fixed; the last term is uniform in the kernel under the asserted bound on \(k/m\).

Under the target, the first term in (6) is an expectation under the actual independent errors \(f_{b'}\), and the invariant term is an expectation under independent \(g_{b'}\). To check the latter, grid-invariance permits the averaging defining \(g_{b'}\) before integration. Let \(\nu_0=\int_{\mathbb T}e^{i\lambda\cos(2\pi y)}dy=1-\lambda^2/4+O(\lambda^4)\), real. A scalar cosine expansion gives
\[
 \begin{split}
 \int e^{i\lambda\cos(2\pi y)}f_{b'}(y)dy
   &=\nu_0+i b'\lambda(1+O(\lambda^2))+O(b'^4\lambda),\\
 \int e^{i\lambda\cos(2\pi y)}g_{b'}(y)dy
   &=\nu_0+O(b'^{q^2}\lambda).
 \end{split}
\]
The first-order imaginary coefficient follows from \(\int\cos^2(2\pi y)=1/2\) and the vanishing odd moments; normalization of the remainder allows the factor \(\lambda\). Since \(m b'\lambda=o(1)\), taking \(m\)-th powers yields target expectation
\[
 a\,e^{-a^2/4} b'\sqrt m(1+o(1))                                \tag{8}
\]
including the negligible failure probability of \(\mathcal G_*\). Choose \(a>0\) with \(e^{-a^2/4}>1-\eta/2\). The difference between (8) and (7) is at least a fixed positive multiple of \(b'\sqrt m\). A function bounded by 2 gives a TV lower bound of one-fourth of that difference. The corresponding upper bound is vacuous, by comparing to the parameter-independent target design and independent Haar responses. In fact the TV to this reference is \(b'\sqrt{m/\pi}(1+o(1))\): conditional on the parameter and designs, translate to the error coordinates. The product density minus 1 has first-shell linear term \(2b'\sum_j\cos(2\pi y_j)\); Parseval bounds the squared norm of the rest by \(O((mb'^2)^2+m b'^8)=o(mb'^2)\). The product-Haar CLT for the sum of cosines, with uniform integrability from their second moment, gives the formula after dividing its absolute first moment by two. Thus the lower bound says a fixed-factor expansion cannot improve even the **order** of the trivial full-experiment error in this window. It does not specify any informative conversion.

## 5. Earlier work and boundary

[Peikert, How (Not) to Instantiate Ring-LWE](https://eprint.iacr.org/2016/351.pdf), in the discussion of coefficient views and LWE, notes that the scalar coefficient rows of a ring sample are maximally dependent despite their uniform marginals. This direct dependence statement is different from a bound on **all** Markov conversions, including those that replace the public designs after reading the responses. [Axelrod–Garg–Han–Sharan–Valiant, On the Statistical Complexity of Sample Amplification](https://arxiv.org/abs/2201.04315) supplies the general comparison-of-experiments framework. [Genise–Micciancio–Peikert–Walter](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf) analyze a different sample conversion setting with larger error; the bounds here preserve this distinction. The earlier [literal-prefix obstruction](https://github.com/mxym/math/blob/167e621623da0f5e801945ff36583d8e1ec3b2b3/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-unchanged-prefix-obstruction.md) keeps a fixed labeled prefix and appends same-design samples; the present result does not keep any prefix, and its target has independent random scalar designs.

Uniform harmonic control in (2) depends on the stated \(k=o(d/\log d)\) regime. The collective witness is only asserted for \(m=o((\log d)^2)\); (1) has the larger polynomial-\(m\) range but need not give the full TV scale there. We supply no conversion preserving useful correlations, efficient search procedure, key-recovery method, or result about practical parameters.
