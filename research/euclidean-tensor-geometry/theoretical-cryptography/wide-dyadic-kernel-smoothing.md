# Cubic smoothing for wide random dyadic module kernels

This note treats the kernel-smoothing ingredient in Albrecht–Felderhoff–Lai–Lapiha–Woo's Gaussian leftover hash lemma over number fields. For sufficiently wide random dyadic matrices, the kernel's full dual Gaussian mass has the same sharp window as the unit cubic lattice, in coefficient norm. The proof does not construct short preimages or use a shortest-vector algorithm.

## 1. Model and theorem

Let \(d\) be a power of two (including \(d=1\), which gives the integer case), \(R_d=\mathbb Z[Y]/(Y^d+1)\), and \(X\in R_d^{r\times m}\). Independently in every coefficient of every entry, draw an integer with mass proportional to \(e^{-k^2/(2s^2)}\). The real coefficient matrix \(A\in\mathbb Z^{D\times N}\) of multiplication by \(X\) has \(D=rd\), \(N=md\). It uses the ordinary Euclidean norm on the coefficient vectors. Put
\[
 \Lambda=\ker_{\mathbb R}(A)\cap\mathbb Z^N,\qquad
 \Theta_A(t)=\sum_{w\in\Lambda^*}e^{-t\|w\|^2},\qquad
 M=D+(\log(m+1))^2.
\]
The dual is taken in the real span of \(\Lambda\). For \(N\to\infty\) assume
\[
  1\le s\le N^C \text{ for a fixed } C,\qquad
  \frac{m}{D M(\log N)^4}\longrightarrow\infty.                 \tag{1}
\]
Then, for any fixed \(b\) and any deterministic \(T_N=o((\log N)^2)\) with \(T_N\ge\log N-b\),
\[
 \sup_{\log N-b\le t\le T_N}
 \left|\frac{\Theta_A(t)-1}{\exp(2Ne^{-t})-1}-1\right|
       \longrightarrow0\quad\text{in probability}.            \tag{2}
\]
More precisely, the uniform relative error tends to zero on events of probability at least \(1-e^{-c_*(\log N)^2}\) for some \(c_*>0\). In particular, at \(t=\log N+c\) the limiting total mass is \(\exp(2e^{-c})\). For any fixed upper bound \(E>0\), if \(0<\epsilon_N\le E\) and \(\log(1/\epsilon_N)=o((\log N)^2)\), the usual smoothing parameter satisfies
\[
  \pi\,\eta_{\epsilon_N}(\Lambda)^2
      =\log\!\left(\frac{2N}{\log(1+\epsilon_N)}\right)
          +o_{\mathbb P}(1).                                  \tag{3}
\]
Here \(\eta_\epsilon\) is the infimum of \(\lambda>0\) with \(\Theta_A(\pi\lambda^2)\le1+\epsilon\). For small \(\epsilon_N\) the logarithm in (3) is \(\log(2N/\epsilon_N)+o(1)\). This includes errors smaller than every inverse polynomial, for example \(\exp(-(\log N)^{3/2})\).

For \(d\ge2\), the ordinary canonical Euclidean norm counting both members of each complex pair is \(\sqrt d\) times the coefficient norm in this basis. Hence the canonical smoothing width is \(\sqrt d\) times the width in (3), and the canonical input Gaussian width in the exponent convention \(e^{-\pi\|x\|^2/\lambda^2}\) is \(\sqrt{2\pi d}\,s\). The identity follows by summing evaluations of monomial products over the roots of \(Y^d+1\). In other normalization conventions this deterministic conversion has to be made explicitly.

## 2. Uniform concentration of the row phases

Let \(x_i\in\mathbb Z^D\) be the coefficient vector of the \(i\)-th ring column of \(X\). The real columns of \(A\) are \(U_j x_i\), where \(0\le j<d\) and \(U_j\) is simultaneous multiplication by \(Y^j\) in the \(r\) coordinates, a signed permutation. The vectors \(x_i\) are independent across \(i\); the \(d\) expanded columns for one \(i\) are not assumed independent.

For a scalar coefficient \(U\), comparison of shifted Gaussian sums at zero by Poisson summation gives \(\mathbb E e^{t U}\le e^{s^2 t^2/2}\) by completing the square. Its variance is at least \(c_0 s^2\) for an absolute \(c_0>0\): the integers with \(s\le |k|\le2s\) carry a fixed positive fraction of total mass for all \(s\ge1\), by comparison with the integral of the Gaussian. Its variance is also at most \(s^2\). Uniformly for unit real \(a\), \(W_i=\langle a,x_i\rangle/s\) is thus unit-sub-Gaussian and \(\mathbb EW_i^2\in[c_0,1]\).

With probability at least \(1-e^{-c_*(\log N)^2}\) for some absolute \(c_*>0\), the following estimates hold simultaneously for all real \(a\):
\[
 c_1 m s^2\|a\|^2\le\sum_i\langle a,x_i\rangle^2\le C_1 m s^2\|a\|^2,
 \qquad
 \sum_i\langle a,x_i\rangle^4\le C_2 m s^4\|a\|^4,\qquad
 \max_i\|x_i\|\le C_3 s\sqrt M.                                 \tag{4}
\]
For the quadratic concentration, for each fixed unit \(a\) the centered squares have a uniformly bounded moment generating function on a fixed neighborhood of zero, with log bounded by \(C t^2\) there, by the sub-Gaussian tail. The usual exponential Markov bound therefore controls a fixed positive deviation with failure \(2e^{-cm}\). A sufficiently fine constant-radius Euclidean net with \(e^{O(D)}\) points transfers both lower and upper bounds to the quadratic form: use the net to bound the operator norm and then bound its quadratic-form change between nearby unit vectors.

For the fourth powers at a fixed direction, \(B_i=W_i^2\) have tails \(2e^{-c u}\). Except with probability \(2m e^{-c\sqrt m}\) all \(B_i\le\sqrt m\). At \(h=c'/\sqrt m\), for small absolute \(c'>0\),
\[
 \mathbb E[e^{h B_i^2}{\boldsymbol 1}_{B_i\le\sqrt m}]
 \le1+h\,\mathbb E[B_i^2 e^{c' B_i}]\le1+C h .
\]
An exponential Markov bound then gives \(\Pr[\sum W_i^4>C' m]\le e^{-c''\sqrt m}+2m e^{-c\sqrt m}\) for sufficiently large \(C'\). Use a constant-radius net and the triangle inequality for the empirical \(L^4\) seminorm to pass to all directions. Condition (1) ensures \(\sqrt m/D\to\infty\), so the failure is at most \(e^{-c\sqrt m}\) for large indices. The bound on the maximum column norm follows by applying a fixed-radius net to each sub-Gaussian vector and a union bound over \(m\) vectors at a large multiple of \(\sqrt M\), with failure at most \(e^{-c(\log m)^2}\). The quadratic estimate has failure at most \(e^{-cm}\) for large indices. Here \(\log m\le\log N=O(\log m)\), since (1) implies \(d\le D\le\sqrt m\) eventually.

Write \(\operatorname{dist}(u,\mathbb Z)\) for the distance of a real number to the closest integer. On an event with the same probability bound, with a possibly smaller positive \(c_*\),
\[
  \sum_{i=1}^m\operatorname{dist}(\langle a,x_i\rangle,\mathbb Z)^2
      \ge c_2 m\min(s^2\|a\|^2,1)
      \qquad(a\in[-1/2,1/2]^D).                                 \tag{5}
\]
For \(s\|a\|\le a_0\) with small fixed \(a_0\), apply \(\operatorname{dist}(u,\mathbb Z)^2\ge u^2-4u^4\) and (4). For the complementary region use the scalar characteristic bound
\[
   0<\mathbb E e^{2\pi i\xi U}\le e^{-c_3 s^2\xi^2}
       \quad (|\xi|\le1/2).
\]
For clarity, write \(\tau=2\pi^2s^2\). Poisson summation identifies this characteristic function with \(\sum_{k}e^{-\tau(k+\xi)^2}/\sum_k e^{-\tau k^2}\). If \(|\xi|\le1/4\), factor out \(e^{-\tau \xi^2}\); the logarithm of the remaining ratio is at most
\[
 4\tau^2 \xi^2\sum_{k\ge1}k^2 e^{-\tau(k^2-k/2)}
       \le 8\tau^2 e^{-\tau/2}\xi^2 \le \tfrac12\tau\xi^2,
\]
using \(\cosh u-1\le u^2e^{|u|}/2\), \(\tau\ge2\pi^2\), and summing the resulting geometric series. If \(1/4\le|\xi|\le1/2\), all terms other than a nearest term and possibly its neighbor have sum at most \(0.01\) times the nearest term, by the same exponent comparison. The ratio is at most \(2.01 e^{-\tau\xi^2}\le e^{-\tau\xi^2/3}\). This proves the bound.

By independence within each \(x_i\) the phase expectation at \(a\) is at most \(e^{-c_3s^2\|a\|^2}\), so \(\mathbb E\operatorname{dist}(\langle a,x_i\rangle,\mathbb Z)^2\) is bounded below by a fixed positive constant for \(s\|a\|\ge a_0/2\). This uses \(1-\cos(2\pi u)\le2\pi^2\operatorname{dist}(u,\mathbb Z)^2\). On the cube take a net of radius \(\delta_0/s\) for a sufficiently small absolute \(\delta_0>0\), with \((C_4s\sqrt D)^D\) points. Hoeffding's inequality on the independent bounded summands gives failure at most \(e^{-c_4m}\) at each relevant point. The empirical average of the squared distances is \(C_5s\)-Lipschitz in \(a\): the squared distance is 1-Lipschitz and Cauchy–Schwarz and (4) bound the average absolute increment. Thus the net transfers the estimate to all \(s\|a\|\ge a_0\), with failure \(e^{-cm}\) by (1) and \(s\le N^C\). This proves (5).

A signed permutation preserves both the real norm and the cube. Therefore (4)–(5), applied to \(U_j^{\mathsf T}a\) and summed over \(j\), imply
\[
  c_1 Ns^2 I\preceq AA^{\mathsf T}\preceq C_1 Ns^2 I,\quad
  \max_i\|A_i\|\le C_3s\sqrt M,\quad
  \operatorname{dist}(A^{\mathsf T}a,\mathbb Z^N)^2
      \ge c_2 N\min(s^2\|a\|^2,1)
      \quad(a\in[-1/2,1/2]^D),                                 \tag{6}
\]
where \(A_i\) denotes a real column of \(A\). In particular \(A\) has real rank \(D\) on this event. Also \(A\mathbb Z^N=\mathbb Z^D\): the dual of the image consists of \(a\) with \(A^{\mathsf T}a\in\mathbb Z^N\), and, modulo \(\mathbb Z^D\), (6) allows only zero.

## 3. The full dual theta sum

From now on assume (6). Write \(P\) for orthogonal projection onto \(\ker A\), so \(\Lambda^*=P\mathbb Z^N\). Indeed \(P\) is a rational matrix under full row rank, making \(P\mathbb Z^N\) a lattice in the kernel; its dual consists of the kernel vectors with integral pairing against every standard basis vector, exactly \(\Lambda\).

For each dual point choose a single \(z\in\mathbb Z^N\) projecting to it. Its least-squares row coefficient is \(a=(AA^{\mathsf T})^{-1}Az\) and \(z=Pz+A^{\mathsf T}a\). Subtracting \(A^{\mathsf T}k\), \(k\in\mathbb Z^D\), arranges \(a\in[-1/2,1/2)^D\) without changing \(Pz\). For the zero point choose \(z=0\). Representatives for distinct points are distinct integer vectors; no canonical ordering is needed.

First take the representatives with
\[
        \|a\|\le L:=\frac1{s\sqrt M(\log N)^2}.
\]
Each coordinate of \(A^{\mathsf T}a\) has absolute value \(O((\log N)^{-2})\) by (6). As \(\sum_i|z_i|\le\sum_i z_i^2\), the squared projected length is
\[
        \|z-A^{\mathsf T}a\|^2
            \ge (1-O((\log N)^{-2}))\|z\|^2 .
\]
Excluding zero, sum this bound over all nonzero points of the ordinary cubic lattice. Uniformly for \(t\) in (2), the reduced exponent equals \(t-o(1)\). The ordinary cubic theta at exponent \(t'=t-o(1)\) is
\[
       \left(1+2e^{-t'}+O(e^{-4t'})\right)^N-1
       =(\exp(2Ne^{-t})-1)(1+o(1)),                              \tag{7}
\]
uniformly, because \(Ne^{-t}\) is bounded and \(e^{-t'}/e^{-t}=1+o(1)\).

For a representative with \(\|a\|>L\), (6) implies \(E_z=\|Pz\|^2\ge B\), where \(B=c_2 N/[M(\log N)^4]\). Cover the coefficient cube with a net of radius \(\sqrt B/(4\|A\|_{\mathrm{op}})\), using at most \(\exp(O(D\log N))\) points by (1) and (6). For the closest net point \(b\), orthogonality gives
\[
      \|z-A^{\mathsf T}b\|^2=E_z+\|A^{\mathsf T}(a-b)\|^2
        \le E_z+B/16 .
\]
In particular \(e^{-tE_z}\le e^{-tB/8}\exp[-(3t/4)\|z-A^{\mathsf T}b\|^2]\). For each fixed net point, sum this over all integer vectors; the Gaussian mass of a translate of \(\mathbb Z^N\) is maximized at the untranslated lattice by Poisson summation. At exponent \(3t/4\) this mass has logarithm \(O(Ne^{-3t/4})=O(N^{1/4})\), uniformly over the range in (2). Thus the entire far sum is bounded by
\[
       \exp[-tB/8+O(D\log N)+O(N^{1/4})].
\]
Here \(B/D\to\infty\) by (1), and \(M=O(\sqrt m)=O(\sqrt N)\) implies \(tB\gg N^{1/4}\). It follows that the far sum is \(o(Ne^{-t})\), uniformly. Together with (7) this is the desired upper bound, not a count of short vectors alone.

For the lower bound, the leverage scores are
\(\| (AA^{\mathsf T})^{-1/2} A_i\|^2\le C_6 M/N\). If \(z\) has at most \(k\) nonzero coordinates, Cauchy–Schwarz gives
\(\|(I-P)z\|^2\le C_6 (M/N) k\,\|z\|^2\).
For every fixed \(K\), this shows that for large \(N\) the images of all signed \(0,\pm1\) vectors supported on at most \(K\) positions are distinct: a difference has at most \(2K\) positions and cannot lie in the row space unless zero. Their squared projected lengths are at most their support sizes, giving a lower bound on \(\Theta_A(t)-1\) of
\[
        \sum_{k=1}^K \binom{N}{k}2^k e^{-t k}.
\]
For fixed \(K\) this is asymptotic, uniformly relative to the full bounded-argument exponential profile, to \(\sum_{k=1}^K (2Ne^{-t})^k/k!\). The remaining relative Taylor tail goes uniformly to zero as \(K\to\infty\), also when \(2Ne^{-t}\to0\): divide the tail by its first-order scale \(2Ne^{-t}\). This proves (2). Inverting the profile at fixed additive offsets around \(\log(2N/\log(1+\epsilon_N))\) gives (3), since scaling the exponential argument by \(e^{\pm\delta}\) changes its nonzero mass by at least a fixed relative amount for every \(\delta>0\).

## 4. Consequence for the Gaussian image step

For \(A\) satisfying the good event, draw a spherical discrete Gaussian on \(\mathbb Z^N\) with width \(\lambda\). By decomposing each fiber of \(A\) into its orthogonal row-space component and a translate of the kernel, the mass at \(y\in\mathbb Z^D\) of its image is proportional to
\[
 \exp\!\left(-\frac{\pi}{\lambda^2}\,y^{\mathsf T}
                (AA^{\mathsf T})^{-1}y\right)
      \sum_{z\in\Lambda+c_y} e^{-\pi\|z\|^2/\lambda^2}
\]
for some shift \(c_y\in\ker A\). If \(\Theta_A(\pi\lambda^2)-1\le\epsilon<1\), Poisson summation shows that every shifted factor divided by \(\lambda^{N-D}/\det\Lambda\) lies in \([1-\epsilon,1+\epsilon]\). Thus the total variation from the discrete Gaussian with just the displayed ellipsoidal exponential is at most \(\epsilon/(1-\epsilon)\), by bounding both the pointwise correction and its normalizer. In particular \(\pi\lambda^2=\log(2N/\log(1+\epsilon_N))+\delta\) suffices outside a matrix event of probability at most \(e^{-c_*(\log N)^2}=o(\epsilon_N)\), for every fixed \(\delta>0\) and each tolerance sequence in (3) with \(\epsilon_N<1\). With the matrix label kept, the average total variation is at most \(\epsilon_N/(1-\epsilon_N)+o(\epsilon_N)\). This is the conditional ellipsoidal, not fixed spherical, conclusion, and no conclusion about a specific application follows without its other hypotheses.

## Prior work and limitations

[Albrecht, Felderhoff, Lai, Lapiha and Woo, *A Gaussian Leftover Hash Lemma for Modules over Number Fields*](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), §1.3 and Thm. 4.2, point out the looseness of known kernel smoothing bounds and give an upper bound for much more general fields, Gaussian widths and sample regimes. [Kirshanova, Nguyen, Stehlé and Wallet, *On the smoothing parameter and last minimum of random orthogonal lattices*](https://eprint.iacr.org/2020/057.pdf), Thms. 1 and 4, give upper bounds for integer matrices at substantially smaller sample counts, using dual minima and transference; their Lemma 3 gives the projection identity used here. The result above instead controls the whole projected dual theta, works for broad oversampling with spherical independent coefficients, and replaces the known large upper bound by the exact cubic profile in that narrower regime. It makes no claim for near-square kernels, general number fields, anisotropic Gaussians, or finding a vector in a kernel. The accompanying verifier checks arithmetic and scalar theta estimates on synthetic examples; the proof is analytic.
