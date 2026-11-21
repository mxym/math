# Which primitive-character phases survive a short prime correction?

This is an exact appendix to [Short prime corrections](ShortPrimeCorrectionRail.md), not a new lower bound for Goldbach pairs. It compares that additive correction with the signed primitive-character projection in Gou–Wang–Xu, [*Landau's problems through ratios of L-functions*](https://arxiv.org/abs/2611.18825), §§1, 3 (November 2026). Their Theorem 1.1 assumes **both** Dirichlet GRH and the uniform all-primitive-conductor 2/2 ratios Hypothesis 1.1. The calculation below uses neither and does not establish either. Its input is just character orthogonality and the Chinese remainder theorem.

**Notation.** Let \(N\ge4\) be even, \(G=(\mathbb Z/N)^\times\), \(h=\phi(N)\). For \(\chi\in\widehat G\) let \(f\mid N\) be its primitive conductor. On the unit-pair matrix \(1_{a+b=\Delta\bmod N}\), the coefficient belonging to the conjugate pair \((\chi,\bar\chi)\), before Fourier normalization, is
\[
 J_\Delta(\chi)=\sum_{a,b\in G,\ a+b=\Delta\bmod N}\chi(a)\bar\chi(b).
\]
Here and below \(p+p'=N-Qr\) has displacement \(\Delta=-Qr\bmod N\). The results depend only on \((\Delta,N)\). They concern **this diagonal**, not the full matrix: in general other pairs of characters contribute to a shifted count.

**Exact multiplier.** For each \(\ell^e\Vert N\), put \(u=\min(v_\ell(\Delta),e)\), with \(u=e\) at zero, and \(j=v_\ell(f)\). Then
\[
 J_\Delta(\chi)/h=\chi(-1)\prod_{\ell^e\Vert N} L_\ell(e,u,j).
\]
The factor is \(1\) if \(u=e\). For \(0\le u<e\) it is
\[
 \begin{cases}
 (\ell-2)/(\ell-1),&u=j=0,\\
 1,&0<u,\ j\le u,\\
 -1/(\ell-1),& j=u+1,\\
 0,&j>u+1.
 \end{cases}
\]
In particular for even displacements the diagonal is nonzero **if and only if**
\(f/\operatorname{rad}(f)\mid\Delta\), with \(\operatorname{rad}(1)=1\).
Thus if \(0<|\Delta|<f/\operatorname{rad}(f)\) the entire signed \(f\)-diagonal is invisible in this correction, no matter how many prime pairs the correction has. If \(N\) is squarefree this size observation says nothing for nonzero \(\Delta\).

*Proof.* Split by CRT. Write \(s=-a/b\) locally. For given \(s\), the equation \((1-s)b=\Delta\) with \(b\) a unit has no solution unless \(\min(v_\ell(1-s),e)=u\). In the latter case the number of solutions is the same for every eligible \(s\): it is the size of the kernel of reduction on units modulo \(\ell^{e-u}\), or \(\phi(\ell^e)\) for \(u=e\). For \(0<u<e\) the eligible set is the difference of consecutive subgroups \(s=1\bmod\ell^u\) and \(s=1\bmod\ell^{u+1}\); their sizes have ratio \(\ell:1\). The sum of a character over a subgroup is its size if trivial there and zero otherwise. For \(u=0\), subtract the subgroup \(1\bmod\ell\) from the full unit group; their sizes have ratio \((\ell-1):1\), and there is one unit \(b\) per eligible \(s\). For \(u=e\), only \(s=1\) occurs. Multiplication by \(\chi(-1)\) completes the formula. At odd \(\Delta\) the matrix itself is zero for even \(N\).

**What the primitive lift actually measures.** Take real finitely supported weights \(A(x),B(y)\) on integers coprime to \(N\); for primes use only \(p\nmid N\). Put \(\widehat A(\chi)=\sum_x A(x)\chi(x)\) and similarly for \(B\). For each \(f\mid N\) define
\[
 D_f=\sum_{\chi\bmod N:\ {\rm cond}(\chi)=f}\chi(-1)\widehat A(\chi)\overline{\widehat B(\chi)}.
\]
There is exactly one lift to \(N\) of each primitive character modulo \(f\), with all nonunits of \(N\) deleted even if they are units modulo \(f\). For smooth bounded weights times \(\log p\), removing those extra primes from an unrestricted sum modulo \(f\) costs at most \(\|w\|_\infty\log N\) per transform. No conductor multiplicity is introduced. For an actual pair \(p+p'=N\), either summand nonunit implies \(p=p'=N/2\); this exceptional case \(N=2p\) is already represented.

On the designated unit weights, character orthogonality and Möbius inversion give exactly
\[
 D_f=\sum_{d\mid f}\mu(f/d)\phi(d)\sum_{x+y=0\bmod d} A(x)B(y).
\]
There is no factor \(1/\phi(d)\) inside the primitive sum. At modulus \(N\) the full congruence count is \(\sum_{f\mid N}D_f/h\). In particular, if **every** pair of support points satisfies \(|x+y-N|<f/\operatorname{rad}(f)\), every nonzero Möbius term tests precisely \(x+y=N\), so
\[
 D_f=\phi^*(f)\sum_{x+y=N}A(x)B(y),
 \qquad \phi^*(f)=\sum_{d\mid f}\mu(f/d)\phi(d).
\]
This holds also for distinct complementary windows, not necessarily a norm square. For nonnegative weights these particular high-conductor signed blocks are nonnegative, and they vanish at an unrepresented target. In this range, knowing a shifted positive count is not an independent estimate for this unshifted block.

**Sharp dyadic endpoint.** For \(N=2^n,\ n\ge3\), and \(1\le a=v_2(\Delta)<n\), the normalized multiplier relative to \(\chi(-1)\) is \(1,-1,0\) according as \(v_2(f)\le a,=a+1,>a+1\). For \(\Delta=N/2\) there are *no* off-diagonals in the multiplicative transform: on odd classes \(\Delta-x=(N/2-1)x\bmod N\). All \(f<N\) phases agree with the unshifted reflection; precisely the top \(f=N\) phases change sign. Consequently on boxes with \(|x+y-N|<N/2\) this displaced count is identically zero, and the identity gives \(D_N=\phi(N)R/2\) where \(R=\sum_{x+y=N}A(x)B(y)\). It folds the problem to modulus \(N/2\); it does not estimate \(R\). Arbitrary smaller shifts do not enjoy this full-matrix diagonalization. These identities do not show that nonlinear combinations of corrected information could never recover a target.

The standard-library checker reconstructs each complete unit-pair difference histogram by **inverse Fourier transform of the predicted conductor multipliers**, compares the result on every unit with direct addition/enumeration, and separately checks the prime-window and sharp dyadic statements. Run `python3 -O check_primitive_correction_diagonal.py`.
