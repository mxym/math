# How erasure failure changes a Gaussian Fourier measurement

A quantum Gaussian-sampling step may end by erasing a register and Fourier-measuring the register that remains. Average decoding error and uniform per-input decoding error are not interchangeable in this step. A clean compute–subtract–uncompute model admits an explicit error bound using both the mean and the second moment of the conditional failure probability. For a one-dimensional Gaussian amplitude, the worst Fourier-measurement discrepancy under average error alone can be found to leading order, including the constant.

This treats an abstract erasure subroutine and the law of its final measurement. It does not construct a decoding oracle, solve a lattice or Ring-LWE instance, or change the hypotheses of a hardness reduction.

## Conditional failure and the clean branch

Let $G$ be a finite abelian group labeling the retained register. Its normalized amplitude vector is $f=(f_y)_{y\in G}$. The register to erase has a definite classical value $a_y$ on each basis component, so the starting state is $\sum_y f_y|y\rangle|a_y\rangle|0\rangle$. Whatever its implementation, the decoder is modeled by a unitary $U_y$ on a workspace, controlled by the retained label $y$, with an outcome-label register. The probability that its label is **not** $a_y$, when run from workspace zero, is $q_y$. Apply the unitary, subtract its outcome label in the erasure register, and apply $U_y^\dagger$ to the workspace. Distinct possible decoder labels give distinct erasure residuals at fixed $y$.

Write $p_y=1-q_y$. The branch in which both the erased register and the workspace are zero has amplitude $f_y p_y$, not $f_y\sqrt{p_y}$. Indeed only the correct outcome projector $\Pi_{a_y}$ gives residual zero, and the coefficient of workspace zero after uncomputation is
$\langle0|U_y^\dagger\Pi_{a_y}U_y|0\rangle=p_y$.
After tracing out these two registers the retained state is exactly

$$
\rho=|fp\rangle\langle fp|+J,\qquad J\succeq0,\qquad
\operatorname{tr}J=1-\|fp\|_2^2 .
\tag{1}
$$

Here $fp$ means entrywise multiplication; no assumption is made on the retained state's junk term $J$ beyond (1).

Let $\delta=\sum_y|f_y|^2q_y$ and $v=\sum_y|f_y|^2q_y^2$. Set $a=1-\delta$, $b=1-2\delta+v$. If $P$ is the output of any fixed measurement (including one after a Fourier transform) and $Q$ its perfect-erasure law, then

$$
d_{\rm TV}(P,Q)
 \le \tfrac12\left(1-b+\sqrt{(1+b)^2-4a^2}\right)
 \le \delta+\sqrt v .
\tag{2}
$$

The first inequality follows from the rank-at-most-two trace norm of $|f\rangle\langle f|-|fp\rangle\langle fp|$: its trace is $1-b$ and the determinant on their span is $a^2-b$, yielding the square root in (2), with the same result by continuity if the span is one-dimensional. The remaining trace norm is $\operatorname{tr}J=1-b$. For the simpler bound, split the rank-one difference as two outer products involving $f-fp$, so its trace norm is at most $(1+\sqrt b)\sqrt v\le2\sqrt v$. A uniform guarantee $q_y\le\epsilon$ therefore gives $d_{\rm TV}\le2\epsilon$. An average guarantee alone gives only $v\le\delta$ in this estimate.

The linear scale for uniform error cannot be improved in the abstract model. On $G=\mathbb Z/2\mathbb Z$ take the uniform amplitudes and true erased value $a_y=y$. For $p=1-\epsilon$ use a two-dimensional workspace and choose columns of $U_y$ equal to

$$
\sqrt p\,|y\rangle+\sqrt\epsilon\,|1-y\rangle,\qquad
(-1)^y(\sqrt\epsilon\,|y\rangle-\sqrt p\,|1-y\rangle).
$$

After clean erasure, the auxiliary states on the two retained labels have inner product $(p-\epsilon)^2$: their residual-zero workspace components have coefficients $(p,(-1)^y\sqrt{p\epsilon})$ and their residual-one components have coefficients $(\epsilon,-(-1)^y\sqrt{p\epsilon})$. Hence the Fourier measurement has probability $2p\epsilon$ on the incorrect frequency, whereas the perfect erasure has zero mass there.

## Sharp average-only obstruction for a Gaussian amplitude

Use the continuous Fourier transform with phase $e^{-2\pi i\xi x}$, and let $f(x)=2^{1/4}e^{-\pi x^2}$, so $\|f\|_2=1$ and $\widehat f=f$. The continuous measurement model has conditional failure $q:\mathbb R\to[0,1]$ and $\int f^2q=\delta$, and allows output densities

$$
P(\xi)=|\widehat{f(1-q)}(\xi)|^2+j(\xi),\quad j\ge0,\quad
\int j=1-\|f(1-q)\|_2^2 .
\tag{3}
$$

This is the continuous analogue of the clean-branch constraint (1), not an assumption that every choice of $j$ is physically attainable. Put $Q=f^2$ and let $R$ be determined by $\int_{|x|\ge R}f^2=\delta$. The supremum over (3) has the sharp asymptotic

$$
\begin{split}
\sup d_{\rm TV}(P,Q)
 &\sim \frac{2}{\pi}\left(\int f\right)\int_{|x|\ge R} f(x)\,dx\\
 &\sim \frac{4}{\pi^{5/4}}\sqrt{\delta}\,
               \bigl(\log(1/\delta)\bigr)^{-1/4},\qquad \delta\downarrow0 .
\end{split}
\tag{4}
$$

A two-valued auxiliary flag realizes the leading term: it only indicates whether $x$ is in the two tails, thus removing coherence between the core and the tails. In particular no universal $O(\delta^\beta)$ bound for any $\beta>1/2$ can follow from an average guarantee in such one-dimensional Gaussian inputs. The logarithmic correction in (4) is specific to this model, not a bound claimed in general dimension.

**Upper bound.** Let $h=fq$. Expand (3), noting that $\widehat f=f$ is real:

$$
d_{\rm TV}(P,Q)
 \le \int f(\xi)|\Re\widehat h(\xi)|\,d\xi
       +\tfrac12\bigl(\|h\|_2^2+\int j\bigr)
 = \int f(\xi)|\Re\widehat h(\xi)|\,d\xi+\delta.
\tag{5}
$$

Since $h$ is nonnegative, the last integral without $\delta$ is at most $\int h(x)A(x)\,dx$, where $A(x)=\int f(\xi)|\cos(2\pi x\xi)|\,d\xi$. By the Riemann–Lebesgue lemma (or the absolutely summable Fourier series for the absolute cosine), $A(x)\to(2/\pi)\int f$ as $|x|\to\infty$. Uniformly over all $q$, the contribution from any fixed compact $x$ range is $O(\delta)$: on it $h=f^2q/f$ and $f$ is bounded below. Also

$$
\int h\le\int_{|x|\ge R}f .
$$

To see this without any continuity assumption on $q$, subtract $q_*(x)={\bf1}_{\{|x|\ge R\}}$. Both have the same $f^2$-weighted mass, and $(q-q_*)(1/f-1/f(R))\le0$ throughout. Integrating with weight $f^2$ gives the inequality. Taking the compact range large and then $\delta$ small establishes the leading upper bound in (4).

**Lower bound.** Keep just the two orthogonal flag values for $f-h$ and $h$ with $q=q_*$. The exact density is $|\widehat{f-h}|^2+|\widehat h|^2$. As $h$ is even, its Fourier transform is real, and the resulting TV differs from $\int f|\widehat h|$ by at most $\delta$. Put $T_R=\int_{|x|\ge R} f$. On the positive tail with weights proportional to $f$, the mean excess $x-R$ is $O(1/R)$, by substituting $x=R+t/R$ into the Gaussian integrals. The cosine Lipschitz bound therefore gives

$$
|\widehat h(\xi)-T_R\cos(2\pi R\xi)|
 \le O(T_R/R)\,|\xi|.
$$

Integrating against $f$ and averaging the absolute cosine gives $\int f|\widehat h|\sim (2/\pi)(\int f)T_R$. Finally Gaussian tail integration gives $T_R\sim 2^{1/4}e^{-\pi R^2}/(\pi R)$ and $\delta\sim 2^{1/2}e^{-2\pi R^2}/(2\pi R)$. Thus $\delta=o(T_R)$ and (4) follows with the indicated constant.

## Finite Fourier witnesses

The obstruction is not specific to a continuous measurement. For odd $N$, take $\mathbb Z/N\mathbb Z$, centered indices $k$, mesh $h_N=N^{-1/2}$ and period $L_N=\sqrt N$. Normalize the amplitude vector with components

$$
\sqrt{h_N}\sum_{\ell\in\mathbb Z}f(kh_N+\ell L_N).
$$

Use a deterministic flag when $|kh_N|\ge R$. It is realizable in (1) by a constant true erased label and a deterministic other label on the flagged components, both giving cleared workspace. For each fixed $R$, the failure mass converges to its continuous value. The normalized discrete Fourier transform of each of the two amplitude pieces, divided by $\sqrt{h_N}$, converges on bounded sets of frequency grid points to the corresponding continuous transform by Riemann summation: with this mesh the frequency point indexed by $j$ is $jh_N$. The periodic alias terms vanish in the weighted absolute sum, bounded by a Gaussian tail. On each bounded frequency range this convergence is uniform by the Gaussian majorant and the two fixed jump points of the mask. Viewing each measurement law as a density constant on cells of width $h_N$ gives pointwise convergence, and the densities have mass one, so Scheffé's lemma yields total-variation convergence for the ideal and flagged laws. For a sequence of increasing $R$, choose $N$ large enough at each step to make these differences and the failure-mass error $o(\delta)$, where $\delta$ is the corresponding continuous tail mass. This supplies finite Gaussian witnesses with the lower asymptotic in (4), without a complexity claim about discretization.

## Scope and primary precedents

[Regev, §3.2.2](https://arxiv.org/abs/2401.03703) uses erasure followed by Fourier transformation in the quantum Gaussian-sampling step. [Peikert–Regev–Stephens-Davidowitz, Lemma 6.7](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) require an oracle that succeeds with all but negligible probability in their GDP setting. [Shutty et al., Theorem 1](https://arxiv.org/abs/2604.24633) analyze square-root losses from average failures for a related finite-code reduction; [No Exponential Quantum Advantage for Decoded Quantum Interferometry with Local Quantum Decoders, Proposition 7.3](https://arxiv.org/abs/2611.12718) addresses a different, heralded preparation in a structured decoder model. The claims here are the conditional-accuracy refinement for the stated clean erasure, and exact Gaussian Fourier-output asymptotics showing why average error cannot simply be substituted for uniform error in a linear budget. They do not verify that the published GDP oracle obeys a uniform guarantee, nor alter the reduction or its runtime.

The toy verifier checks the finite clean-branch identities and compares small Gaussian Fourier examples. The sharp asymptotic and its finite-grid consequence are analytic.
