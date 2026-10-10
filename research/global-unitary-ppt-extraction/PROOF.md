# Global-unitary entanglement extraction: capacity and exact strong-converse exponents

**Written analytic proof, not Lean-formalized or externally peer reviewed.** All logarithms are natural. The semidefinite characterization used below is due to Rains [R]; we include its elementary proof for the precise operation class needed here. A deterministic local subspace-packing construction supplies the matching bound for all three operation classes. Unlike the preceding negativity-rate argument [Z], this proof needs no matrix concentration theorem or random projector.

## 1. Task and results

Fix integers $2\le m\le n$, a density matrix $\rho$ on $\mathbb C^m\otimes\mathbb C^n$, and its eigenvalue probability vector $p$, with zeros permitted. Set
\[
 A=\log m,\qquad B=\log n,\qquad L=A+B.
 \tag{1}
\]
At blocklength $k$ one first applies an arbitrary global unitary $U_k$ on the existing $m^k\times n^k$ system. One then applies a deterministic channel to two output systems of dimension $K$. No ancillary system is supplied before the global unitary. Local ancillas, discarding, and classical communication are permitted in the subsequent LOCC stage. No postselected branch is renormalized as a deterministic success.

Let $\Phi_K$ be the normalized rank-one maximally entangled projector. For an operation class $\mathcal C$, define the **squared-fidelity convention**
\[
 f_k^{\mathcal C}(K)=\sup_{U_k,\Lambda\in\mathcal C}
 \operatorname{Tr}\!\left[\Phi_K\Lambda(U_k\rho^{\otimes k}U_k^*)\right].
 \tag{2}
\]
We consider local product channels (LO), LOCC, and **completely PPT channels**: both $\Lambda$ and $\Gamma_{\mathrm{out}}\Lambda\Gamma_{\mathrm{in}}$ must be completely positive and trace preserving. Here the partial transposes are taken on the second party. The latter class is denoted $\mathrm{cPPT}$ to avoid confusion with channels that merely send PPT states to PPT states. LOCC is contained in cPPT: partial-transpose conjugation replaces a product Kraus operator $A_j\otimes B_j$ by $A_j\otimes\overline{B_j}$, preserving complete positivity; trace preservation is invariant under the conjugation. The same holds for limits of such channels. The supremum in the cPPT case is a maximum by the finite-dimensional semidefinite formulation below.

For a rate $R\ge0$ use $K_k=\lceil e^{kR}\rceil$, with $K_k=1$ when $R=0$. Write $H(p)=-\sum p_i\log p_i$ and $S_\alpha(p)=(1-\alpha)^{-1}\log\sum p_i^\alpha$ for $\alpha>1$, extended by $S_1=H$.

**Theorem 1 (capacity and strong converse).** The three capacities coincide:
\[
 \boxed{C_{\mathrm{LO}}=C_{\mathrm{LOCC}}=C_{\mathrm{cPPT}}
 =\min\left\{\log m,\frac{\log(mn)-H(p)}2\right\}.}
 \tag{3}
\]
Capacity means the supremum of rates for which the fidelity in (2) tends to one. Every $R<C$ is achievable by a single global unitary followed by local product channels; classical communication is unnecessary. For every $R>C$, even cPPT fidelity tends to zero exponentially. No assertion that fidelity tends to one at $R=C$ is needed.

**Theorem 2 (exact common fidelity exponent).** For every $R\ge0$ and each $\mathcal C\in\{\mathrm{LO},\mathrm{LOCC},\mathrm{cPPT}\}$, the following limit exists, with the same value for all three classes:
\[
 \boxed{\begin{aligned}
 \mathcal E(R)&=\lim_{k\to\infty}-\frac1k\log f_k^{\mathcal C}(K_k)\\
 &=(R-A)_++\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}\bigl(S_\alpha(p)-c_R\bigr),\\
 c_R&=L-2\min\{R,A\}.
 \end{aligned}}
 \tag{4}
\]
The maximand at $\alpha=1$ is defined to be zero. For $0\le R\le A$ this is
\[
 \mathcal E(R)=\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}\bigl(2R-\log(mn)+S_\alpha(p)\bigr).
 \tag{5}
\]
It is zero for $R\le C$ and strictly positive for $R>C$. The converse holds for the largest class cPPT, while deterministic local product channels after the global unitary attain the exponent. Thus (4) is exact even for LO; classical communication or nonlocal cPPT postprocessing gives no improvement at the exponential scale.

Define the preceding logarithmic-negativity rate [Z] by
\[
 \mathcal N(p)=\min_{1\le\alpha\le2}
 \frac{A+(\alpha-1)B+\log\sum_i p_i^\alpha}{\alpha}.
 \tag{6}
\]
An equivalent high-rate consequence is
\[
 \mathcal E(R)=R-\mathcal N(p)\quad(R\ge A).
 \tag{7}
\]
The equality in (7) is established below without assuming that logarithmic negativity is an achievable LOCC yield.

**Relation to a recent converse.** Lami's quadratic converse [L, Corollary 13 and equations (100)--(102)] already implies the entropy-deficit upper bound for fixed-state cPPT distillation: choosing the auxiliary state $\tau=I/N$ makes the quadratic form $N^{-1}\mathrm{id}$ and its logarithmic potential is $\tfrac12\operatorname{Tr}(\rho\log(N\rho))=\tfrac12(\log N-H(\rho))$, with the same logarithm convention. We do not claim this converse principle as new. Below we derive the finite-block inequalities directly from the Rains constraints, uniformly over the varying collective unitaries, and match them by local achievability of the capacity and the exact all-rate fidelity exponent. The cited fixed-input distillation problem has no free global-unitary preprocessing and is not claimed to be solved here.

These are spectrum-optimized extraction statements. The initial global unitary is an entangling resource, so (3) is **not** a formula for the ordinary distillable entanglement of the unrotated state. No claim is made about the exact finite-copy APPT purity conjecture, APPT=AS, or an efficient circuit implementation.

## 2. The fidelity effect: exact necessity and sufficiency

Fix input dimensions $2\le a\le b$, total dimension $N=ab$, and $K\ge2$. Partial transpose is an involution and self-adjoint for the trace pairing. If $\Lambda$ is cPPT, let $M=\Lambda^*(\Phi_K)$. Complete positivity and trace preservation give
\[
 0\le M\le I,\qquad -I/K\le M^\Gamma\le I/K.
 \tag{8}
\]
Indeed $\Phi_K^\Gamma=F_K/K$, where $F_K$ is the swap, with eigenvalues $\pm1$. The adjoint of $\Gamma_{\mathrm{out}}\Lambda\Gamma_{\mathrm{in}}$ is positive and unital, so it preserves the two order bounds on $F_K/K$ and maps it to $M^\Gamma$.

Conversely every $M$ satisfying (8) defines the CPTP map
\[
 \Lambda_M(X)=\operatorname{Tr}(MX)\Phi_K+
 \operatorname{Tr}((I-M)X)\frac{I-\Phi_K}{K^2-1}.
 \tag{9}
\]
Let $Q_\pm=(I\pm F_K)/2$ be the output symmetric and antisymmetric projections. Direct partial transposition gives
\[
 (\Gamma_{\mathrm{out}}\Lambda_M\Gamma_{\mathrm{in}})(X)
 =\operatorname{Tr}\!\left[\frac{I+KM^\Gamma}{K(K+1)}X\right]Q_+
 +\operatorname{Tr}\!\left[\frac{I-KM^\Gamma}{K(K-1)}X\right]Q_-.
 \tag{10}
\]
Both coefficient effects are positive by (8), so this map is completely positive. It is trace preserving: $\operatorname{Tr}Q_\pm=K(K\pm1)/2$, and the two resulting effects sum to $I$. Equation (9) has target overlap $\operatorname{Tr}(MX)$. This proves the precise Rains characterization used here:
\[
 f_{a,b}^{\mathrm{cPPT}}(\lambda,K)
 =\max_{U,M\text{ satisfying }(8)}\operatorname{Tr}(U\operatorname{diag}(\lambda)U^*M).
 \tag{11}
\]
The channel in (9) is not in general LOCC. It is not used for achievability: Section 3 constructs deterministic local product channels instead. Its role here is to establish the exact cPPT optimization and to make the converse operation class unambiguous.

## 3. Converse inequalities and a one-shot spectral envelope

For Hermitian $X$ on $a\times b$,
\[
 \|X^\Gamma\|_\infty\le a\|X\|_\infty.
 \tag{12}
\]
To see this, test $X^\Gamma$ on a unit vector $v$. If $s_j$ are its Schmidt coefficients, the eigenvalues of $(vv^*)^\Gamma$ are $s_j^2$ and $\pm s_i s_j$. Its trace norm is $(\sum s_j)^2\le a$. Trace duality proves (12). Thus (8), together with invariance of the Hilbert--Schmidt norm under partial transpose, implies
\[
 \|M\|_\infty\le\gamma:=\min\{1,a/K\},\qquad
 \operatorname{Tr}M^2\le N/K^2.
 \tag{13}
\]
For $1<\alpha\le2$ let $q=\alpha/(\alpha-1)\ge2$. Then
$\operatorname{Tr}M^q\le\gamma^{q-2}\operatorname{Tr}M^2$.
Hölder's inequality in (11) yields
\[
 f_{a,b}^{\mathrm{cPPT}}(\lambda,K)
 \le\gamma^{(2-\alpha)/\alpha}
       (N/K^2)^{(\alpha-1)/\alpha}
       \left(\sum_i\lambda_i^\alpha\right)^{1/\alpha}.
 \tag{14}
\]
For $\alpha=1$ the bound is $f\le\gamma$. In particular the factor $K^2$, not $K$, in (13) is responsible for the half entropy deficit in the capacity.

Let $\lambda_1\ge\cdots\ge\lambda_N$, $L_r=\sum_{i\le r}\lambda_i$, and
\[
 v_r=\min\{1,a/K,\sqrt{N/r}/K\},\qquad T_K=\max_{1\le r\le N}v_rL_r.
 \tag{15}
\]
The decreasing eigenvalues of $M$ are at most $v_r$, by (13). The singular-value trace inequality and $\lambda_i\le L_i/i$ give
\[
 f_{a,b}^{\mathrm{cPPT}}(\lambda,K)\le\sum_i\lambda_i v_i\le H_N T_K,
 \qquad H_N=\sum_{i=1}^N1/i.
 \tag{16}
\]
The following matching estimate will supply exact asymptotic exponents.

**Lemma 3 (one-shot approximation).** For every input spectrum, every $2\le a\le b$, and every integer $K\ge2$,
\[
 \frac{T_K}{4}\le f_{a,b}^{\mathrm{LO}}(\lambda,K)\le f_{a,b}^{\mathrm{LOCC}}(\lambda,K)\le f_{a,b}^{\mathrm{cPPT}}(\lambda,K)\le H_NT_K.
 \tag{17}
\]
The lower bound is achieved by an explicit global change of eigenbasis followed by local product channels. The Bell-block size is chosen from the target dimension and a spectral-prefix rank; it need not be the full smaller input dimension. The remaining factor $H_N$ is subexponential in tensor-power dimension. In particular cPPT can improve the one-shot optimum over LO by at most a factor $4H_N$ after this global preprocessing.

### 3.1 Deterministic packing at a variable Bell dimension

Fix a prefix rank $1\le r\le N$ and put
\[
 w=\min\{a,K,\sqrt{N/r}\},\qquad
 d=\max\{1,\lfloor w/2\rfloor\},\qquad
 u=\lfloor a/d\rfloor,\quad v=\lfloor b/d\rfloor.
 \tag{18}
\]
These integers satisfy
\[
 1\le d\le\min(a,K),\qquad uv\ge r,\qquad d\ge w/4.
 \tag{19}
\]
If $w<2$, take $d=1$ and $uv=N\ge r$. Otherwise $d\le w/2$ and $d\ge w/4$, since $\lfloor x\rfloor\ge x/2$ for $x\ge1$. Also $a/d,b/d\ge1$, so
$uv\ge N/(4d^2)\ge N/w^2\ge r$. Thus (19) holds without divisibility assumptions.

Identify good local coordinate subspaces with $\mathbb C^d\otimes\mathbb C^u$ and $\mathbb C^d\otimes\mathbb C^v$. There are $uv$ orthonormal vectors
\[
 \psi_{jl}=d^{-1/2}\sum_{x=0}^{d-1}|x,j\rangle_A|x,l\rangle_B,
 \qquad 1\le j\le u,\ 1\le l\le v.
 \tag{20}
\]
Assign the largest $r$ eigenvalues to any $r$ of these vectors, and complete both input and output orthonormal bases to obtain a global unitary. The spectrum is unchanged. The unused good vectors and all other output eigenvectors receive the remaining eigenvalues in any order.

### 3.2 Local channel and fidelity

Alice's output has dimension $K\ge d$. Her local Kraus operators are
\[
 A_j=\sum_{x=0}^{d-1}|x\rangle\langle x,j|\quad(1\le j\le u),
 \qquad A_z=|0\rangle\langle z|\quad\text{for every unused input coordinate }z.
 \tag{21}
\]
The Kraus adjoint products sum to $I_a$. Bob uses the corresponding operators, whose adjoint products sum to $I_b$. Hence these are deterministic local channels, with no postselection or classical communication. Each selected projector $\psi_{jl}\psi_{jl}^*$ maps to the same embedded maximally entangled projector of dimension $d$ inside the $K\times K$ output. Its overlap with $\Phi_K$ is $d/K$: the overlap of the normalized vectors is $\sqrt{d/K}$.

The other input eigenprojectors are mapped to positive states and therefore contribute nonnegatively to the target overlap. It follows that
\[
 f_{a,b}^{\mathrm{LO}}(\lambda,K)\ge(d/K)L_r.
 \tag{22}
\]
Finally, by (19),
\[
 \frac dK\ge\frac{w}{4K}=\frac14\min\{1,a/K,\sqrt{N/r}/K\}
 =\frac{v_r}{4}.
 \tag{23}
\]
Maximizing over $r$ and combining with (16) proves (17). The same reasoning works at $d=1$: every branch outputs the product vector $|0,0\rangle$, of fidelity $1/K$. There is no probabilistic existence argument or unproved projector lemma.

## 4. Tensor powers and the exact variational exponent

Let $s$ be the number of positive eigenvalues, and let $q$ range over probability distributions on that fixed support. Write $D(q\|p)=\sum q_i\log(q_i/p_i)$. For a type with integer counts $kq_i$, the multinomial cardinality $r_q=k!/\prod_i(kq_i)!$ satisfies
\[
 (k+1)^{-s}e^{kH(q)}\le r_q\le e^{kH(q)}.
 \tag{24}
\]
For completeness the probability of that type under law $q$ is $r_q e^{-kH(q)}$. It is at most one and is a mode. To check the latter, the likelihood ratio of any competing counts $h_i$ equals
$\prod_i[(kq_i)!/h_i!](kq_i)^{h_i-kq_i}$ after cancellation of the powers of $k$. Each factor is at most one by comparing its factorial factors with $kq_i$; a competing positive count at a zero coordinate has probability zero. There are at most $(k+1)^s$ types, proving (24).

The mass of type $q$ under $p^{\otimes k}$ is at least $(k+1)^{-s}e^{-kD(q\|p)}$. The largest $r_q$ eigenvalues have at least this mass. Applying (17) in dimensions $a=m^k,b=n^k$ gives the explicit bound
\[
 f_k^{\mathrm{LO}}(K_k) \ge
 \frac{\exp\{-k\,[D(q\|p)+\max\{0,R-A,R-L/2+H(q)/2\}]\}}{8(k+1)^s}.
 \tag{25}
\]
The factor 8 combines the factor 4 in (17) with $e^{kR}\le K_k\le2e^{kR}$; (24) gives the type-size and mass bounds. Approximate an arbitrary $q$ by types of denominator $k$; entropy and relative entropy are continuous on the positive support. Therefore
\[
 \limsup_k-\frac1k\log f_k^{\mathrm{LO}}(K_k)
 \le \min_q\left[D(q\|p)+\max\{0,R-A,R-L/2+H(q)/2\}\right].
 \tag{26}
\]
Put $d=(R-A)_+$ and $c=c_R=L-2\min(R,A)$. A direct two-case check ($R\le A$ or $R\ge A$) shows that the objective in (26) is
\[
 d+D(q\|p)+\tfrac12(H(q)-c)_+.
 \tag{27}
\]
On the other hand applying (14) to tensor powers proves
\[
 \liminf_k-\frac1k\log f_k^{\mathrm{cPPT}}(K_k)
 \ge d+\max_{1\le\alpha\le2}J_c(\alpha),\qquad
 J_c(\alpha)=\frac{\alpha-1}{\alpha}(S_\alpha(p)-c).
 \tag{28}
\]
For $R=0$, fidelity is exactly one. Otherwise $K_k\ge2$ eventually and all preceding inequalities apply.

### 4.1 Matching without an assumed minimax exchange

Write $Z_\alpha=\sum_{p_i>0}p_i^\alpha$ and $q_{\alpha,i}=p_i^\alpha/Z_\alpha$. Differentiation gives
\[
 J_c'(\alpha)=\frac{H(q_\alpha)-c}{\alpha^2},\qquad
 \frac{d}{d\alpha}H(q_\alpha)=-\alpha\operatorname{Var}_{q_\alpha}(\log p_i)\le0.
 \tag{29}
\]
If $H(p)\le c$, the maximum in (28) is $J_c(1)=0$. The choice $q=p$ makes the nonconstant term in (27) zero.

If $H(q_2)\ge c$, the maximum is at $\alpha=2$. Choosing $q=q_2$ gives
\[
 D(q_2\|p)+\tfrac12(H(q_2)-c)=\tfrac12(S_2(p)-c)=J_c(2).
 \tag{30}
\]
In the remaining case $H(q_2)<c<H(p)$, choose $\alpha_*\in(1,2)$ with $H(q_{\alpha_*})=c$. This maximizes $J_c$, and is unique unless the positive eigenvalues are all equal; that exceptional case cannot satisfy the strict intermediate inequalities. If $\ell_\alpha=\sum_iq_{\alpha,i}\log p_i$, then
\[
 H(q_\alpha)=-\alpha\ell_\alpha+\log Z_\alpha,\quad
 D(q_\alpha\|p)=(\alpha-1)\ell_\alpha-\log Z_\alpha.
\]
Substituting $H(q_{\alpha_*})=c$ yields
\[
 D(q_{\alpha_*}\|p)=J_c(\alpha_*).
 \tag{31}
\]
The boundary cases agree. Thus the LO lower construction (26) matches the cPPT converse (28). Since $f_k^{\mathrm{LO}}\le f_k^{\mathrm{LOCC}}\le f_k^{\mathrm{cPPT}}$ at every blocklength, the same limit exists for all three classes, proving (4). In particular we have the fully proved identity
\[
 \min_q\{D(q\|p)+\tfrac12(H(q)-c)_+\}
 =\max_{1\le\alpha\le2}J_c(\alpha)\quad(c\ge0).
 \tag{32}
\]
Here $c_R\ge B-A\ge0$. No unproved exchange of extrema, finite grid, or optimizer is used. For $R\ge A$, substituting $c_R=B-A$ into (4) and rearranging proves (7).

## 5. Strong converse and the entropy threshold

For $R\le A$, (29) shows that $\mathcal E(R)=0$ precisely when $L-2R\ge H(p)$. If this inequality fails, $J_c'(1)>0$, so some $\alpha>1$ gives a strictly positive exponent. For $R>A$, $d>0$ and the maximum in (4) is nonnegative. It follows that every rate above (3) has exponentially vanishing cPPT fidelity, and hence exponentially vanishing LOCC fidelity as well.

This proof of the converse uses the complete-PPT order constraints, not an assumed Shannon formula for ordinary mixed-state entanglement. A weaker bound derived only by testing a maximally mixed separable input would control $\operatorname{Tr}M$ by $N/K$, which would lose the factor of two and would not prove (3).

## 6. Achievability by local extraction after the global unitary

The packing construction in Section 3 can be used with $d=K$ rather than the constant-factor choice in (18), whenever $1\le K\le a$. In that case it supplies
\[
 r=\lfloor a/K\rfloor\lfloor b/K\rfloor
 \tag{33}
\]
exactly extractable good eigenvectors, with the same complete local Kraus maps. Since the target overlap of each good output is now one, (22) strengthens to
\[
 f_{a,b}^{\mathrm{LO}}(\lambda,K)\ge L_{\lfloor a/K\rfloor\lfloor b/K\rfloor}.
 \tag{34}
\]
The unused coordinates are still included in the trace-preserving local channels. No postselected branch or renormalized success probability is used.

Fix $0<R<C$. Then $R<A\le B$, and
\[
 k^{-1}\log\bigl(\lfloor m^k/K_k\rfloor\lfloor n^k/K_k\rfloor\bigr)
 \longrightarrow L-2R>H(p).
 \tag{35}
\]
For a direct proof that the corresponding prefix mass tends to one, sample $X$ with law $p$ on its positive support. The random variable $-\log p_X$ is finite and has mean $H(p)$. The law of large numbers implies that the words whose self-information is at most $k(H(p)+\epsilon)$ have total mass tending to one. Each such word has probability at least $e^{-k(H+\epsilon)}$, so there are at most $e^{k(H+\epsilon)}$ of them. For fixed sufficiently small $\epsilon>0$, (35) makes this number no larger than the prefix rank in (34), eventually. Thus (34) tends to one. Rate zero is trivial. With the converse this proves all three capacity equalities in (3), including the case $C=0$.

## 7. Consequences and boundaries

### 7.1 A strict distinction from negativity growth

For $m=n=d$, the capacity is
\[
 C=\log d-\tfrac12H(p),
 \qquad \mathcal N(p)=\log d-\tfrac12S_2(p).
 \tag{36}
\]
Unless the positive eigenvalues are all equal, $H(p)>S_2(p)$ and therefore $C<\mathcal N(p)$. The entropy inequality follows from Jensen's inequality for $-\log$ under the probability weights $p_i$: $H(p)\ge-\log\sum_i p_i^2$, with equality exactly for a uniform positive support. Thus the previous negativity rate must not be identified with an achievable faithful extraction rate.

For the qutrit APPT example $p=(3,1,1,1,1,1,1,1,1)/11$,
\[
 C=\tfrac12\left(\log9-\log11+\tfrac3{11}\log3\right),\qquad
 \mathcal N(p)=\tfrac12\log(153/121).
 \tag{37}
\]
Both are positive and the first is strictly smaller. The previously Lean-certified one-copy APPT property supplies context, not a premise in this proof.

### 7.2 Rank-deficient and flat spectra

If $p$ is uniform on $s$ positive entries, all its Rényi entropies equal $\log s$. Equations (3)--(4) reduce to
\[
 C=\min\{A,\tfrac12\log(mn/s)\},\qquad \mathcal E(R)=(R-C)_+.
 \tag{38}
\]
This includes pure inputs ($s=1$). For the fully maximally mixed input ($s=mn$), the optimum fidelity is exactly $1/K$: the input stays PPT under every global unitary, a cPPT channel keeps it PPT, and a PPT state's overlap with $\Phi_K$ is at most $1/K$. Product output achieves equality.

### 7.3 An interior Rényi branch really occurs

Take $m=2,n=8$ and $p=(w,1,1,1,1,0,\ldots,0)/(w+4)$ with $w=2^{4/3}$. At target rate $R=\log2$, $c_R=\log4$. The escort distribution at $\alpha=3/2$ is $(1/2,1/8,1/8,1/8,1/8)$, whose entropy is exactly $\log4$. Since the positive eigenvalues are unequal, (29) proves strict monotonicity of escort entropy and a unique interior optimizer. Its exponent is
\[
 \mathcal E(\log2)=\log(4+2^{4/3})-\tfrac83\log2>0.
 \tag{39}
\]
The positivity also follows from $H(p)>H(q_{3/2})$ and (29). It is not legitimate to retain only $\alpha=1,2$ in the general fidelity exponent.

### 7.4 What is and is not resolved

The fixed-dimension, arbitrary-spectrum capacity and the entire fidelity exponent are resolved for all three stated two-stage operation classes. The below-capacity optimal error exponent, standard fixed-input LOCC or PPT distillation without global preprocessing, finite-copy APPT purity, and APPT=AS are different questions and are not claimed here. In particular the word PPT always means the explicitly defined **complete** partial-transpose-conjugation condition when applied to channels in the theorem.

The proof supplies a finite one-shot approximation (17), a deterministic local extraction construction, and a matching exponent argument, not merely numerical evidence. Given an input eigenbasis, it selects a spectral-prefix rank and a Bell-block dimension explicitly; it does not assert polynomial-size global circuits as a function of the number of copies. The old immutable qutrit and negativity publications are not modified.

## References and attribution

[R] Eric M. Rains, *A semidefinite program for distillable entanglement*, IEEE Transactions on Information Theory **47** (2001), 2921--2933, arXiv:quant-ph/0008047. The fidelity-effect constraints and isotropic-output construction are credited to this work, not claimed as new.

[L] Ludovico Lami, *On PPT entanglement distillation*, arXiv:2610.12454v1, submitted 8 October 2026. Corollary 13 and equations (100)--(102) give the quadratic converse whose maximally mixed auxiliary state yields the entropy-deficit expression. Credited for that prior converse; not needed as an external premise for the direct finite-block proof here.

[Z] Yongxian Zhang, *The collective-unitary logarithmic-negativity rate of every bipartite spectrum*, repository preprint, immutable [version 1](https://github.com/mxym/math/releases/tag/collective-unitary-negativity-rate-preprint-v1), source `3fac265d142cbc5ce48700abce5cced59a1a4b8f`. That companion establishes the negativity rate (6) with a stronger fixed-full-Bell-basis restriction. The present variable-block packing avoids its random-projector method; neither result is represented as Lean-formalized. The rate comparison in (7) follows algebraically from the displayed formulas.

[FWTD] Kun Fang, Xin Wang, Marco Tomamichel and Runyao Duan, *Non-asymptotic entanglement distillation*, IEEE Transactions on Information Theory **65** (2019), 6454--6465, arXiv:1706.06221v3. Related finite-blocklength PPT optimization; it does not supply the spectrum-optimized exponent asserted here.

[LLF] Zhiwen Lin, Ke Li and Kun Fang, *Exponential Analysis for Entanglement Distillation*, arXiv:2601.10190v2. Their operational definitions must not be conflated with the global-unitary preprocessing and completely PPT channels in this paper; in particular PPT-state-preserving operations in their Example 1 are defined by state preservation, not by complete positivity of partial-transpose conjugation. Used for scope comparison, not as a proof premise.

[K] Tulja Varun Kondra, Pedro Barrios Hita, Justus Neumann, Hermann Kampermann and Dagmar Bruß, *Fundamental limitations on entanglement extraction from purity*, arXiv:2605.29197v1, Supplemental Lemma 6. Qualitative finite-copy activation was known and is not claimed as a new contribution here.

The elementary pure-subspace packing and typicality argument are standard information-theoretic methods. The contribution claimed here is the local achievability matching the entropy converse under collective global-unitary preprocessing, and the exact, single-letter, all-spectrum common fidelity exponent using deterministic variable-block packing. Literature screening is not an exhaustive novelty or priority certification. Independent mathematical review remains necessary; finite ancillary calculations and successful document compilation do not certify the whole analytic proof.
