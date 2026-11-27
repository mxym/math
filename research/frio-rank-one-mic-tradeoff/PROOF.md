# Rank-one FRIO measurements: support-complete clipping and a simultaneous-MIC obstruction

## 1. Model and result

Let $\rho$ be a density operator on $\mathbb C^d$, $d\ge1$. Alice uses a known POVM $M=(M_i)_{i=1}^n$, $M_i=|m_i\rangle\langle m_i|\ne0$, $\sum_i M_i=I_d$; hence $n\ge d$. Eve may hold a purification of $\rho$, but has no extra information about the measurement device. Her measurement has $n$ possible guesses and a reject outcome. Let $S_M(Q)$ be her maximal **unconditional** probability of a correct guess subject to **exact** reject probability $Q\in[0,1]$.

Write $P$ for the support projector of $\rho$, $r=\operatorname{rank}\rho$, and $\lambda_j>0$ for its eigenvalues on $P$. Set $s=1-Q$. Take $u\in[0,\sqrt{\lambda_{\max}}]$ such that
$$
\sum_{j=1}^r h_j^2=s,\qquad h_j=\min(\sqrt{\lambda_j},u).
\tag{1}
$$
The left side is continuous and strictly increasing on that interval; thus the choice is unique there. At $Q=0$, all larger choices would give the same $h_j$; we use the right endpoint. Equal eigenvalues or coincident thresholds need no tie-breaking. Let $A_Q$ have eigenvalues $h_j$ in this eigenbasis of $\rho$, and zero on the kernel. Put
$$
v_n(Q)=\frac{(\operatorname{Tr}A_Q)^2}{n}.
\tag{2}
$$
For every fixed $n\ge d$:
$$
\min_{M\ \text{rank one, }n\text{ outcomes}} S_M(Q)=v_n(Q).
\tag{3}
$$
If $Q<1$, equality for a given $M$ holds exactly when every $\operatorname{Tr}(M_i A_Q)=\operatorname{Tr}(A_Q)/n$. When $Q=1$, all $M$ have value zero. In fact
$$
S_M(Q)\ge v_n(Q)+\sum_{i=1}^n\left(\operatorname{Tr}(M_iA_Q)-\frac{\operatorname{Tr}A_Q}{n}\right)^2.
\tag{4}
$$

This extends the domain of Curran v4 Theorem 3. The clipping formula and squared-gap/equality criterion for full-rank projective measurements are already in that work, using the earlier Nakahira–Usuda–Kato discrimination construction. Sections 4 and 5 distinguish separate rate-wise MIC attainment from optimizing one MIC over every rate.

## 2. Feasible conclusive effects and a matching dual bound

Use the canonical purification in the chosen eigenbasis of $\rho$. For each Alice outcome, the unnormalized Eve state on the copy of $P$ is
$$
\sigma_i=|w_i\rangle\langle w_i|,\qquad
w_i=\sqrt{\rho}\,\overline m_i,\qquad
\sum_i \sigma_i=\rho,
\tag{5}
$$
where the bar is coordinatewise complex conjugation and $\sqrt\rho$ also projects away the kernel. This follows by contracting the Alice register of $\sum_j\sqrt{\lambda_j}|j\rangle|j\rangle$ with $\langle m_i|$. Compression of Eve's POVM to its occupied support preserves all probabilities; a POVM on that support extends to the kernel by assigning it to reject. Different purifications are equivalent on the occupied support. More generally any extension of $\rho$ is obtainable from a purification by a channel on Eve's system: purify the extension, identify the two purifying supports by an isometry, and discard the additional environment. Pulling a POVM back by its adjoint preserves both the success and reject probabilities.

Thus Eve maximizes $\sum_i\operatorname{Tr}(\sigma_iN_i)$ over $N_i\succeq0$, $\sum_iN_i\preceq I_P$, and $\operatorname{Tr}(\rho\sum_iN_i)=s$. This set is compact and nonempty at every rate, for example by mixing one fixed guess with independent rejection. For $Q=1$, positivity and invertibility of $\rho$ on $P$ force $\sum_iN_i=0$; for $Q=0$ they force $\sum_iN_i=I_P$.

On $P$ define the diagonal operator $F=A_Q\rho^{-1/2}$. For all $Q$, $0\preceq F\preceq I_P$. The following conclusive effects are feasible:
$$
N_i=F\,\overline{M_i}F,\qquad \sum_iN_i=F^2,\qquad
\operatorname{Tr}(\rho F^2)=s.
$$
Each correct contribution is $|\langle w_i,F\overline m_i\rangle|^2=(\operatorname{Tr}M_i A_Q)^2$, using that $A_Q$ is diagonal and real in this basis. The sum and the identity $\sum_i\operatorname{Tr}(M_iA_Q)=\operatorname{Tr}A_Q$ prove (4).

Assume $Q<1$ and that the traces are all $\alpha=\operatorname{Tr}A_Q/n>0$. Define on $P$
$$
D=\alpha\,\operatorname{diag}(\lambda_j/h_j),\qquad
\mu=\alpha/u,\qquad Y=D-\mu\rho.
$$
Here $h_j>0$ on $P$, $D\succ0$, and $Y\succeq0$ because $h_j\le u$. The elementary rank-one order test is $D\succeq |w\rangle\langle w|$ iff $\|D^{-1/2}w\|^2\le1$; it follows by conjugating with $D^{-1/2}$. In the present case
$$
\langle w_i,D^{-1}w_i\rangle=\alpha^{-1}\operatorname{Tr}(M_i A_Q)=1.
$$
Consequently for every feasible conclusive POVM the success is at most
$$
\sum_i\operatorname{Tr}\big((Y+\mu\rho)N_i\big)\le \operatorname{Tr}Y+\mu s.
$$
On any coordinate with $h_j=u$, $Y$ vanishes; on the others $h_j=\sqrt{\lambda_j}$ and $F=I$ there. Hence the last bound equals
$$
\operatorname{Tr}(YF^2)+\mu\operatorname{Tr}(\rho F^2)
=\operatorname{Tr}(DF^2)
=\alpha\operatorname{Tr} A_Q
=v_n(Q).
$$
No inversion on the kernel or invocation of strict SDP feasibility is required. This applies at $Q=0$ as written. It shows sufficiency of the trace condition, and (4) shows necessity.

For existence, choose $m_i$ to be the columns of the first $d$ rows of the normalized $n\times n$ Fourier matrix in the chosen eigenbasis. Every component has squared modulus $1/n$ and the rows are orthonormal; these vectors give nonzero rank-one effects summing to $I_d$ and balance every $A_Q$. No requirement of informational completeness is used for this construction.

## 3. Clipping, endpoints and the Naimark mapping

When $Q=0$, $A_Q=\sqrt\rho$. Write $\lambda_{\min,+}$ for the least positive eigenvalue and
$$
Q_{\mathrm{flat}}=1-r\lambda_{\min,+}.
$$
For $Q\ge Q_{\mathrm{flat}}$, $u=\sqrt{s/r}$ and $A_Q=uP$. Therefore the optimal score is $r(1-Q)/n$ in this range, including zero at $Q=1$. For $Q_{\mathrm{flat}}\le Q<1$, for any score-minimizing Alice measurement, Eve's optimized correct probability conditional on a conclusive outcome is $r/n$. For $r<n$ this is not unambiguous discrimination; at $Q=1$ conditioning on a conclusive event is undefined. When the positive spectrum is flat, $Q_{\mathrm{flat}}=0$.

In the portion where the largest $t$ positive eigenvalues are clipped to $u^2$, one has $t u^2=\sum_{j\le t}\lambda_j-Q$. Substitution in (2) gives Curran's expression with denominator $n$; at an exact threshold, either placement of a tied term gives the same value. One can also characterize the clipping as maximizing $\sum_j h_j$ with $0\le h_j\le\sqrt{\lambda_j}$ and $\sum_j h_j^2=s$: for $u>0$ maximize $h-h^2/(2u)$ on each interval and sum, then use the fixed squared norm. This merely explains the choice of filter; the primal and dual bounds above establish the measurement claim.

The exact rank-one Naimark isometry is $Vx=(\langle m_i,x\rangle)_i$ into $\mathbb C^n$. Taking $\widetilde\rho=V\rho V^\dagger$, the computational PVM on $\widetilde\rho$ has the same Eve ensemble as (5) up to the irrelevant choice of purifying coordinates. Moreover $A_Q(\widetilde\rho)=VA_Q(\rho)V^\dagger$ since the extra eigenvalues are zero and the clipping function vanishes at zero. Its computational diagonal is precisely $(\operatorname{Tr}M_i A_Q)_i$. Thus this is a support-complete, zero-padded extension of the same projective problem, not a distinct core formula. The proof of Curran v4 inverts positive eigenvalues and is not directly applicable to that singular dilation as written.

The fixed outcome number matters. For $Q<1$ every finite $n$ gives positive $v_n(Q)$; allowing arbitrary finite $n$ without an extremality constraint has infimum zero and no finite minimizer. We do not optimize over all effects of unrestricted rank at fixed $n$.

## 4. Rate-wise attainment and feasibility of simultaneous balancing

Here a rank-one MIC is a POVM with $d^2$ rank-one effects that span the $d^2$-dimensional real vector space of Hermitian matrices. These effects are linearly independent. Such a POVM is extreme: in a convex decomposition of a positive rank-one effect, every summand is supported on its one-dimensional range, and independence then forces the two decompositions to agree with the original POVM. Conversely a finite rank-one POVM with real linearly dependent effects is not extreme, by a vanishing nonzero real linear combination and sufficiently small two-sided coefficient perturbations preserving positivity and completeness.

For every $Q<1$ the [weighted MIC theorem](https://github.com/mxym/math/blob/8a7a0af8cf975ea707c6eaa7a645efe6ad1d85ee/research/weighted-mic-randomness-attainment/PROOF.md) applied to $R=A_Q$ gives a MIC that attains (3) at $n=d^2$. This earlier theorem allows arbitrary nonzero PSD $R$, including singular operators. Its use here is only rate-wise, not uniform in $Q$. Among finite extreme rank-one POVMs with unconstrained outcome count, $d^2$ is the unique optimal count for $Q<1$: independence limits the count to $d^2$, and the lower bound (2) strictly decreases with $n$. At $Q=1$ the objective cannot distinguish any measurement.

Let $E_\ell$ be the spectral projectors for the $k$ **distinct positive** eigenvalues of $\rho$, with positive square roots $0<\nu_1<\cdots<\nu_k$. A single rank-one $n$-outcome POVM is optimal at **all** $Q<1$ iff
$$
\operatorname{Tr}(M_i E_\ell)=\operatorname{rank}(E_\ell)/n
\quad\text{for every }i,\ell.
\tag{6}
$$
Indeed, setting $\delta_{i\ell}=\operatorname{Tr}(M_i E_\ell)-\operatorname{rank}(E_\ell)/n$, the pointwise equality criterion reads $\sum_\ell \min(\nu_\ell,u)\delta_{i\ell}=0$. As $Q$ varies over $[0,1)$, $u$ covers $(0,\nu_k]$. The slope on $(\nu_{k-1},\nu_k)$ is $\delta_{ik}$; then descend successively through intervals, ending at $(0,\nu_1)$. All coefficients vanish, also for $k=1$. The converse is immediate by summing the weighted projectors.

If $k>1$, (6) makes every $M_i$ orthogonal in trace to the nonzero traceless Hermitian matrix $E_1/\operatorname{rank}E_1-E_2/\operatorname{rank}E_2$, contradicting informational completeness. More generally (6) gives $k-1$ independent traceless constraints, so at most $d^2-k+1$ effects of a simultaneously optimal POVM can be linearly independent. If $k=1$, apply the weighted MIC theorem to $P$; this balances all rates since each $A_Q=uP$.

For two rates $Q_1,Q_2<1$, let $B_j=A_{Q_j}/\operatorname{Tr}(A_{Q_j})$. If $B_1\ne B_2$, no rank-one informationally complete POVM of any fixed outcome count is optimal at both: the difference $B_1-B_2$ would be trace-orthogonal to each effect. When $k>1$, distinct rates with at least one below $Q_{\mathrm{flat}}$ have different normalized spectra: their largest-to-smallest positive eigenvalue ratios are $u/\nu_1>1$ below the threshold, strictly monotone there, and $1$ on the plateau.

A quantitative version is available. Let $\beta>0$ be any tomography lower frame bound on traceless Hermitian matrices,
$$
\sum_i|\operatorname{Tr}(M_iH)|^2\ge \beta\|H\|_{\mathrm{HS}}^2
\quad\text{whenever }\operatorname{Tr}H=0.
$$
Such a $\beta$ exists for every finite informationally complete POVM by injectivity and compactness on the traceless unit sphere (the nontrivial tradeoff concerns $d\ge2$). For $Q_1,Q_2<1$, (4) gives
$$
\max_{j=1,2}\left(\frac{S_M(Q_j)}{v_n(Q_j)}-1\right)
\ge \frac{n\beta}{4}\|B_1-B_2\|_{\mathrm{HS}}^2.
\tag{7}
$$
To see this, put $z_{ji}=\operatorname{Tr}(M_i B_j)-1/n$. The left side is at least $n\max_j\|z_j\|_2^2$, and $\|z_1-z_2\|_2^2\le 4\max_j\|z_j\|_2^2$. Apply the frame bound to $B_1-B_2$.

## 5. Exact minimax infimum and nonattainment

For $n=d^2$ define the relative worst-rate objective
$$
\mathcal R(M)=\sup_{0\le Q<1}\frac{S_M(Q)}{v_n(Q)} .
$$
Then
$$
\inf_{M\,\mathrm{rank\!-\!one\ MIC}}\mathcal R(M)=1,
\quad \text{with attainment iff } \rho \text{ is proportional to }P .
\tag{8}
$$
To handle the limit $Q\to1$, note first that on $P$, $\rho\succeq\lambda_{\min,+}I_P$. For any two rank-one POVMs $M,M'$ with the same outcome count and any feasible conclusive Eve measurement,
$$
\left|\sum_i\operatorname{Tr}\big((\sigma_i-\sigma_i')N_i\big)\right|
\le \|\rho\|_{\mathrm{op}}\max_i\|M_i-M_i'\|_{\mathrm{op}}\operatorname{Tr}\sum_iN_i
\le \frac{s\|\rho\|_{\mathrm{op}}}{\lambda_{\min,+}}\max_i\|M_i-M_i'\|_{\mathrm{op}} .
$$
The feasible set depends on $\rho,Q$, not on $M$. This bounds the absolute difference of the optimal scores. Since $(\operatorname{Tr}A_Q)^2\ge\sum_j h_j^2=s$, after dividing by $v_n(Q)$ we get a uniform Lipschitz bound $n\|\rho\|_{\mathrm{op}}/\lambda_{\min,+}$ times the maximum effect distance for all $Q<1$. It also bounds the difference of their suprema. The supremum is finite, since $S_M(Q)\le s$.

Every rank-one $d^2$-outcome POVM $M_i=|f_i\rangle\langle f_i|$ is a limit of rank-one MICs. Choose $d^2$ vectors $g_i$ whose projectors span the Hermitian space, for example $e_j$, $e_j+e_\ell$, $e_j+\mathrm{i}e_\ell$ for $j<\ell$, with $e_j$ ranging over the standard basis. Put $w_i(t)=(1-t)f_i+t g_i$ for real $t$. The determinant of the real Hermitian coordinate columns of $|w_i(t)\rangle\langle w_i(t)|$ is polynomial in $t$ and nonzero at $1$. There are only finitely many roots. The sum $T(t)$ of these projectors tends to $I$ as $t\to0$; it is positive definite near zero. Away from the roots, congruence by $T(t)^{-1/2}$ normalizes the effects and preserves their rank-one character and independence. The resulting MIC converges effectwise to $M$ along $t\to0$. This argument does not require existence of SICs.

Apply this density to the $d^2$-outcome Fourier measurement, which attains $\mathcal R=1$ by (6). Uniform Lipschitz continuity gives the upper infimum bound $1$ on MICs, and (3) gives the reverse. If an MIC attained $1$, all ratios would equal $1$ individually, so (6) forces a flat positive spectrum. Conversely a MIC balancing $P$ attains it when the positive spectrum is flat. The nonattainment in (8) is compatible with (7): the positive tomography frame bound need not stay fixed along a sequence approaching the non-IC Fourier measurement.
