# State-independent entanglement extraction: exact exponents, reliability and a Gaussian threshold

**Written analytic argument, not Lean-formalized or externally peer reviewed.** All logarithms are natural. Standard Schur--Weyl duality, the Weyl/hook dimension formulas and the highest-weight character bound are explicit representation-theoretic inputs [KW]. The central limit theorem is used only for the Gaussian conclusion. Exact finite checks accompany, but do not certify, the unbounded argument.

## 1. A single protocol for unknown states

Fix integers $2\le m\le n$ and let $D=mn$, $A=\log m$, $B=\log n$, $L=\log D$. For each copy number $k$ and target dimension $K$, a protocol consists of one global unitary on the existing $m^k\times n^k$ input, followed by deterministic local product channels with $K\times K$ output. No extra ancilla, measurement, or discarded system is supplied before that unitary. Local ancillas and discarding are allowed after it. The target fidelity is the overlap with the normalized rank-one maximally entangled projector $\Phi_K$, not the square root of that overlap.

The distinction from a state-aware optimization is the order of quantifiers:
\[
 \exists\{U_{k,K},\mathcal A_{k,K},\mathcal B_{k,K}\}_{k,K}
 \quad\forall\rho\text{ on }\mathbb C^m\otimes\mathbb C^n.
 \tag{1}
\]
The unitary and the local channels depend only on $m,n,k,K$, not on the eigenvalues, eigenvectors, entropy or rank of $\rho$. There is no preliminary tomography, common random choice of a state-dependent protocol, or outcome-conditioned global unitary. Write $F_k^{\rm univ}(\rho,K)$ for this fixed protocol's fidelity, and $F_k^\star(\rho,K)$ for the state-aware optimum with a global unitary and completely PPT postprocessing. Completely PPT means that both the channel and its partial-transpose conjugate are completely positive and trace preserving. This class contains LOCC and local product channels.

Let $p$ be the decreasing eigenvalue distribution of $\rho$, and $s=\operatorname{rank}\rho$. Zero eigenvalues are retained, with relative entropy evaluated on the positive support. Define
\[
 C(p)=\min\{A,(L-H(p))/2\},\qquad
 C_0(p)=\min\{A,(L-\log s)/2\}.
 \tag{2}
\]
For $R\ge0$ set $K_k=\lceil e^{kR}\rceil$ and
\[
 c_R=L-2\min(R,A),\qquad
 E_p(R)=(R-A)_++\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}\bigl(S_\alpha(p)-c_R\bigr).
 \tag{3}
\]
The term at $\alpha=1$ is zero.

**Theorem 1 (universal performance).** There is a family (1) such that, simultaneously for every fixed input state:

(a) At every fixed target rate $R\ge0$,
\[
 \lim_{k\to\infty}-\frac1k\log F_k^{\rm univ}(\rho,K_k)
 =\lim_{k\to\infty}-\frac1k\log F_k^\star(\rho,K_k)=E_p(R).
 \tag{4}
\]
In particular, the same optimal fidelity exponent is achieved without state knowledge and using local product postprocessing alone.

(b) For every $0\le R<C(p)$ the universal fidelity tends to one. For every $R>C(p)$ even the state-aware completely PPT optimum tends to zero exponentially. Thus ignorance of the entire state costs no first-order capacity.

(c) In the nontrivial direct regime
\[
 C_0(p)<R<C(p),\quad c=L-2R,
 \tag{5}
\]
the exact error exponent is also universal and optimal:
\[
 \lim_k-\frac1k\log(1-F_k^{\rm univ})
 =\lim_k-\frac1k\log(1-F_k^\star)
 =I_p(c):=\min_{H(q)\ge c}D(q\|p).
 \tag{6}
\]
Equivalently,
\[
 I_p(c)=\sup_{0<\alpha<1}\frac{1-\alpha}{\alpha}
                 \bigl(c-S_\alpha(p)\bigr).
 \tag{7}
\]
The inequalities in (5) imply $H(p)<c<\log s$; they specify the exact range claimed in (6).

(d) For every $0\le R<C_0(p)$ the universal protocol has fidelity exactly one for all sufficiently large $k$. No state-aware completely PPT protocol can achieve exact fidelity at any asymptotic rate above $C_0(p)$. Thus the zero-error capacity, defined by eventual exact extraction, is also (2).

**Theorem 2 (Gaussian threshold).** Suppose $0<C(p)<A$ and the varentropy
\[
 V(p)=\sum_{p_i>0}p_i(-\log p_i-H(p))^2
 \tag{8}
\]
is positive. For any target sequence with
\[
 \log K_k=kC(p)+z\sqrt{k}+o(\sqrt{k}),
 \tag{9}
\]
the very same family (1) satisfies
\[
 \lim_k F_k^{\rm univ}(\rho,K_k)
 =\lim_k F_k^\star(\rho,K_k)
 =\Phi(-2z/\sqrt{V(p)}),
 \tag{10}
\]
where $\Phi$ is the standard normal distribution function. In particular the fixed-error, state-aware optimal target size has expansion
\[
 \log K_k^{\rm opt}(\varepsilon)
 =kC(p)+\tfrac12\sqrt{kV(p)}\,\Phi^{-1}(\varepsilon)+o(\sqrt{k}),
 \quad 0<\varepsilon<1,
 \tag{11}
\]
and universal local postprocessing attains the same expansion. The protocol is indexed by the requested integer $K$, not by the unknown quantities in (9).

These theorems strengthen the state-aware extraction law in [Z]; they do not solve ordinary fixed-input LOCC distillation, where the initial global entangling unitary is absent. The convergence is pointwise for every fixed $\rho$ with one common protocol family, not an assertion of uniform convergence at all capacity boundaries. Formula (6) excludes the exact zero-error threshold; (10) excludes the local-dimension cap and zero varentropy. Those boundaries are not silently covered by continuity.

Universal compression [JHHH], universal pure-state concentration [HM], classical reliability and second-order source coding [H], state-agnostic work extraction [WT], and universal mixed-state LOCC distillation [TW] are prior results. The contribution argued here is a coherent simultaneous packing that attains the stated mixed-state extraction laws in the no-pre-unitary-ancilla model. No first-discovery claim is made for Schur estimation, the source-coding rate functions, the Rains constraints, or the entropy-deficit converse [L].

## 2. Representation-theoretic facts with explicit polynomial losses

Fix once and for all a Schur--Weyl identification
\[
 (\mathbb C^D)^{\otimes k}
 =\bigoplus_{\lambda\vdash k,\,\ell(\lambda)\le D}
       \mathcal Q_\lambda\otimes\mathcal P_\lambda,
 \qquad
 \rho^{\otimes k}=\bigoplus_\lambda Q_\lambda(\rho)\otimes I_{v_\lambda}.
 \tag{12}
\]
Here $u_\lambda=\dim\mathcal Q_\lambda$, $v_\lambda=\dim\mathcal P_\lambda$ and $r_\lambda=u_\lambda v_\lambda$. The central projector onto the summand is $\Pi_\lambda$. The identification and bases are fixed without $\rho$. The formula extends to singular $\rho$ by continuity. Put $J=\#\{\lambda\}$, $h=D(D-1)/2$, $Q=(k+D)^{h+D}$, and $q=\lambda/k$.

We use the standard dimension formulas
\[
 u_\lambda=\prod_{i<j}\frac{\lambda_i-\lambda_j+j-i}{j-i},\qquad
 v_\lambda=\frac{k!\prod_{i<j}(\lambda_i-\lambda_j+j-i)}
                       {\prod_i(\lambda_i+D-i)!}.
 \tag{13}
\]
They give
\[
 J\le(k+1)^D,\quad u_\lambda\le(k+D)^h,\quad
 Q^{-1}e^{kH(q)}\le v_\lambda\le e^{kH(q)},\quad
 Q^{-1}e^{kH(q)}\le r_\lambda\le Qe^{kH(q)}.
 \tag{14}
\]
Indeed $v_\lambda$ is at most the multinomial coefficient because, for each $i<j$, $\lambda_i-\lambda_j+j-i\le\lambda_i+j-i$. It is at least that coefficient divided by $(k+D)^h$, since all numerator factors are at least one. The multinomial bounds $(k+1)^{-D}e^{kH(q)}\le k!/\prod\lambda_i!\le e^{kH(q)}$ follow by the modal-type argument recalled in Section 6. This proves (14), with deliberately loose but explicit polynomial factors.

The block probability is
\[
 t_\lambda(p):=\operatorname{Tr}(\Pi_\lambda\rho^{\otimes k})
             =v_\lambda s_\lambda(p),
 \tag{15}
\]
where $s_\lambda$ is the Schur character. The highest-weight monomial $p^\lambda$ occurs once. Every other weight is dominated by $\lambda$; since $p$ is decreasing, its monomial is at most $p^\lambda$. The sum of multiplicities is $u_\lambda$. Hence
\[
 p^\lambda\le s_\lambda(p)\le u_\lambda p^\lambda,\qquad
 Q^{-1}e^{-kD(q\|p)}\le t_\lambda(p)\le Qe^{-kD(q\|p)}.
 \tag{16}
\]
For rank $s<D$, blocks with more than $s$ rows have zero probability, since their Schur character in $s$ variables is zero. For at most $s$ rows the same inequalities hold on the positive support. These are the finite representation estimates underlying the Keyl--Werner spectral large-deviation law, not a new spectral-estimation theorem.

A normalized universal operator needed later is
\[
 \tau_k=\frac1J\sum_\lambda\frac{\Pi_\lambda}{r_\lambda}.
 \tag{17}
\]
It commutes with every $\rho^{\otimes k}$ and obeys
\[
 \rho^{\otimes k}\le Q\tau_k.
 \tag{18}
\]
To see this, $v_\lambda\operatorname{Tr}Q_\lambda(\rho)=t_\lambda\le1$, so $Q_\lambda(\rho)\le I/v_\lambda$, so the full block operator is at most $I/v_\lambda$. Comparing with the block value $1/(Ju_\lambda v_\lambda)$ of $\tau_k$ costs at most $J\max u_\lambda\le Q$. This proof uses a positive trace bound on the actual block, not a guessed eigenbasis.

## 3. A simultaneous, state-independent packing

Write $a=m^k$, $b=n^k$, $N=ab$. For all sufficiently large $k$, depending only on $m,n$, we have
\[
 a,b\ge2J,\qquad a_0b_0\ge2\max_\lambda u_\lambda,
 \quad a_0=\lfloor a/J\rfloor,\quad b_0=\lfloor b/J\rfloor.
 \tag{19}
\]
The reason is exponential growth versus the fixed-dimensional polynomial bounds (14). Put $N_0=a_0b_0$, so $N_0\ge N/(4J^2)$. Small $k$ not satisfying (19) can use a fixed product-output channel without affecting any asymptotic assertion. $K=1$ always uses the trivial exact channel.

Allocate to each Young diagram one disjoint coordinate sector of dimension $a_0$ on Alice and one of dimension $b_0$ on Bob. In the input Schur block select
\[
 \mathcal S_\lambda=\mathcal Q_\lambda\otimes
      \operatorname{span}\{e_1,\ldots,e_{v'_\lambda}\},\qquad
 v'_\lambda=\min\{v_\lambda,\lfloor N_0/u_\lambda\rfloor\},
 \quad r'_\lambda=u_\lambda v'_\lambda.
 \tag{20}
\]
Crucially the truncation is in the permutation-multiplicity factor. Equation (12) implies that it retains exactly the fraction
\[
 \theta_\lambda=v'_\lambda/v_\lambda\ge1/(8J^2)
 \tag{21}
\]
of the block's mass for every state, even though the state on $\mathcal Q_\lambda$ is unknown and need not be diagonal in our basis. For the bound, either no truncation occurs or $\lfloor N_0/u_\lambda\rfloor\ge N_0/(2u_\lambda)$, whence $\theta_\lambda\ge N_0/(2r_\lambda)\ge1/(8J^2)$.

Choose $d_\lambda$ to be the largest integer $1\le d\le\min(K,a_0)$ such that
\[
 \lfloor a_0/d\rfloor\lfloor b_0/d\rfloor\ge r'_\lambda.
 \tag{22}
\]
Such a $d$ exists. If $w=\min\{K,a_0,\sqrt{N_0/r'_\lambda}\}$, then $\max(1,\lfloor w/2\rfloor)$ is feasible: when it exceeds one, the inequalities $\lfloor x\rfloor\ge x/2$ for $x\ge1$ prove (22); when it equals one, $r'_\lambda\le N_0$ suffices. It is at least $w/4$. Therefore
\[
 \frac{d_\lambda}{K}\ge\frac1{8J}
       \min\{1,a/K,\sqrt{N/r_\lambda}/K\}.
 \tag{23}
\]

Inside its assigned $a_0\times b_0$ sector, use the orthonormal coded vectors
\[
 |\psi_{ij}^{(\lambda)}\rangle=
 \frac1{\sqrt{d_\lambda}}\sum_{t=0}^{d_\lambda-1}
 |\lambda,id_\lambda+t\rangle_A
 |\lambda,jd_\lambda+t\rangle_B,
 \tag{24}
\]
for distinct pairs $(i,j)$. There are enough of them by (22). Map a fixed orthonormal basis of $\mathcal S_\lambda$ to $r'_\lambda$ such vectors. All selected target subspaces lie in disjoint sectors, and their total dimension is at most $JN_0\le N$. Thus this partial isometry extends to one fixed unitary $U_{k,K}$ on the whole original input. This is a deterministic choice of bases, sectors, and extension; no part uses $p$ or an input measurement.

Alice's local Kraus operators on sector $\lambda$ are
\[
 A_{\lambda,i}=\sum_{t=0}^{d_\lambda-1}|t\rangle_{\mathbb C^K}
          \langle\lambda,id_\lambda+t|,
 \tag{25}
\]
plus $|0\rangle\langle x|$ for every unused coordinate in that sector and for all coordinates outside the allocated sectors. Bob uses the corresponding operators. Their adjoint products sum to the full local identity. Each selected code vector maps to $\Phi_{d_\lambda}$ embedded into the $K\times K$ output; the overlap with $\Phi_K$ is $d_\lambda/K$.

This assertion holds for arbitrary states supported on the code subspace, not just mixtures of its listed vectors. The local maps send $|\psi_{ij}\rangle\langle\psi_{i'j'}|$ to zero unless $(i,j)=(i',j')$, and to $\Phi_d$ if the pairs agree. Before the unitary, (12) has no cross terms between selected and discarded multiplicity factors or different Young blocks. Thus the discarded part remains a positive contribution and
\[
 F_k^{\rm univ}(\rho,K)\ge
 \sum_\lambda\theta_\lambda\frac{d_\lambda}{K}t_\lambda(p)
 \ge\frac1{64J^3}\max_\lambda
   \min\{1,a/K,\sqrt{N/r_\lambda}/K\}t_\lambda(p).
 \tag{26}
\]
This is a single universal protocol, not a different choice of unitary for whichever diagram dominates the last maximum.

A block is extracted exactly whenever
\[
 K\le a_0,\qquad r_\lambda\le G:=\lfloor a_0/K\rfloor\lfloor b_0/K\rfloor.
 \tag{27}
\]
Then there is no truncation and the maximal choice in (22) is $d_\lambda=K$. Consequently
\[
 1-F_k^{\rm univ}(\rho,K)\le\sum_{r_\lambda>G}t_\lambda(p)
 \quad\text{when }K\le a_0.
 \tag{28}
\]
No common-randomness mixture is inserted to obtain (26): such a mixture could have destroyed the exponentially small error in (28).

## 4. State-aware converses and the exact fidelity exponent

For any completely PPT channel with $K\times K$ output, its fidelity effect $M=\Lambda^*(\Phi_K)$ satisfies the Rains constraints
\[
 0\le M\le I,\qquad -I/K\le M^\Gamma\le I/K.
 \tag{29}
\]
For necessity, partial-transpose conjugation is a channel whose adjoint is positive and unital, and $\Phi_K^\Gamma$ is the swap divided by $K$. These constraints therefore hold in particular for LOCC. Partial transpose is a Hilbert--Schmidt isometry, so
\[
 \operatorname{Tr}M^2\le N/K^2,
 \qquad\|M\|_\infty\le\beta:=\min(1,a/K).
 \tag{30}
\]
The second bound follows by pairing $M^\Gamma$ with partially transposed rank-one projectors: a vector of Schmidt rank at most $a$ has projector partial-transpose trace norm at most $a$.

For $1<\alpha\le2$, Schatten Holder and the scalar interpolation inequality for the eigenvalues of $M$ give
\[
 F_k^\star(\rho,K)\le
 \beta^{(2-\alpha)/\alpha}
 (N/K^2)^{(\alpha-1)/\alpha}
 \left(\operatorname{Tr}(\rho^{\otimes k})^\alpha\right)^{1/\alpha}.
 \tag{31}
\]
At $\alpha=1$ the bound is $\beta$. These bounds are uniform over the input unitary. With $K=\lceil e^{kR}\rceil$, their optimal exponential form is the lower bound $E_p(R)$ on $\liminf-k^{-1}\log F_k^\star$.

Conversely, approximate a decreasing probability vector $q$ on the positive support of $p$ by Young diagrams $\lambda^{(k)}/k$. Equations (14), (16) and (26) yield
\[
 \limsup_k-\frac1k\log F_k^{\rm univ}
 \le\min_q\left\{D(q\|p)+\max(0,R-A,R-L/2+H(q)/2)\right\}.
 \tag{32}
\]
Sorting $q$ cannot increase its relative entropy to decreasing $p$, by the rearrangement inequality, and leaves its entropy unchanged. Thus restricting to decreasing $q$ loses nothing. The maxima in (32) equal $(R-A)_++(H(q)-c_R)_+/2$.

For clarity, the exact matching identity is
\[
 \min_q\{D(q\|p)+(H(q)-c)_+/2\}
 =\max_{1\le\alpha\le2}\frac{\alpha-1}{\alpha}(S_\alpha(p)-c),\quad c\ge0.
 \tag{33}
\]
It requires no unproved minimax exchange. Put $Z_\alpha=\sum p_i^\alpha$ and $q_{\alpha,i}=p_i^\alpha/Z_\alpha$. For the maximand $J_c$,
\[
 J_c'(\alpha)=\frac{H(q_\alpha)-c}{\alpha^2},\qquad
 H'(q_\alpha)=-\alpha\operatorname{Var}_{q_\alpha}(\log p_i)\le0.
 \tag{34}
\]
If $H(p)\le c$, both sides of (33) vanish with $q=p$. If $H(q_2)\ge c$, $q=q_2$ gives value $(S_2(p)-c)/2=J_c(2)$. Otherwise the escort with entropy $c$ is in $(1,2)$ and gives $D(q_\alpha\|p)=J_c(\alpha)$. Boundary cases agree. For every $q$ the value on the left is at least each $J_c(\alpha)$, since
\[
 D(q\|p)=\alpha^{-1}D(q\|q_\alpha)
          +(\alpha-1)\alpha^{-1}(S_\alpha(p)-H(q))
\]
and $(H-c)_+/2\ge(\alpha-1)(H-c)/\alpha$ for $1\le\alpha\le2$. This completes (33) and proves (4). All polynomial losses in (26) have logarithm $O_{m,n}(\log k)$.

## 5. Universal reliable and zero-error extraction

For $0<R<C(p)$, put $c=L-2R>H(p)$. Eventually $K_k\le a_0$, and
\[
 G\ge N/(16J^2K_k^2)\ge e^{kc}/(64J^2).
 \tag{35}
\]
If a block fails (27), its entropy satisfies $H(q)>c-\log(64J^2Q)/k$. Equations (16) and (28), with compactness on the positive support, show that the probability of these blocks tends to zero. This proves universal faithful extraction below $C$. The exponent in (3) is strictly positive above $C$, since either $R>A$ or $J_{L-2R}'(1)>0$. This proves the converse and part (b).

If $R<C_0(p)$, then $c>\log s$. Every block of nonzero probability has at most $s$ rows and $r_\lambda\le Qs^k$. For all sufficiently large $k$, (35) exceeds this upper bound. Thus every nonzero block is good and the fidelity is exactly one. Conversely exact fidelity requires $M$ to be the identity on the rotated rank-$s^k$ support, so (30) gives $s^k\le N/K^2$ and $1\le a/K$. This proves part (d), with no assumed knowledge of $s$ in the construction.

### 5.1 Exact reliability in the strict direct regime

Assume (5), hence $H(p)<c<\log s$. Equations (16), (28), (35) yield
\[
 \liminf_k-\frac1k\log(1-F_k^{\rm univ})\ge I_p(c).
 \tag{36}
\]
The continuity needed here follows explicitly from the escort formula below.

To prove optimality even for state-aware completely PPT operations, let $L_j(p^{\otimes k})$ be the sum of the $j$ largest eigenvalues, capped at one beyond the support size. For any $0<t<1$, (30) implies that at most $N/(K^2t^2)$ eigenvalues of $M$ exceed $t$. The spectral trace inequality therefore gives
\[
 1-F_k^\star(\rho,K)\ge
 (1-t)\left[1-L_{\lfloor N/(K^2t^2)\rfloor}(p^{\otimes k})\right].
 \tag{37}
\]
Choose $t=1/2$. For ranks $M_k$ with $k^{-1}\log M_k\to c\in(H(p),\log s)$, the classical optimal-prefix tail has exponent
\[
 \lim_k-\frac1k\log(1-L_{M_k}(p^{\otimes k}))=I_p(c).
 \tag{38}
\]
Here is a type proof. Include all types with entropy at most $c-\delta$; their total cardinality is at most $(k+1)^s e^{k(c-\delta)}\le M_k$ eventually. The excluded types have total probability at most $(k+1)^s\exp[-k I_p(c-\delta)]$. Conversely, for any type approximation to a $q$ with $H(q)>c$, its cardinality is exponentially larger than $M_k$, and at least a fraction $1-M_k/r_q$ of its equiprobable words must be excluded. Its mass is at least $(k+1)^{-s}e^{-kD(q\|p)}$. Letting $q$ approach the entropy-$c$ minimizer and $\delta$ decrease to zero proves (38). Thus (37) and (36) give (6).

For (7), when $H(p)<c<\log s$ there is a unique $\alpha\in(0,1)$ with $H(q_\alpha)=c$; positive eigenvalues cannot all be equal in this regime. The identity
\[
 D(q\|p)=\alpha^{-1}D(q\|q_\alpha)
       +\frac{1-\alpha}{\alpha}(H(q)-S_\alpha(p))
 \tag{39}
\]
shows both the lower bound for every $H(q)\ge c$ and equality at $q_\alpha$. It also gives continuity as $c$ varies strictly between $H(p)$ and $\log s$.

The zero-error threshold itself is intentionally excluded from (6). For example, a known rank-four state on $4\times4$ can be globally encoded into $\Phi_{2^k}$ times a $4^k$-dimensional garbage system at $R=\log2=C_0$, giving exact fidelity at every $k$. A finite formula obtained by blindly extending $I_p(c)$ to $c=\log s$ would fail for a nonuniform spectrum on that support. Rank, target rounding and subspace divisibility matter at this boundary.

## 6. The Gaussian window without estimating the state

Assume the hypotheses of Theorem 2. Since $C<A$, $K_k\le a_0$ eventually. Let $r=N/K_k^2$. If
\[
 \log(Jr_\lambda)\le\log r-\log(16J),
 \tag{40}
\]
then $r_\lambda\le r/(16J^2)\le G$ by the first inequality in (35), so the block is exactly extracted. The random variable on the left is the spectral self-information $-\log\tau_k$, measured under $\rho^{\otimes k}$.

As $\tau_k$ commutes with $\rho^{\otimes k}$, choose a common eigenbasis. Equation (18) gives pointwise on the positive support
\[
 -\log\tau_k\le-\log\rho^{\otimes k}+\log Q.
 \tag{41}
\]
Under $\rho^{\otimes k}$, the random variable $-\log\rho^{\otimes k}$ is the sum $S_k$ of $k$ independent copies of $-\log p_X$, with $X\sim p$. Hence (40)--(41) and exact extraction of good blocks show
\[
 F_k^{\rm univ}(\rho,K_k)\ge
 \Pr\{S_k\le\log r-\log(16J)-\log Q\}.
 \tag{42}
\]
This step does not assert a separate, unproved central limit theorem for Young diagrams.

For the converse, diagonalize the rotated state and write the diagonal entries of $M$ in that basis as $x_i$. Then $0\le x_i\le1$ and $\sum x_i^2\le\operatorname{Tr}M^2\le r$. For any $\gamma>0$, split the input eigenvalues at $e^{-(\log r+\gamma)}$. The contribution of the smaller eigenvalues is at most $e^{-\gamma/2}$ by Cauchy--Schwarz: their squared sum is at most $e^{-(\log r+\gamma)}$. Therefore
\[
 F_k^\star(\rho,K_k)\le
 \Pr\{S_k\le\log r+\gamma\}+e^{-\gamma/2}.
 \tag{43}
\]
Take $\gamma=k^{1/4}$. By (9), $\log r=kH(p)-2z\sqrt{k}+o(\sqrt{k})$, while $\log(16JQ)=O(\log k)$. The ordinary central limit theorem applied to $S_k$ proves that both bounds tend to the right side of (10). The resulting threshold gives (11) by bracketing target sizes above and below a fixed Gaussian quantile. The upper bracket follows from (43) for every larger integer $K$, and the lower bracket from (42); no monotonicity of the particular universal construction is assumed.

## 7. Scope, prior work, and unresolved boundaries

The construction removes both spectral and eigenbasis information from the state-aware theorem [Z]. It preserves its full fidelity exponent, identifies the previously untreated strict direct reliability regime, and proves a second-order threshold without state estimation or an extra ancilla before the global unitary. It is not a claim that all finite-block state-aware fidelities are matched, or that efficient circuits have been designed.

Schur--Weyl universality is an established method, notably in universal compression [JHHH], pure-state concentration [HM], and state-agnostic work extraction [WT]. Classical source reliability and Gaussian thresholds are also established [H]. The new argument uses those structures to meet the simultaneous no-state-information quantifiers under the constrained two-stage extraction model. Lami's quadratic converse [L] already includes the half-entropy-deficit bound; that bound is not claimed here as a new principle. Rains's constraints [R] are restated and used with credit. Recent universal mixed-state distillation [TW] already removes state knowledge for the usual LOCC capacity; it leaves finer error and second-order behavior as separate directions. It does not include free global entangling preprocessing. The present task changes that operation class and therefore is not a solution of those remaining standard-LOCC questions. Universal distillation [LLF] also concerns different free-operation classes and no free entangling global preprocessing; its results are not relabeled as the theorem here.

A fixed-family universal theorem is stronger than choosing a different optimal protocol for each state, but weaker than uniform finite-block convergence over states arbitrarily close to a transition. The reliability value at the exact zero-error threshold, the Gaussian law at the local-dimension cap or at zero varentropy, efficient implementation, and ordinary fixed-input distillation are not resolved by the statements above. The unrestricted finite-copy APPT purity and APPT-versus-AS questions remain separate.

## References

[KW] M. Keyl and R. F. Werner, *Estimating the spectrum of a density operator*, Physical Review A 64, 052311 (2001), arXiv:quant-ph/0102027v1. Schur decomposition and character/highest-weight estimates, especially equations (2)--(4), (17) and (21). The standard Weyl and hook formulas are used explicitly in (13); their representation-theoretic validity is an external mathematical input.

[JHHH] R. Jozsa, M. Horodecki, P. Horodecki and R. Horodecki, *Universal Quantum Information Compression*, Physical Review Letters 81, 1714 (1998), arXiv:quant-ph/9805017. Prior basis-independent universal compression.

[HM] M. Hayashi and K. Matsumoto, *Variable length universal entanglement concentration by local operations and its application to teleportation and dense coding*, arXiv:quant-ph/0109028; see also *Universal distortion-free entanglement concentration*, Physical Review A 75, 062338 (2007). These concern unknown pure-state concentration without free entangling global preprocessing.

[H] M. Hayashi, *Second order asymptotics in fixed-length source coding and intrinsic randomness*, IEEE Transactions on Information Theory 54, 4619--4637 (2008), arXiv:cs/0503089v2. Prior classical information-spectrum and second-order results; the needed type bounds and Gaussian reduction are given above.

[WT] K. Watanabe and R. Takagi, *Universal work extraction in quantum thermodynamics*, Nature Communications 17, 1857 (2026), DOI:10.1038/s41467-026-69143-3. Prior state-agnostic resource extraction in a different operational model.

[TW] R. Takagi, K. Watanabe, T. Matsuura, H. Arai and M. Hayashi, *Universal distillation of quantum entanglement*, arXiv:2609.40215v1, submitted 30 September 2026. Prior universal first-order mixed-state LOCC distillation; the distinction between its operation class and the globally preprocessed model is substantive.

[R] E. M. Rains, *A semidefinite program for distillable entanglement*, IEEE Transactions on Information Theory 47, 2921--2933 (2001), arXiv:quant-ph/0008047v2.

[L] L. Lami, *On PPT entanglement distillation*, arXiv:2610.12454v1. The maximally mixed auxiliary state in the quadratic converse yields the entropy-deficit upper bound; no new attribution for it is made here.

[LLF] Z. Lin, K. Li and K. Fang, *Finite-Blocklength and Exponential Analyses for Universal Entanglement and Coherence Distillation under Various Free Operations*, arXiv:2601.10190v3, revised 22 September 2026. The latest primary abstract was retrieved directly because the web cache still returned v2. Used for comparison, not as a proof premise.

[Z] Y. Zhang, *Global-unitary entanglement extraction: capacity and exact strong-converse exponents*, repository analytic preprint, immutable `global-unitary-extraction-preprint-v1`, source `8a5eaa8be917132e1d64e079a9ef5d1934a700c7`. State-aware predecessor. Its exact checker and written proof do not provide a Lean certificate for the present work.
