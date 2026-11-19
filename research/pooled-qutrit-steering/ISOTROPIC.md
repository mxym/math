# The pooled qutrit isotropic steering witness also has a strict gap

**Research note by Yongxian Zhang.** AI-assisted; independently checked internally, not externally peer reviewed. There is an absolute $\delta>0$ such that the direct-sum qutrit isotropic-state witness of Yang and Qiao, for any number and arrangement of complex rank-one projective bases, requires visibility at least $5/12+\delta$. This is a qualitative uniform gap, without a numerical value of $\delta$ or an exact optimum. It concerns the conjecture after Eq. (25) in [Yang–Qiao](https://doi.org/10.1038/s41534-026-01204-3), for the specific pooled witness. It does not change the physical projective-measurement steering threshold or address general steering tests.

## Compactification and the equality conditions

For $N$ complex qutrit bases, [Yang–Qiao](https://arxiv.org/html/2507.20950v2) Eqs. (16), (20), (22), (23), (25), (32)–(33) give the raw pooled threshold $w^*=(3H-1)/2$, with $H=\Omega_N/N$ maximizing the sum of the globally largest $N$ of $3N$ probabilities, divided by $N$. Their maximization over outcome subsets is constrained only by their total size, not by one-per-basis. Eq. (23) also follows by comparing the isotropic top entry $(1+2w)/3$ in each setting with $\Omega_N/N$. Replacing raw partial-sum suprema by their least concave majorant can only increase the value at $L=N$; the isotropic Lorenz curve is affine on both sides of $L=N$, so its two endpoints and this one breakpoint suffice when the comparison curve is concave.

Let $\mathcal B=U(3)$ denote ordered orthonormal bases, allowing arbitrary column phases, and take any Borel probability measure $\mu$ on $\mathcal B$; embedding the finite cases as empirical measures suffices. At unit state $\psi$, order the probabilities of a basis $B$ as $p_1\le p_2\le p_3$. Put
$$
 \alpha_\mu(\psi)=\int p_3\,d\mu,\qquad
 T_\mu(\psi)=\min_{0\le t\le1}\left[t+\int\sum_{i=1}^3(p_i-t)_+\,d\mu\right],
 \qquad H(\mu)=\max_\psi T_\mu(\psi).
$$
This cutoff formula is exactly the maximal cost of a fractional selection of total mass 1 from the pooled three units of mass: take every item strictly above the upper one-third quantile and the required fraction of the tied items. For any feasible selection the cutoff objective is an upper bound, with equality for this rule. In the equally weighted empirical case it reproduces the finite largest-$N$ expression. As a particular feasible rule one can take one maximizer from each basis; hence $T_\mu\ge\alpha_\mu$.

The bracketed continuous function of $\mu,\psi,t$ is jointly continuous for weak convergence of probability measures: on compact $\mathcal B$ the integrands converge uniformly as $\psi,t$ vary convergently. Minimizing and maximizing over the indicated fixed compact sets preserves continuity. Probability measures on the compact metric space $\mathcal B$ are weakly compact, so $H$ attains a global minimum.

For a Haar test state in any fixed basis the squared moduli are uniform on the simplex (Dirichlet(1,1,1)). Inclusion–exclusion using $\Pr(p_{i_1}>t,\ldots,p_{i_j}>t)=(1-jt)_+^2$ for specified original labels shows
$$
 \mathbb E_\psi\alpha_\mu(\psi)=\int_0^1[3(1-t)^2-3(1-2t)_+^2+(1-3t)_+^2]\,dt
 =1-\tfrac12+\tfrac19=\tfrac{11}{18}=:m .
$$
Thus $H(\mu)\ge m$. If $H(\mu)=m$, continuity and full support of Haar measure give
$\alpha_\mu(\psi)=T_\mu(\psi)=m$ **at every state**, since $\alpha_\mu\le T_\mu\le m$.

For each fixed state choose a minimizing cutoff $t$. The excess of the cutoff objective over $\alpha_\mu$ is the integral of the nonnegative continuous function
$$
 (t-p_3)_+ +(p_2-t)_++(p_1-t)_+ .
$$
As the integral vanishes, the function vanishes at **every support basis**, without requiring that individual bases be atoms. Therefore at each state there is a common $t$ with $p_2\le t\le p_3$ simultaneously for every support basis. In particular, when $\psi$ is unbiased to any support basis $A$, that basis forces $t=1/3$: no other support basis may have two probabilities strictly greater than $1/3$ at such a state.

## Pair rigidity in dimension three

**Lemma (three-phase proof derived in independent internal review).** If every state unbiased to a basis $A$ has at most one probability strictly above $1/3$ in a second qutrit basis $B$, the two bases have a common ray.

Write $U=B^*A$. A common ray is an entry of modulus one, equivalently a row of $U$ with just one nonzero entry. Sample a flat input $(1,u,v)^T/\sqrt3$ with independent uniform phases $u,v$. We claim each row supported on at least two columns has probability **strictly greater than $1/3$** to produce an output probability strictly greater than $1/3$.

For a single row, phases in its entries can be removed: absorb them into the independent phases and an irrelevant overall phase. Write its entries as $a,b,c\ge0$, with $a^2+b^2+c^2=1$, and set
$$
 D=ab\,u+bc\,\bar u v+ca\,\bar v.
$$
The sign of the output probability minus $1/3$ is the sign of $|a+bu+cv|^2-1=2\Re D$. Put $\omega=e^{2\pi i/3}$. Under the three measure-preserving phase rotations $(u,v)\mapsto(\omega^k u,\omega^{2k} v)$, the deviations are $2\Re(\omega^k D)$, $k=0,1,2$. They sum to zero and at least one is positive whenever $D\ne0$. The zero set has product measure zero: for fixed $v$, $uD=ab\,u^2+ca\,\bar v u+bc\,v$ is a nonzero polynomial because at least one pairwise product is nonzero.

On an open set *two* deviations are positive. Indeed the possible triples of real signs $(u,\bar u v,\bar v)$ for $u,v\in\{\pm1\}$ are precisely the sign triples of product $+1$. Give the smallest of $ab,bc,ca$ the positive sign and the other two negative signs. Then $D<0$ is real: those two nonnegative products sum to more than the smallest since they are not all zero. The $k=1,2$ deviations are then $-D>0$ and remain positive in a neighborhood. Averaging the positive count over the three measure-preserving rotations proves the claim for that row.

If all three rows were non-singletons, linearity of expectation on the *same* random input would give an expected number of outputs strictly above $1/3$ greater than 1, contradicting the hypothesis. Thus there is a common ray. An independent Laurent-polynomial proof is supplied [in the appendix](ISOTROPIC-PAIR-APPENDIX.md).

## Uniform obstruction

Every pair of support bases now shares a ray. If they are all identical as unordered ray sets this is already a family with a common ray. Otherwise take two distinct ray sets $A,B$. They share exactly one ray $q$ (two common rays would force the third). If another support basis $C$ failed to contain $q$, its rays shared with $A$ and $B$ would be distinct orthogonal rays in $q^\perp$. They would span that plane, forcing $C$'s third ray to be $q$, a contradiction. Thus all support bases contain $q$. At state $q$ every support basis has largest probability 1, giving $\alpha_\mu(q)=1$, which contradicts the required constant $11/18$. The minimum of $H$ over all setting measures is therefore strictly greater than $11/18$. Since $(3(11/18)-1)/2=5/12$, this proves the uniform visibility gap. The argument supplies no numerical value for the new positive margin.

The physical projective-steering threshold $5/12$ is prior [Wiseman–Jones–Doherty](https://doi.org/10.1103/PhysRevLett.98.140402), not contradicted here. The [source comparison](ISOTROPIC-SOURCES.md) distinguishes the earlier flat-torus intersection results from the strict two-coordinate test needed here. Nonprojective POVMs, general alignments and other majorization/steering questions are not treated.
