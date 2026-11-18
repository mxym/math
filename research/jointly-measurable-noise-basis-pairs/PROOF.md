# Compatible noise for a pair of basis measurements

For two orthonormal bases of $\mathbb C^d$, let $P=(P_i)$ and $Q=(Q_j)$ denote their rank-one projective measurements. Two POVMs are **compatible** if they are the row and column marginals of a positive array of total sum $I$. We use the jointly measurable incompatibility robustness of [Designolle, Farkas and Kaniewski (DFK), Eqs. (44)–(45)](https://arxiv.org/pdf/1906.00448): $\eta^{\rm jm}(P,Q)$ is the largest $t\in[0,1]$ for which there is a compatible noise pair $(N,M)$ such that $(tP+(1-t)N,tQ+(1-t)M)$ is also compatible. The noise and the mixture may have different parents. Lower maximal visibility means greater incompatibility.

**Theorem.** In every dimension $d\ge3$ the minimum of $\eta^{\rm jm}(P,Q)$ over pairs of orthonormal bases is $\eta=(1+1/\sqrt d)/2$. Every mutually unbiased pair attains the minimum. For $d=2$ the minimum is instead $2(\sqrt2-1)$, also attained by mutually unbiased bases (DFK (69), (77)). The qubit case and the exact value on mutually unbiased bases are prior results. It remains to show that no other basis pair does worse in $d\ge3$.

## 1. Compute the noise required by the known mixture parent

Write $r=\sqrt d$, $D=4(d+r)$ and $\Phi_P(X)=\sum_iP_iXP_i$; define $\Phi_Q$ similarly. Use the rank-one PVM instance of DFK (60)–(62):
$$
DG_{ij}=P_i+Q_j+2r(P_iQ_j+Q_jP_i)+d(P_iQ_jP_i+Q_jP_iQ_j). \tag{1}
$$
For $P=P_i$, $Q=Q_j$, the right side is the sum of two positive squares, $(P+rPQ)^*(P+rPQ)$ and $(Q+rQP)^*(Q+rQP)$. Summing first over $j$ gives
$$
D G_{i\bullet}=I+(2d+4r)P_i+d\Phi_Q(P_i). \tag{2}
$$
Interchange $P,Q$ for the column sum. Summing (2) over $i$ gives $DI$, so $G$ is normalized.

Since $D\eta=2(d+2r+1)$ and $D(1-\eta)=2(d-1)$, the required residual first marginal is
$$
 N_i=\frac{G_{i\bullet}-\eta P_i}{1-\eta}
    =\frac12\left[\frac{I-P_i}{d-1}+\frac{d\Phi_Q(P_i)-P_i}{d-1}\right]. \tag{3}
$$
Similarly
$$
 M_j=\frac12\left[\frac{I-Q_j}{d-1}+\frac{d\Phi_P(Q_j)-Q_j}{d-1}\right].
$$
These effects being positive is not enough: $N$ and $M$ must have a *single joint parent*.

## 2. Construct the second parent

For an outcome $i$ define
$$
 K_i^P(X)=\frac{1}{(d-1)(d-2)}
   \sum_{\substack{k<l\\k,l\ne i}} (P_k-P_l)X(P_k-P_l). \tag{4}
$$
Each map is completely positive. Two counts give its marginals:
$$
 K_i^P(I)=\frac{I-P_i}{d-1},\qquad
 \sum_i K_i^P(X)=\frac{d\Phi_P(X)-X}{d-1}. \tag{5}
$$
For the first identity, $(P_k-P_l)^2=P_k+P_l$ for $k\ne l$, and each $k\ne i$ occurs $d-2$ times. For the second, each fixed unordered pair occurs for $d-2$ possible $i$. Expanding the sum over all unordered pairs gives $(d-1)\Phi_P(X)$ minus $\sum_{k\ne l} P_kXP_l=X-\Phi_P(X)$. This proves (5).

Define a second positive array by crossing the two choices of basis:
$$
 H_{ij}=\tfrac12\big[ K_i^P(Q_j)+K_j^Q(P_i)\big]. \tag{6}
$$
In its row sum, the first term contributes $(I-P_i)/(d-1)$ before division by two. The second contributes $(d\Phi_Q(P_i)-P_i)/(d-1)$. These are precisely the two terms in (3). By interchange the column sum is $M_j$, and the total is $I$. Therefore $H$ is a parent of the actual residual noise, while $G$ is a parent of the mixture. Together they certify $\eta^{\rm jm}(P,Q)\ge\eta$ for every basis pair.

The separate one-sided compatibility expressed by (4)–(5) can also be deduced from older results; see [sources](SOURCES.md). The point here is that their crossed average fits the residuals of (1) *exactly*.

## 3. Attainment

For mutually unbiased bases $|\langle p_i,q_j\rangle|=1/\sqrt d$ and $\lambda_{\max}(P_i+Q_j)=1+1/\sqrt d$. The last equality follows by diagonalizing on the span of the two basis vectors. If a mixture is compatible at visibility $t$, let $G'$ be its parent. Positivity of the noise effects gives
$$
  2td\;\le\;\sum_i\operatorname{Tr}(P_iG'_{i\bullet})
                 +\sum_j\operatorname{Tr}(Q_jG'_{\bullet j})
       =\sum_{ij}\operatorname{Tr}((P_i+Q_j)G'_{ij})
       \le (1+1/\sqrt d)d .
$$
Hence $t\le\eta$. This is the known MUB upper bound; it even allows noise that is not compatible. Standard and Fourier bases supply a mutually unbiased pair in every dimension. With the universal lower bound from §2, this proves the theorem for $d\ge3$. No step involving $d-2$ is used for the separately known qubit result. ∎
