# Fixed-support cyclic noise: a read-\(k\) bound

## 1. Model and statement

Let \(n,s\ge1\), let \(G=\mathbb Z/n\mathbb Z\), and let \(t_j\in\mathbb F_2[X]/(X^n-1)\) have fixed support \(T_j\subseteq G\), of size \(w_j\), for \(1\le j\le s\). Write \(R_{j,a}\) for the coefficient of \(X^a\) of \(R_j\). All \(R_{j,a}\) are mutually independent, and each has success probability \(\eta_j\in[0,1]\). For a fixed \(I\subseteq G\), set
\[
 Y_i=\bigoplus_{j=1}^s\ \bigoplus_{b\in T_j}R_{j,i-b},
 \qquad W_I=\sum_{i\in I}Y_i,\qquad m=|I|.
\]
Indices are in \(G\), the parity is in \(\mathbb F_2\), and the final sum is over the integers. Define
\[
 p=\tfrac12\left(1-\prod_{j:w_j>0}(1-2\eta_j)^{w_j}\right),\qquad
 k_I=\max_{j,a}|I\cap(a+T_j)|.
\]
The empty product is one. If \(m=0\) or \(k_I=0\), then \(W_I=0\). If \(p=0\) or \(p=1\), then \(W_I=mp\) almost surely. Otherwise, for each real \(\lambda\),
\[
 \mathbb E e^{\lambda W_I}\le (1-p+p e^{k_I\lambda})^{m/k_I}.                     \tag{1}
\]
In particular, with relative entropy in nats,
\[
 D(q\Vert p)=q\ln(q/p)+(1-q)\ln((1-q)/(1-p)),
\]
using the usual zero-term convention at \(q=0,1\), the two one-sided statements are
\[
 \Pr(W_I\ge mq)\le e^{-(m/k_I)D(q\Vert p)}\quad(p\le q\le1),\qquad
 \Pr(W_I\le mq)\le e^{-(m/k_I)D(q\Vert p)}\quad(0\le q\le p).                    \tag{2}
\]
These conclusions hold for every fixed choice of supports and every fixed \(I\). In particular \(I=G\) gives \(m=n\) and \(k_I=\max_jw_j\). No primality or invertibility is required. A bound exponential in \(m/k_I\) does not by itself give decay if this ratio stays bounded.

## 2. Marginals and overlap

For each \(i\), the input bits in the displayed parity are distinct: for fixed \(j\), subtraction from \(i\) is injective, and blocks carry distinct indices. Therefore independence gives
\[
 \mathbb E(-1)^{Y_i}=\prod_{j:w_j>0}(1-2\eta_j)^{w_j}=1-2p .
\]
In particular \(\mathbb E W_I=mp\). In the parametrization of the source, a common rate \(\eta=(1-2^{-\omega})/2\) gives \(p=(1-2^{-\omega\sum_jw_j})/2\).

The input bit at \((j,a)\) appears in the output at \(i\) exactly when \(i-a\in T_j\), hence in exactly \(|I\cap(a+T_j)|\) of the indicated parity formulas. Thus the outputs in \(I\) form a read-\(k_I\) family of functions of independent inputs, in the sense of Gavinsky, Lovett, Saks and Srinivasan. This statement is about how many outputs read each *input*, not how many other output functions a given output can overlap. It also gives the deterministic cases in §1 from empty formulas or from the equal degenerate marginals.

## 3. Moment and tails

For completeness, let \(g_i\ge0\) be functions of a finite independent family, where each base variable occurs in at most \(k\ge1\) functions. Then
\[
 \mathbb E\prod_i g_i\le\prod_i(\mathbb E g_i^k)^{1/k}.                         \tag{3}
\]
Indeed, hold all but one base variable fixed; if \(h\le k\) factors read this variable, apply ordinary Hölder with \(k\) equal exponents, padding by \(k-h\) copies of the constant one. Replace each participating factor by the \(k\)-th root of its conditional \(k\)-th moment over just the variable integrated out. The remaining read counts cannot increase. Induction on the number of variables proves (3), since the \(k\)-th moment of each replacement over the remaining product measure is the original full moment by iterated expectation.

Apply (3) to \(g_i=e^{\lambda Y_i}\) with \(k=k_I\), proving (1). For the upper tail use Markov with \(\lambda\ge0\), and for the lower tail with \(\lambda\le0\). Substituting \(\theta=k_I\lambda\) gives exponent
\[
 (m/k_I)\bigl[\ln(1-p+pe^\theta)-\theta q\bigr].
\]
For \(0<q<1\), the minimizing \(\theta\) is \(\ln[q(1-p)/(p(1-q))]\), of the required sign; substituting gives \(-mD(q\Vert p)/k_I\). Take the limit at either endpoint. At \(q=p\), the bound is one. As a weaker two-sided consequence, Bernoulli Pinsker gives \(\Pr(|W_I/m-p|\ge\epsilon)\le 2e^{-2m\epsilon^2/k_I}\) for positive \(\epsilon\), dropping a side when its threshold lies outside \([0,1]\).

## 4. Exact cyclic sharpness

Let \(n=kr\), take a single block and let \(T\) be the subgroup of \(G\) of order \(k\). Every output in a coset of \(T\) is the parity of the same \(k\) input bits: \(i-T=i+T\). Different cosets involve disjoint inputs, so their parities are independent Bernoulli\((p)\). For \(I=G\) this gives \(W_I=k\,\mathrm{Bin}(r,p)\), exactly attaining (1); the upper endpoint \(q=1\) and lower endpoint \(q=0\) attain (2). For any fixed \(0<p<1/2\) and any \(k\), choosing \(\eta=(1-(1-2p)^{1/k})/2\) realizes that \(p\). The same moment equality holds if \(I\) selects exactly \(\ell\) points from each of any \(r'\ge1\) cosets and no others, since then \(k_I=\ell\), \(m=\ell r'\), and \(W_I=\ell\,\mathrm{Bin}(r',p)\). In particular a coordinate restriction can strictly reduce the relevant parameter.

If \(r>1\) and \(k>1\) this family shows why using the fully independent bound without a read loss is not valid in general: for \(0<p<1\) the probability of all-one outputs is \(p^r>p^{kr}\). This is a statement about exact abstract distributions, not about cryptographic schemes.

The lower endpoint also proves a local-in-bias sharpness statement without any subgroup, including prime \(n\). Fix a nonempty one-block support of size \(w\), and take \(I=G\). As \(\eta\downarrow0\), one has \(p=w\eta+O(\eta^2)\). The input is identically zero with probability \((1-\eta)^n\), which is a lower bound on \(\Pr(W_I=0)\); (2) supplies the upper bound \((1-p)^{n/w}\). Both bounds expand to \(1-n\eta+O(\eta^2)\) for fixed \(n,w\). Replacing \(w\) in the denominator of (2) by any positive \(k'<w\) that is independent of \(\eta\) would instead give \(1-nw\eta/k'+O(\eta^2)\), smaller than the all-zero-input probability for all sufficiently small positive \(\eta\). This is first-order sharpness at \(q=0\), not a sharp tail statement for all biases and thresholds.
