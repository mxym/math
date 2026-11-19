# Nonunit coefficients versus signs in sums of iid lattice variables: a parity dichotomy

Yongxian Zhang

For a discrete real variable let $Q(X)=\max_x\mathbb P(X=x)$. Let $X_1,\ldots,X_n$ be independent copies of a fixed integer-valued law $X$. Juškevičius and Kurauskas, [*On the Littlewood–Offord problem for arbitrary distributions*](https://doi.org/10.1002/rsa.20977), [authors' manuscript, §5, Conjecture 1](https://web.vu.lt/mif/v.kurauskas/files/2020/08/general_200704.pdf), asked whether every nonzero real coefficient vector is bounded by some choice of unit signs, for iid lattice random vectors of any dimension. Their Corollary 1(b) proves the even case with balanced signs. Their Conjecture 2, and the later Juškevičius conjecture about separately capped marginal laws, have different comparison distributions and are not being refuted here.

**Theorem.** For each fixed odd $n\ge3$ and every $C<\infty$ there exists a finitely supported integer law $X$ (all probabilities rational) and positive integer coefficients $a_1,\ldots,a_n$ such that
$$
 Q\!\left(\sum_{i=1}^na_iX_i\right)>C\ \max_{w_i\in\{-1,1\}} Q\!\left(\sum_{i=1}^nw_iX_i\right).
$$
The coefficients can be held fixed as $C$ varies: take $(n+1)/2$ coefficients equal to 1 and $(n-1)/2$ equal to $2n+1$. Thus even in one dimension there is no law-independent finite comparison factor for any such odd $n$. The worst factor is 1 for even $n$ by the cited result, and for $n=1$ by invariance of atom sizes under nonzero scaling. This does not contradict known unit-sign optimality for a single iid **Bernoulli** law.

## 1. Two incompatible Bernoulli sign counts

Fix $n=2m+1\ge3$. For $0\le k\le m$ write $T_k(p)$ for the largest atom of a sum of $n-k$ positive and $k$ negative independent Bernoulli($p$) terms. This covers every sign choice up to global reversal. We need rational $p_A,p_B\in(0,1/2)$ such that
$$
 \arg\max_k T_k(p_A)=\{m\},\qquad \arg\max_k T_k(p_B)=\{0\}.
$$
This dependence of the optimal Bernoulli sign count on the bias is an established phenomenon; we give a short proof for the two regimes used below.

Take $p_A=1/(2n+1)$. As $(1-p_A)^n\ge1-np_A>1/2$, zero is the unique mode for each $k$. Its mass at any such $p$ equals
$$
 \sum_{j=0}^{k}\binom{k}{j}\binom{n-k}{j}p^{2j}(1-p)^{n-2j}.
$$
For $k<m$ each binomial product is nondecreasing upon replacing $k$ by $k+1$ (for a nonzero old product, compare $(k+1)(n-k-j)$ with $(k+1-j)(n-k)$); the $j=1$ product strictly increases, with a new term if $k=0$. This proves the first assertion.

For the second, put $p=1/2-e$ with $e>0$. After adding a constant $k$, the signed sum is a sum of $n-k$ Bernoulli($1/2-e$) and $k$ Bernoulli($1/2+e$) variables. At $e=0$ its only modes are $m,m+1$. There are finitely many $k$ and outcomes, so for all sufficiently small $e$ the largest atom for every $k$ is at one of these two sites. Put $b_s=2^{-2m}\binom{2m}{s}$ (zero off support). At site $s$, differentiating the mass with respect to a single Bernoulli success parameter at the fair point gives $b_{s-1}-b_s$ by conditioning. Thus the two possible central heights have the same value $T$ at zero and opposite derivatives $(n-2k)(b_m-b_{m-1})$ and $-(n-2k)(b_m-b_{m-1})$ in $e$. As $b_m>b_{m-1}$ and $k\le m$, it follows that
$$
 T_k(1/2-e)=T+(n-2k)(b_m-b_{m-1})e+O_n(e^2).
$$
The largest slope occurs uniquely at $k=0$. Any sufficiently small positive rational $e$ therefore gives a suitable $p_B$.

## 2. A single integer law that uses each local sign pattern

Write $A_k=T_k(p_A)$ and $B_k=T_k(p_B)$. For every $k$, either $A_k<A_m$ or $B_k<B_0$, so (all numbers being positive)
$$
 H=\max_{0\le k\le m}A_kB_k<A_mB_0.
$$
Fix $b=2n+1$ and an integer $L\ge2$. Take independent Bernoulli digits $D_j$, success parameter $p_A$ for $0\le j<L$ and $p_B$ for $L\le j<2L$. Let $s_j=(-1)^j$ in the first block and $s_j=(-1)^{L-1}$ in the second. Define the integer
$$
 X=\sum_{j=0}^{2L-1}b^j s_jD_j.
$$

In any of the sums considered below, the digits contributing to different output columns are independent: across copies and positions the underlying Bernoulli variables are independent, and each of them enters just one column. The set of integers occurring in any given column has diameter at most $n$; in fact every contributing signed Bernoulli digit has range of length one and there are at most $n$ of them. Since $b>n$, the map from a feasible list of column sums $u_j$ to $\sum b^ju_j$ is injective. For two lists first differing in the least significant differing column, equality of totals would force their nonzero difference there to vanish modulo $b$. Consequently the largest atom of the integer sum is the product of its columnwise largest atoms.

With unit signs, the local signs in every column are either the given signs or their common reversal. Thus each choice with $k$ negatives (up to reversal) has peak $(A_kB_k)^L$ and the best possible sign peak is $H^L$.

Now use $n-m$ coefficients 1 and $m$ coefficients $b$. In every interior column $1\le j\le L-1$, the $n-m$ current digits have sign $s_j$ and the $m$ shifted digits have sign $s_{j-1}=-s_j$, all with bias $p_A$. The peak there is $A_m$. In columns $L+1\le j\le2L-1$ the two local signs coincide at bias $p_B$; the peak is $B_0$. The remaining columns $0,L,2L$ contain respectively $n-m,n,m$ digits. Each has peak at least its all-zero-input probability, so their product is at least $c=\min(1-p_A,1-p_B)^{2n}>0$. Hence the nonunit peak divided by the best sign peak is at least
$$
 \frac{c}{A_mB_0}\left(\frac{A_mB_0}{H}\right)^L.
$$
This tends to infinity. All constructions are finite and use rational probabilities. The law, not the fixed integer coefficients, varies with $L$.

## 3. A numerical-free strict example with three summands

Take $b=10$ and nine independent Bernoulli digits: at positions 0 and 1 use $p_A=1/4$, at positions 2 through 8 use $p_B=2/5$. Give position 0 a positive sign and positions 1 through 8 a negative sign in $X$. The support has 512 atoms. The two sign classes and the positive triple $(1,1,10)$ have the same denominator $D=(4^2 5^7)^3=1\,953\,125\,000\,000\,000\,000$. Their exact peak numerators are

| Coefficients | Product of column maxima | Numerator |
|---|---:|---:|
| $(1,1,1)$ | $27^2\,54^7$ | 976076478078336 |
| $(1,1,-1)$ | $33^2\,51^7$ | 977280228179739 |
| $(1,1,10)$ | $9\cdot33\cdot45\cdot54^6\cdot3$ | 994151968413120 |

For example, the all-positive three-digit convolution has coefficients $(27,27,9,1)$ for the low bias, and $(27,54,36,8)$ for the high bias. With one minus sign the lists in increasing exponent, up to reflection, are $(9,33,19,3)$ and $(18,51,44,12)$. In the shifted triple the transition column (index 2) has numerator polynomial $(3+2z)^2(3+z)$ up to reflection; its largest coefficient is 45. The boundary maxima are 9 and 3. This gives a strict violation without limits, root finding, or a search over laws. The general theorem is not extrapolated from this example.
