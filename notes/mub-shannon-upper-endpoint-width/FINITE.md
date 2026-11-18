# Independent finite-dimensional verification without any sphere concentration theorem

Here is a second proof of the explicit example $d=2^{40}$, $L=d+1$. The goal is to find one set of bases for which *every* input gives an average entropy within $1/8$ nat of the common center. Instead of appealing to concentration on the sphere, we work with independent exponential random variables. First we control one basis, then the proportion of bad bases for each fixed input, then all inputs at once. The [checker](finite_check.py) verifies rational inequalities; it does not construct matrices. Natural logarithms are used throughout.

Let X_i be independent Exp(1), S=(ΣX_i)/d, Y=(Σ X_i ln X_i)/d, b=E[X_1 ln X_1], c=ln d−b. For a fixed pure state and a uniform random basis, its H has law ln d+ln S−Y/S. By convexity of x ln x, b≥0; also x ln x≤x²−x, so b≤1. Use |x ln x|≤1+x², giving E[(X ln X)²]≤1+2·2!+4!=29. Since 0≤H≤ln d<28 and 0≤b≤1<ln d, |H−c|<28<29.

To compare c with the common Haar mean μ, on S≥1/2 the mean value theorem and 1/S≤2 give |H−c|≤4|S−1|+2|Y−b|. On S<1/2 use 29, with probability ≤4/d by Chebyshev. Thus |μ−c|≤(4+2√29)/√d+116/d<1/1000. This does not use harmonic asymptotics.

**Fixed state**. Cut off X and X ln X to zero for X>T=40000. The probability of any cutoff in one basis is ≤d exp(−40000), and the absolute shift of either expectation is ≤E[(1+X²)1_{X>T}]=(T²+2T+3)exp(−T)<1/1000. For the truncated sample averages S',Y', apply the bound
  Pr(|Ū−EŪ|>a)≤2 exp(−d(λa−λ²V))
for independent identically distributed U when V≥Var U and |λ(U−EU)|≤1. Indeed e^x≤1+x+x² for |x|≤1; center, multiply mgfs and apply Markov twice. The following choices work:
- S': V=2, λ=1/100000, a=9/1000. The truncated variable lies in [0,40000].
- Y': V=29, λ=1/500000, a=1/40. Here ln(40000)<11, so |U|≤440000 and |EU|≤√29. The lower endpoint of x ln x is −1/e.

Each exponent d(λa−λ²V) exceeds 50000. The total failure probability is bounded by d exp(−40000)+4 exp(−50000)<exp(−39000). On success |S−1|≤1/100, |Y−b|<3/100. Therefore
 |H−c|≤ |S−1|/(1−1/100)+(|Y−b|+b|S−1|)/(1−1/100) ≤5/99<1/19.

**Every state for one tuple**. For L independent bases and a fixed state x, independently each basis is bad (|H−c|>1/19) with probability at most exp(−39000). If F is their arithmetic mean and at most L/500 are bad, then |F−c|≤1/19+29/500. The probability otherwise is at most 2^L exp(−78L), by a union bound on the subsets having at least ceil(L/500) bad bases. A Euclidean δ-net of the sphere for δ=1/(200√d) has size ≤(1+400√d)^{2d}<2^{58d}. The derivative bound |(−r²ln r²)'|≤2 gives entropy Lipschitz constant 2√d, so the extended error is at most 1/100. Taking the union over the net gives total failure probability ≤2^{58d}2^L exp(−78L)<1. For a surviving tuple, *all pure states* obey
  |F−μ|< 1/19+29/500+1/100+1/1000 <1/8.
This implies M≤μ+1/8 and W≤1/4. The MUB comparison uses an eigenvector of any one of the d+1 bases, giving F=(d/(d+1))ln d and particularly M≥that value. With m≤μ and the rational lower bound in [the main proof, §3](PROOF.md#3-a-specified-finite-prime-power-dimension) M−μ>1/4 this proves both strict comparisons. ∎
