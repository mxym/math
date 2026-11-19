# A negative answer for sums of rows, even for the first two

This addresses the second half of Baslingker–Krishnapur–Madiman, arXiv:2412.15116v2 §7, open question (ii). The setting is ordinary Plancherel at fixed size n, not Poissonized size. Put S=lambda_1+lambda_2 and w_j=n! Pr(S=j)=sum (f^lambda)^2 over the indicated shapes. For every n at least 9, the distribution of S fails log-concavity at j=3.

In fact w_2=1 from the sole shape (1^n), and w_3=(n−1)^2 from the sole shape (2,1^(n−2)). For S=4 the shapes are (3,1^(n−3)) and (2^j,1^(n−2j)) for 2≤j≤floor(n/2). These are exhaustive by the only two ordered positive splits of four, 3+1 and 2+2 (a one-row diagram has S=n). The hook shape has f=binom(n−1,2). The latter shapes are transposes of (n−j,j); their hook dimensions are d_j=binom(n,j)−binom(n,j−1). The sum of d_j² over 0≤j≤floor(n/2) equals Cat(n)=binom(2n,n)/(n+1): extend through j=n+1 with out-of-range binomial coefficients zero, observe d_(n+1−j)=−d_j, and apply Vandermonde to get total 2[binom(2n,n)−binom(2n,n+1)]. Thus exactly
~~~
w_4 = Cat(n) − 1 − (n−1)^2 + binom(n−1,2)^2.
~~~
At n=9, w_2=1, w_3=64 and w_4=5581, so 64²<5581. Here the four dimensions for S=4 are 28, 27, 48, 42, also directly obtained by the hook formula.

For completeness it fails for all n≥9 without further enumeration. Let F_n=1+(n−1)^2+(n−1)^4. We have Cat(9)=4862>F_9=4161. Each nonconstant summand in F_n increases by a factor at most (n/(n−1))^4≤(9/8)^4<2, while Cat(n+1)/Cat(n)=(4n+2)/(n+2)>3 for n≥9. Hence Cat(n)>F_n throughout, and w_4>(n−1)^4=w_3². This disproves the prefix-sum assertion already at a fixed prefix of length two. It is fully consistent with log-concavity of each individual row in the companion positive result.
