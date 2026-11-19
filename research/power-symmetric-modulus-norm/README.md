# Power symmetric moduli: the exact exponent for universal normhood

Bourin and Teng Zhang asked whether a matrix norm can be obtained by symmetrizing the powers of the right and left moduli of a matrix, taking the positive root, and applying **any** unitarily invariant norm. For fixed finite real \(p\ge1\), write
\[
 S_p(X)=\left((|X|^p+|X^*|^p)/2\right)^{1/p}.
\]

**The universal assertion holds exactly at \(p=2\).** The positive case was already proved in the source. For every other exponent in [Conjecture 8.7](https://arxiv.org/html/2610.30538v1#S8), real 4-by-4 matrices and the ordinary operator norm suffice: the functional is strictly larger at a midpoint than at either endpoint. At \(p=1\), the endpoint values are both 12 but the midpoint value is 25/2, using integer matrix entries only.

**Shortest route.** For symmetric 2-by-2 blocks, put \(X(A,B)=\begin{pmatrix}0&A\\B&0\end{pmatrix}\). Then \(2\|S_p(X(A,B))\|_\infty^p=\lambda_{\max}(|A|^p+|B|^p)\). The two elementary cases of the [explicit proof](DIRECT.md) use just this identity, without taking a limit. The [full statement, integer example and alternative derivation](PROOF.md) include the previously known quadratic case and explain the connection with matrix convexity.

This is not a classification for each individual norm or each smaller dimension, nor a determination of the optimal constants in the separate Problem 8.6. For instance, using the Schatten p-norm outside at exponent p always returns the ordinary Schatten p-norm. The expression with the operator norm already appeared in a 2007 numerical-radius bound.

[Source and priority notes](SOURCES.md) · [Independent mathematical check](REVIEW.md) · [Independent check of both explicit parameter choices](DIRECT-REVIEW.md).

The proof is analytic. To reproduce the illustrative exact checks, run `python3 -B -O verify.py` and `python3 -B -O independent.py`. Both are standard-library only. [Author checks](CHECKS.txt) · [independent checks](INDEPENDENT-CHECKS.txt).

AI-assisted draft, independently checked internally, not externally peer reviewed; no priority guarantee.
