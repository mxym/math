# One doubled bit and an exact four-insertion example

For $A_n=0101\cdots$ and $D_n$ formed by doubling the middle letter in $A_{n-1}$, the two maximal alternating segments of $D_n$ have lengths differing by at most one. The [main proof, Eq. (3)](PROOF.md) with $b=2$ gives
\[
 H_k(D_n)-H_k(A_n)=k(k-3)/n+O_k(\log n/n^2).
\]
Thus *a single* doubled bit already beats alternation at every fixed insertion radius $k\ge4$ for all sufficiently long observations. The main theorem additionally optimizes over all words and determines their eventual segment count; two segments need not be optimal at larger $k$.

For four insertions at received length 18, compare $A=(01)^9$ with $D=010101010010101010$. The posterior ranges over **shorter length-14 inputs**. The positive multiplicity histograms, listed as multiplicity: number of such inputs, are
```text
A = 1:1365, 15:105, 120:1
D = 1:850, 2:230, 7:20, 8:84, 9:30, 15:12, 22:2, 28:10, 43:2, 78:1.
```
For either observation the sum of multiplicities is $\binom{18}{4}=3060$. With $h(j)$ the number of inputs of multiplicity $j$, the Shannon entropy is $\log_2 3060-\log_2(\prod_j j^{jh(j)})/3060$. Direct integer comparison in [check.py](check.py) gives a strictly smaller product for $D$, hence a strictly larger entropy. The histogram for $A$ is also given by [Ma and Zhang, Theorem 5.1](https://arxiv.org/html/2611.01064v1).
